import system.io
import set_theory.zfc

open io

section fmt
open format
universe u
meta def my_to_format {α : Type u} [has_to_format α] : list α → format
| [] := to_fmt ""
| xs := group (nest 1 $ format.join $ list.intersperse ("," ++ line) $ xs.map to_fmt)
end fmt

meta def decls := list (_root_.name × pexpr)

meta structure tla_module :=
  (name : string)
  (exts : list string)
  (vars : decls)
  (invs : expr)
  (init : expr)
  (next : expr)

-- TODO: do we need a tla_config struct?

-- def comma_sep {α : Type*} (xs : list α) : format := _

open expr tactic function

-- x : t, y : t'
-- ∀ (x : t) (y : t'), true
-- intros
-- x : t,
-- y : t',
-- ⊢ true
--

meta def primed_name : name → name
| (name.mk_string s n) := name.mk_string (s ++ "'") n
| n := n

meta def scope_check (vs : list expr) (p : pexpr) (primed := ff) : tactic (expr × expr) :=
do -- let vs'' := if primed then vs.map (prod.map primed_name id)
   --                       else [],
   -- vs' ← (vs'' ++ vs).mmap $ uncurry $ λ n t,
   --     (to_expr t >>= mk_local_def n),
   let tgt := expr.pis vs `(Prop),
   solve_aux tgt (do
     intron vs.length, -- Prop
     p ← to_expr p,
     p <$ exact p )

meta def lean_to_tla : expr -> tactic format
| `(%%x = %%y) :=
do xx <- lean_to_tla x,
   yy <- lean_to_tla y,
   return format!"({xx} = {yy})"
| `(%%x ∧ %%y) :=
do xx <- lean_to_tla x,
   yy <- lean_to_tla y,
   return format!"({xx} /\\ {yy})"
| `(%%x ∨ %%y) :=
do xx <- lean_to_tla x,
   yy <- lean_to_tla y,
   return format!"({xx} \\/ {yy})"
| `(%%x ≤ %%y) :=
do xx <- lean_to_tla x,
   yy <- lean_to_tla y,
   return format!"({xx} <= {yy})"
| `(%%x + %%y) :=
do xx <- lean_to_tla x,
   yy <- lean_to_tla y,
   return format!"({xx} + {yy})"
| (local_const _ n _ _) := return $ to_fmt n
| e := do e' ← pp e,
          if is_numeral e
             then return e'
             else fail format!"unsupported: {e'}"

meta def mk_module (module : tla_module) : tactic (list string) :=
do inv  ← lean_to_tla module.invs,
   init ← lean_to_tla module.init,
   next ← lean_to_tla module.next,
   return $ to_string <$>
   [ format!"------- MODULE {module.name} ---------"
   , format!"EXTENDS {my_to_format module.exts}"
   , format!"VARIABLES {my_to_format $ prod.fst <$> module.vars}"
   , format!"Invs == {inv}"
   , format!"Init == {init}"
   , format!"Next == {next}"
   , format!"====================" ]

meta def mk_config (module : tla_module) : list string :=
[ "INIT Init"
, "NEXT Next"
, "INVARIANT Invs" ]

def write_list_to_file (l : list string) (filename: string) : io unit :=
do h ← mk_file_handle filename mode.write,
   mmap (fs.put_str_ln h) l,
   fs.close h

namespace tactic.interactive

open interactive interactive.types lean.parser

meta def comma_sep {α} (tac : lean.parser α) := sep_by (skip_info (tk ",")) tac

precedence `invariant`:0
precedence `init`:0

@[user_command]
meta def parse_tla_module  (meta_info : decl_meta_info) (_ : parse $ tk "tla_module") :
  lean.parser unit :=
do nm ← ident, trace nm,
   tk "extends",
   ext ← comma_sep ident, trace ext,
   tk "variables",
   vars ← comma_sep ident, trace vars,
   vars ← vars.mmap $ λ n,
       (mk_local_def n `(int)),
   tk "invariant",
   inv ← texpr, -- trace vars,
   tk "init",
   int ← texpr, -- trace vars,
   -- let vars' := vars.map (λ x, prod.mk x ``(ℤ)),
   (inv,linv) ← scope_check vars inv,
   (int,lint) ← scope_check vars int,
   trace inv, trace int,
   trace linv, trace lint,
   add_decl $ mk_definition `invariably [] (expr.pis vars `(Prop)) linv,
   add_decl $ mk_definition `initial [] (expr.pis vars `(Prop)) lint,

   tk "end"

end tactic.interactive

tla_module ioexp
extends Integers, FiniteSets
variables x, y
invariant x ≤ y
init x = 0 ∧
     y = 0
-- next    ( x' = x+1 ∧
--           y' = y )
--       ∨ ( x' = y ∧
--           y' = x )
end
-- -/


-- meta def ioexp : tla_module :=
-- { name := "ioexp"
-- -- , vars := ["x"]
-- -- , invs := ["x <= 3"]
-- , exts := ["Integers", "FiniteSets"]
-- , vars := [ (`x, ``(ℤ))
--           , (`y, ``(ℤ)) ]
-- , invs := ```(x <= 3)
-- , init := ```(x = 0 ∧ y = 0)
-- , next := ```(  (x' = x + 1 ∧ y' = y)
--               ∨ (x' = y     ∧ y' = x) ) }

open interaction_monad.result

meta def error_trace {α} (tac : tactic α) : tactic α
| s := match tac s with
       | (exception (some err) p s') := (trace (err ()) >> exception (some err) p) s'
       | e                           := e
       end

meta def main : io bool :=
do let tla_file := ioexp.name ++ ".tla",
   let cfg_file := ioexp.name ++ ".cfg",
   out ← io.run_tactic $ error_trace (mk_module ioexp), -- <|> (tactic.trace "program failed" >> failed),
   write_list_to_file out tla_file, -- TODO: can we combine this line
   write_list_to_file (mk_config ioexp) cfg_file, -- with this line? (using mmap)
   io.cmd { cmd := "java", args := ["tlc2.TLC",tla_file] } >>= put_str_ln,
   -- e ← proc.wait p,
   put_str_ln "foo",
   return tt
   -- print e,
   -- return $ e = 0

#eval main
