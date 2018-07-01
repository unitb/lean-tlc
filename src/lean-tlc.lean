import system.io
open io

section fmt
open format
universe u
meta def my_to_format {α : Type u} [has_to_format α] : list α → format
| [] := to_fmt ""
| xs := group (nest 1 $ format.join $ list.intersperse ("," ++ line) $ xs.map to_fmt)
end fmt

meta structure tla_module :=
  (name : string)
  (exts : list string)
  (vars : list name)
  (invs : pexpr)
  (init : pexpr)
  (next : pexpr)

-- TODO: do we need a tla_config struct?

meta def mk_module (module : tla_module) : list string :=
do to_string <$>
   [ format!"------- MODULE {module.name} ---------"
   , format!"EXTENDS {my_to_format module.exts}"
   , format!"VARIABLES {module.vars}"
   , format!"Invs == {module.invs}"
   , format!"Init == {module.init}"
   , format!"Next == {module.next}"
   , format!"====================" ]

def mk_config (module : tla_module) : list string :=
[ "INIT Init"
, "NEXT Next"
, "INVARIANT Invs" ]

def write_list_to_file (l : list string) (filename: string) : io unit :=
do h ← mk_file_handle filename mode.write,
   mmap (fs.put_str_ln h) l,
   fs.close h

def ioexp : tla_module :=
{ name := "ioexp"
-- , vars := ["x"]
-- , invs := ["x <= 3"]
, exts := ["Integers", "FiniteSets"]
, vars := "x"
, invs := "x <= 3"
, init := "x = 0"
, next := "x' = x + 1" }

meta def main :=
do let tla_file := ioexp.name ++ ".tla",
   let cfg_file := ioexp.name ++ ".cfg",
   write_list_to_file (mk_module ioexp) tla_file, -- TODO: can we combine this line
   write_list_to_file (mk_config ioexp) cfg_file, -- with this line? (using mmap)
   p ← proc.spawn { cmd := "tlc", args := [tla_file] },
   e ← proc.wait p,
   return $ e = 0
