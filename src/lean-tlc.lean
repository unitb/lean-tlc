import system.io
open io

structure tla_module :=
  (name : string)
  (exts : string) -- TODO: make a `list string'
  (vars : string) -- TODO: make a name→string map
  (invs : string) -- TODO: make a name→string map
  (init : string) -- TODO: support custom name ?
  (next : string) -- TODO: support custom name ?

-- TODO: do we need a tla_config struct?

meta def mk_module (module : tla_module) : list string :=
do to_string <$>
   [ format!"------- MODULE {module.name} ---------"
   , format!"EXTENDS {module.exts}"
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
-- , exts := ["Integers"]
-- , vars := ["x"]
-- , invs := ["x <= 3"]
, exts := "Integers"
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
