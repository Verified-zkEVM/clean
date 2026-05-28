import Mathlib.Util.GetAllModules

def main (args : List String) : IO UInt32 := do
  let git := args.contains "--git"
  let rootArgs := args.filter (· != "--git")
  if rootArgs.length > 1 then
    IO.eprintln "usage: ListModules.lean [--git] [root]"
    return 2
  let root := rootArgs.headD "Clean"
  let modules ← getAllModulesSorted git root
  for module in modules do
    IO.println module
  return 0
