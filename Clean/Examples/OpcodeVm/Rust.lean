module

public import Clean.Backends.Plonky3.Print
public import Clean.Examples.OpcodeVm.Ensemble
public import Clean.Utils.Primes

@[expose] public section

def main : IO Unit := do
  match Backends.Plonky3.Print.ensembleToRust
      (OpcodeVm.formalEnsemble OpcodeVm.exampleProgram OpcodeVm.exampleProgram_length
        (2 : F pBabybear)).ensemble 1000 with
  | .ok rust => IO.print rust
  | .error error => throw (IO.userError error)
