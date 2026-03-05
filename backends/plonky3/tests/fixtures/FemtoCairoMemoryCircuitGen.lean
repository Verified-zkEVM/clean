-- Circuit JSON generation for the FemtoCairo plonky3 backend (memory test)
import Clean.Examples.FemtoCairo.Plonky3MemoryTestData
import Clean.Examples.FemtoCairo.Plonky3Helpers

open Examples.FemtoCairo.Plonky3MemoryTestData
open Examples.FemtoCairo.Plonky3Helpers

def main (args : List String) : IO Unit := do
  match args with
  | [output_path] =>
    let constraints := femtoCairoTable.tableConstraintsWitness initialState finalState
    generateCircuitJson constraints programSize programData.toArray
      (numSteps + 1) #[("memory", 2, (memData "memory" 2).size)] output_path
  | _ => IO.println "Usage: lake env lean --run FemtoCairoMemoryCircuitGen.lean <output_path>"
