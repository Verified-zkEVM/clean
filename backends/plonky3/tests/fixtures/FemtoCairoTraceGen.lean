-- Trace generation for the FemtoCairo plonky3 backend
-- Generates the execution trace using witnessesWithData + inductiveWitness
import Lean
import Clean.Examples.FemtoCairo.Plonky3TestData
import Clean.Table.WitnessGeneration
import Clean.Table.Json

open Examples.FemtoCairo.Plonky3TestData
open Examples.FemtoCairo.Types

-- InductiveTable wrapping the FemtoCairo step circuit (Input = unit).
-- Only `.step` is used (via `inductiveWitness`);
-- proof fields are stubbed since this is a test script.
def femtoCairoTable : InductiveTable (F pBabybear) State unit where
  step state _ := femtoCairoStepMain state
  Spec := fun _ _ _ _ _ _ => True
  soundness := by simp only [InductiveTable.Soundness]; intros; trivial
  completeness := by simp only [InductiveTable.Completeness]; intros; sorry
  subcircuitsConsistent := by intros; sorry

-- N = 16 rows (15 steps)
def numRows : ℕ := 16

def initRow : Row (F pBabybear) (ProvablePair State unit) := (initialState, ())

def generateTrace (output_path : String) : IO Unit := do
  let trace_data := witnessesWithData femtoCairoTable.inductiveWitness initRow numRows memData
  let json_data := Lean.toJson trace_data
  IO.FS.writeFile output_path json_data.pretty
  IO.println s!"Generated FemtoCairo trace with {numRows} rows -> {output_path}"

def main (args : List String) : IO Unit := do
  match args with
  | [output_path] => generateTrace output_path
  | _ => IO.println "Usage: lake env lean --run FemtoCairoTraceGen.lean <output_path>"
