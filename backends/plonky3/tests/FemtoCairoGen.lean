-- FemtoCairo trace and circuit generation for plonky3 backend
-- Generates both circuit JSON (constraints) and trace JSON (witness) for a simple test program.
import Lean
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Table.WitnessGeneration
import Clean.Table.Json
import Clean.Utils.Primes

open Examples.FemtoCairo
open Examples.FemtoCairo.Types

-- Test program: 3 ADD instructions with immediate addressing mode
-- Instruction byte: ADD=00, mode1=11(immediate), mode2=11(immediate), mode3=11(immediate)
-- Binary: 11_11_11_00 = 252
-- Program layout (16 words, padded to power of 2):
--   pc=0:  ADD 1 + 2 = 3
--   pc=4:  ADD 10 + 20 = 30
--   pc=8:  ADD 100 + 50 = 150
--   pc=12: ADD 0 + 0 = 0 (padding, not executed)
def programSize : ℕ := 16

instance : NeZero programSize := ⟨by decide⟩

def programData : Fin programSize → (F pBabybear) := fun i =>
  let values : List ℕ := [252, 1, 2, 3, 252, 10, 20, 30, 252, 100, 50, 150, 252, 0, 0, 0]
  (values.getD i.val 0 : F pBabybear)

theorem programSize_lt_p : programSize < pBabybear := by native_decide

theorem validProgramAndSize :
    Spec.ValidProgramSize pBabybear programSize ∧ Spec.ValidProgram programData := by
  constructor
  · -- ValidProgramSize: programSize + 3 < pBabybear
    simp only [Spec.ValidProgramSize, programSize, pBabybear]; omega
  · -- ValidProgram: all values < 256
    intro i
    fin_cases i <;> simp [programData, pBabybear] <;> native_decide

-- Build the FemtoCairo inductive table for 3 steps
def femtoCairoInstance :=
  femtoCairoTable programData programSize_lt_p validProgramAndSize 3

-- Initial state: pc=0, ap=0, fp=0
def initState : State (F pBabybear) := { pc := 0, ap := 0, fp := 0 }

-- Final state after 3 ADD steps: pc=12, ap=0, fp=0
def finalState : State (F pBabybear) := { pc := 12, ap := 0, fp := 0 }

-- Initial row for the trace (State × Unit)
def initRow : Row (F pBabybear) (ProvablePair State unit) := (initState, ())

-- ProverData: memory table with 2 entries (padded to power of 2)
-- Entry 0: (addr=0, value=0) — used as dummy for immediate mode lookups
-- Entry 1: (addr=1, value=0)
def testProverData : ProverData (F pBabybear) := fun name n =>
  if name == "memory" then
    if h : n = 2 then
      h ▸ #[⟨#[(0 : F pBabybear), 0], rfl⟩, ⟨#[(1 : F pBabybear), 0], rfl⟩]
    else #[]
  else #[]

-- Generate circuit JSON
def generateCircuitJson : Lean.Json :=
  Lean.toJson (femtoCairoInstance.tableConstraints initState finalState)

-- Generate trace using witness generators with state propagation fix.
-- InductiveTable's generateNextRow has a circular dependency: getNextRow generators
-- read from the next row's own state columns (which are still zero). The step output
-- is correctly placed in aux columns but not copied to state columns.
-- Fix: after each step, copy the step output (aux cols 30-32) to state columns (0-2).
def generateTrace : Array (Array (F pBabybear)) := Id.run do
  let tc := femtoCairoInstance.inductiveConstraint
  let stateSize := 3  -- size State
  -- Step output is at trace columns: stateSize + stepLocalLength - stateSize = stepLocalLength
  -- For FemtoCairo: localLength=30, so step output is at columns 30, 31, 32
  let stepOutputStart := 30

  let auxCols := Array.replicate tc.finalAssignment.numAux (0 : F pBabybear)
  let initRowArr := (toElements initRow).toArray ++ auxCols

  let mut trace := #[initRowArr]
  let mut current := initRowArr

  for _ in [:3] do  -- 3 steps
    let mut next := generateNextRow tc current testProverData
    -- Fix: copy step output to state columns
    for i in [:stateSize] do
      next := next.set! i (next[stepOutputStart + i]!)
    trace := trace.push next
    current := next
  trace

-- Main: generate both files
def main (args : List String) : IO Unit := do
  match args with
  | [circuit_path, trace_path] =>
    IO.println "Generating FemtoCairo circuit JSON..."
    let circuitJson := generateCircuitJson
    IO.FS.writeFile circuit_path circuitJson.pretty
    IO.println s!"Circuit JSON written to {circuit_path}"

    IO.println "Generating FemtoCairo trace JSON..."
    let traceData := generateTrace
    let traceJson := Lean.toJson traceData
    IO.FS.writeFile trace_path traceJson.pretty
    IO.println s!"Trace JSON written to {trace_path}"
  | _ =>
    IO.println "Usage: lake env lean --run FemtoCairoGen.lean <circuit_path> <trace_path>"
