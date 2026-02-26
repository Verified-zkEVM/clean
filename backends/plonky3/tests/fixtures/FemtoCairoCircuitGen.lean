-- Circuit JSON generation for the FemtoCairo plonky3 backend
-- Generates the circuit structure (constraints + lookups) as JSON
import Lean
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Table.Inductive
import Clean.Table.Json
import Clean.Utils.Primes

open Examples.FemtoCairo
open Examples.FemtoCairo.Types

-- Test program: 15 ADD instructions with all-immediate addressing mode.
-- Instruction byte for ADD+all-immediate = 252 (bits: 00_11_11_11 → 0b11111100)
-- Each instruction occupies 4 entries: [instr, op1, op2, op3]
-- Program has 64 entries (16 instruction slots, 15 real + 1 padding).
-- 15 steps → 16 rows (power of 2, large enough for FRI).
def programSize : ℕ := 64

instance : NeZero programSize := ⟨by decide⟩

-- Define program directly as Vector (F pBabybear) to keep it computable.
-- (Using Vector ℕ with a cast would trigger noncomputable Nat.cast.)
def programData : Vector (F pBabybear) 64 :=
  #v[252, 3, 5, 8,       -- pc=0:  ADD 3 + 5 = 8
     252, 10, 20, 30,     -- pc=4:  ADD 10 + 20 = 30
     252, 1, 2, 3,        -- pc=8:  ADD 1 + 2 = 3
     252, 7, 8, 15,       -- pc=12: ADD 7 + 8 = 15
     252, 4, 6, 10,       -- pc=16: ADD 4 + 6 = 10
     252, 11, 22, 33,     -- pc=20: ADD 11 + 22 = 33
     252, 2, 3, 5,        -- pc=24: ADD 2 + 3 = 5
     252, 9, 1, 10,       -- pc=28: ADD 9 + 1 = 10
     252, 13, 14, 27,     -- pc=32: ADD 13 + 14 = 27
     252, 5, 5, 10,       -- pc=36: ADD 5 + 5 = 10
     252, 6, 7, 13,       -- pc=40: ADD 6 + 7 = 13
     252, 8, 9, 17,       -- pc=44: ADD 8 + 9 = 17
     252, 15, 16, 31,     -- pc=48: ADD 15 + 16 = 31
     252, 20, 30, 50,     -- pc=52: ADD 20 + 30 = 50
     252, 100, 200, 300,  -- pc=56: ADD 100 + 200 = 300
     0, 0, 0, 0]          -- pc=60: padding

def testProgram : Fin programSize → F pBabybear :=
  fun i => programData[i]

theorem h_programSize : programSize < pBabybear := by native_decide

def initialState : State (F pBabybear) := { pc := 0, ap := 0, fp := 0 }
-- After 15 steps: pc = 60, ap = 0, fp = 0
def finalState : State (F pBabybear) := { pc := 60, ap := 0, fp := 0 }

-- Build the step circuit directly from the elaborated circuit's main function.
def femtoCairoStepMain : Var State (F pBabybear) → Circuit (F pBabybear) (Var State (F pBabybear)) :=
  (femtoCairoStepElaboratedCircuit testProgram h_programSize).main

-- Build the two-row constraint using assign (same formulation as the trace generator).
-- Using assign instead of getNextRow + === avoids allocating extra witness columns
-- that would widen the trace beyond what witnessesWithData produces.
def femtoCairoRelation : TwoRowsConstraint (ProvablePair State unit) (F pBabybear) := do
  let (acc, _x) ← getCurrRow
  let output ← femtoCairoStepMain acc
  let elems := toVars output
  for h : i in [:size State] do
    have hi : i < size State := Membership.mem.upper h
    have hi' : i < size State + size unit := by omega
    assign (.next ⟨i, hi'⟩) elems[i]

def femtoCairoConstraints : List (TableOperation (ProvablePair State unit) (F pBabybear)) := [
  .everyRowExceptLast femtoCairoRelation,
  .boundary (.fromStart 0) (InductiveTable.equalityConstraint unit initialState),
  .boundary (.fromEnd 0) (InductiveTable.equalityConstraint unit finalState),
]

def generateCircuit (output_path : String) : IO Unit := do
  let circuit_json := Lean.toJson femtoCairoConstraints
  IO.FS.writeFile output_path circuit_json.pretty

def main (args : List String) : IO Unit := do
  match args with
  | [output_path] => generateCircuit output_path
  | _ => IO.println "Usage: lake env lean --run FemtoCairoCircuitGen.lean <output_path>"
