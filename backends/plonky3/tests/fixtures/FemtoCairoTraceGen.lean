-- Trace generation for the FemtoCairo plonky3 backend
-- Generates the execution trace using witnessesWithData + inductiveWitness
import Lean
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Table.Inductive
import Clean.Table.WitnessGeneration
import Clean.Table.Json
import Clean.Utils.Primes

open Examples.FemtoCairo
open Examples.FemtoCairo.Types

-- Same test program as in FemtoCairoCircuitGen.lean
def programSize : ℕ := 64

instance : NeZero programSize := ⟨by decide⟩

-- Define program directly as Vector (F pBabybear) to keep it computable.
def programData : Vector (F pBabybear) 64 :=
  #v[252, 3, 5, 8,
     252, 10, 20, 30,
     252, 1, 2, 3,
     252, 7, 8, 15,
     252, 4, 6, 10,
     252, 11, 22, 33,
     252, 2, 3, 5,
     252, 9, 1, 10,
     252, 13, 14, 27,
     252, 5, 5, 10,
     252, 6, 7, 13,
     252, 8, 9, 17,
     252, 15, 16, 31,
     252, 20, 30, 50,
     252, 100, 200, 300,
     0, 0, 0, 0]

def testProgram : Fin programSize → F pBabybear :=
  fun i => programData[i]

theorem h_programSize : programSize < pBabybear := by native_decide

def initialState : State (F pBabybear) := { pc := 0, ap := 0, fp := 0 }

-- Memory table: 16 entries (padded for FRI minimum size)
-- All dummy entries for immediate mode (no actual memory reads)
def memData : ProverData (F pBabybear) := fun name n =>
  if name == "memory" then
    if h : n = 2 then
      h ▸ (#[#v[(0 : F pBabybear), 0], #v[(1 : F pBabybear), 0],
            #v[(2 : F pBabybear), 0], #v[(3 : F pBabybear), 0],
            #v[(4 : F pBabybear), 0], #v[(5 : F pBabybear), 0],
            #v[(6 : F pBabybear), 0], #v[(7 : F pBabybear), 0],
            #v[(8 : F pBabybear), 0], #v[(9 : F pBabybear), 0],
            #v[(10 : F pBabybear), 0], #v[(11 : F pBabybear), 0],
            #v[(12 : F pBabybear), 0], #v[(13 : F pBabybear), 0],
            #v[(14 : F pBabybear), 0], #v[(15 : F pBabybear), 0]]
           : Array (Vector (F pBabybear) 2))
    else #[]
  else #[]

-- Build the inductive witness constraint for trace generation
def femtoCairoStepMain : Var State (F pBabybear) → Circuit (F pBabybear) (Var State (F pBabybear)) :=
  (femtoCairoStepElaboratedCircuit testProgram h_programSize).main

def traceConstraint : TableConstraint 2 (ProvablePair State unit) (F pBabybear) Unit := do
  let (acc, _x) ← getCurrRow
  let output ← femtoCairoStepMain acc
  let elems := toVars output
  for h : i in [:size State] do
    have hi : i < size State := Membership.mem.upper h
    have hi' : i < size State + size unit := by omega
    assign (.next ⟨i, hi'⟩) elems[i]

-- N = 16 rows (15 steps)
def numRows : ℕ := 16

def initRow : Row (F pBabybear) (ProvablePair State unit) := (initialState, ())

def generateTrace (output_path : String) : IO Unit := do
  let trace_data := witnessesWithData traceConstraint initRow numRows memData
  let json_data := Lean.toJson trace_data
  IO.FS.writeFile output_path json_data.pretty
  IO.println s!"Generated FemtoCairo trace with {numRows} rows -> {output_path}"

def main (args : List String) : IO Unit := do
  match args with
  | [output_path] => generateTrace output_path
  | _ => IO.println "Usage: lake env lean --run FemtoCairoTraceGen.lean <output_path>"
