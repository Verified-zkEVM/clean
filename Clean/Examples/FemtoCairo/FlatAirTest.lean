module

public import Clean.Backends.Program
public import Clean.Examples.FemtoCairo.FlatAir
public import Clean.Examples.FemtoCairo.FlatAirTestData
public import Clean.Utils.Primes

-- `native_decide` runs compiled code from these modules.
public meta import Clean.Backends.Program
public meta import Clean.Examples.FemtoCairo.FlatAir
public meta import Clean.Examples.FemtoCairo.FlatAirTestData
public meta import Clean.Utils.Primes

@[expose] public section

namespace Examples.FemtoCairo.FlatAirTest

open Air.Flat
open Types
open FlatAir
open FlatAirTestData
open Air.Flat.WitnessGeneration

def memoryValues : fields 8 (F pBabybear) :=
  #v[0, 5, 3, 7, 2, 10, 0, 0]

def alternateMemoryValues : fields 8 (F pBabybear) :=
  #v[0, 5, 3, 7, 2, 10, 0, 99]

/-- The program halts after eight steps at `pc = 32` with `ap = fp = 0`. -/
def finalRegisters : fieldPair (F pBabybear) := (0, 0)

def generateResult (memoryValues : fields 8 (F pBabybear)) (executionRows : UInt64 := 8) :
    Except String (List ℕ × Bool × Bool × ℕ × ℕ × ℕ) :=
  match Witness.generate
      (p := pBabybear) (memorySize := 8)
      testProgram testProgram_valid memorySize_lt
      memoryValues initialState finalRegisters executionRows 1000 with
  | .error error => .error (toString error)
  | .ok witness =>
    let memoryData := witness.data.tables "memory" 3
    let memoryValue := match memoryData[5]? with
      | some row => (row[1]?.getD 0).val
      | none => 0
    let lastMemoryValue := match memoryData[7]? with
      | some row => (row[1]?.getD 0).val
      | none => 0
    .ok (witness.tables.map (fun table => table.table.length),
      constraintsHold witness, channelsBalanced witness, memoryData.size, memoryValue,
      lastMemoryValue)

def result := generateResult memoryValues

/--
The full channel-driven witness contains eight execution rows, the eight-row fixed memory, and the
32-row fixed program. The derived prover data exposes each complete memory input row, including its
multiplicity, while preserving the non-trivial value used by the execution trace.
-/
example : result = .ok ([8, 8, 32], true, true, 8, 10, 0) := by native_decide

/-- The same Lean witness program accepts a second runtime memory without changing the compiled
ensemble or generation configuration. -/
example : generateResult alternateMemoryValues = .ok ([8, 8, 32], true, true, 8, 10, 99) := by
  native_decide

/-- Execution rows beyond the run are disabled padding rows at the initial state. -/
example : generateResult memoryValues 16 = .ok ([16, 8, 32], true, true, 8, 10, 0) := by
  native_decide

def unstableDataReadRejected : Bool :=
  let config : Config (F pBabybear) :=
    Witness.config (memorySize := 8) testProgram testProgram_valid initialState 8 1000
  let mutableMemory : Mode (F pBabybear) := .preallocated {
    rows := 8
    input := .ofFExprs #v[.hintGet memoryValuesKey 1 .idx 0, .const 0]
    input_valid := by rfl
    handlers := [{ interaction := 0, column := 1 }]
  }
  let config : Config (F pBabybear) :=
    { config with components := config.components.map fun (name, generation) =>
        if name = "memory" then
          (name, { generation with mode := mutableMemory })
        else (name, generation) }
  match Backends.lower
      (formalEnsemble testProgram testProgram_valid memorySize_lt initialState) config with
  | .error (.config (.unstableDataRead _ _ "memory" 1)) => true
  | _ => false

/-- Export rejects witness programs that read cells mutated later by channel balancing. -/
example : unstableDataReadRejected = true := by native_decide

end Examples.FemtoCairo.FlatAirTest
