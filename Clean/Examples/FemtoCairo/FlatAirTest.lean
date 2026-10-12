module

public import Clean.Air.Extraction.Lower
public import Clean.Examples.FemtoCairo.FlatAir
public import Clean.Examples.FemtoCairo.FlatAirTestData
public import Clean.Utils.Primes

-- `native_decide` runs compiled code from these modules.
public meta import Clean.Air.Extraction.Lower
public meta import Clean.Examples.FemtoCairo.FlatAir
public meta import Clean.Examples.FemtoCairo.FlatAirTestData
public meta import Clean.Utils.Primes

@[expose] public section

namespace Examples.FemtoCairo.FlatAirTest

open Air.Flat
open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.FlatAir
open Examples.FemtoCairo.FlatAirTestData
open Air.Flat.WitnessGeneration

def memoryValues : fields 8 (F pBabybear) :=
  #v[0, 5, 3, 7, 2, 10, 0, 0]

def alternateMemoryValues : fields 8 (F pBabybear) :=
  #v[0, 5, 3, 7, 2, 10, 0, 99]

/-- The program halts after eight steps at `pc = 32` with `ap = fp = 0`. -/
def finalRegisters : fieldPair (F pBabybear) := (0, 0)

def generateResult (memoryValues : fields 8 (F pBabybear)) :
    Except String (List ℕ × Bool × Bool × ℕ × ℕ × ℕ) :=
  match Examples.FemtoCairo.FlatAir.Witness.generate
      (p := pBabybear) (programSize := programSize) (memorySize := 8)
      testProgram h_programSize h_memorySize
      memoryValues initialState finalRegisters 8 1000 with
  | .error error => .error error
  | .ok witness =>
    let memoryData := witness.data "memory" 3
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
The full channel-driven witness contains eight execution rows, the eight-row fixed
memory, and the 32-row fixed program. The derived prover data exposes each complete
memory input row, including its multiplicity, while preserving the non-trivial value
used by the execution trace.
-/
example : result = .ok ([8, 8, 32], true, true, 8, 10, 0) := by native_decide

/-- The same Lean witness program accepts a second runtime memory without changing
the compiled ensemble or generation configuration. -/
example : generateResult alternateMemoryValues = .ok ([8, 8, 32], true, true, 8, 10, 99) := by
  native_decide

def unstableDataReadRejected : Bool :=
  let config : Config (F pBabybear) (fields 8) :=
    Witness.config (memorySize := 8) testProgram initialState 8 1000
  let mutableMemory : Mode (F pBabybear) := .preallocated {
    rows := 8
    input := .ofFExprs #v[.proverInputGet .idx, .const 0]
    input_valid := by rfl
    handlers := [{ interaction := 0, column := 1 }]
  }
  let config : Config (F pBabybear) (fields 8) :=
    { config with modes := config.modes.set 1 mutableMemory }
  match Air.Flat.Extraction.lower
      (soundEnsemble testProgram h_programSize h_memorySize initialState).ensemble config with
  | .error (.unstableDataRead _ _ "memory" 1) => true
  | _ => false

/-- Export rejects witness programs that read cells mutated later by channel balancing. -/
example : unstableDataReadRejected = true := by native_decide

end Examples.FemtoCairo.FlatAirTest
