module

public import Clean.Backends.Plonky3.Lower
public import Clean.Examples.FemtoCairo.FlatAir
public import Clean.Examples.FemtoCairo.FlatAirTestData
public import Clean.Utils.Primes

-- `native_decide` runs compiled code from these modules.
public meta import Clean.Backends.Plonky3.Lower
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
      memoryValues initialState finalRegisters 8 with
  | .error error => .error (toString error)
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

/-- Memory cells are defined by the execution's reads: a hinted value at an address the program
never reads does not enter the witness. -/
example : generateResult alternateMemoryValues = .ok ([8, 8, 32], true, true, 8, 10, 0) := by
  native_decide

/-- The configuration error of exporting with a replaced memory generation mode. -/
def memoryModeError (memory : Mode (F pBabybear)) : Option ConfigError :=
  let config : Config (F pBabybear) :=
    Witness.config (memorySize := 8) testProgram h_programSize initialState 8
  let config : Config (F pBabybear) :=
    { config with components := config.components.map fun (name, generation) =>
        if name = (provideMemory (p := pBabybear)).name then (name, { generation with mode := memory })
        else (name, generation) }
  match Backends.Plonky3.lower
      (formalEnsemble testProgram h_programSize h_memorySize initialState) config with
  | .error (.config error) => some error
  | _ => none

/-- Export rejects witness programs that read cells mutated later by channel balancing. -/
example : memoryModeError (.preallocated {
    rows := 8
    input := .ofFExprs #v[.const 0, .const 0]
    input_valid := by rfl
    handlers := [{ interaction := 0, column := 1 }]
    lazyColumns := [1] }) =
    some (.lazyHandlerColumn "memory" 1) := by native_decide

/-- Export rejects reads of handler columns, which balancing mutates. -/
example : (match memoryModeError (.preallocated {
    rows := 8
    input := .ofFExprs #v[.const 0, .const 0]
    input_valid := by rfl
    handlers := [{ interaction := 0, column := 1 }] }) with
    | some (.unstableDataRead _ _ "memory" 1) => true
    | _ => false) = true := by native_decide

end Examples.FemtoCairo.FlatAirTest
