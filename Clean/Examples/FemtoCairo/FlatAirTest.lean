import Clean.Examples.FemtoCairo.FlatAir
import Clean.Examples.FemtoCairo.Plonky3MemoryTestData
import Clean.Utils.Primes

namespace Examples.FemtoCairo.FlatAirTest

open Air.Flat
open Examples.FemtoCairo
open Examples.FemtoCairo.Types
open Examples.FemtoCairo.FlatAir
open Examples.FemtoCairo.Plonky3MemoryTestData
open Air.Flat.WitnessGeneration

private def memoryValues : Fin 8 → F pBabybear := fun i =>
  (#v[0, 5, 3, 7, 2, 10, 0, 0] : Vector (F pBabybear) 8)[i]

private def finalStateAfterEight : State (F pBabybear) := { pc := 32, ap := 0, fp := 0 }

private theorem h_memorySize : 8 < pBabybear := by native_decide

private def result : Except String (List ℕ × Bool × Bool × ℕ × ℕ) :=
  match Examples.FemtoCairo.FlatAir.Witness.generate
      (p := pBabybear) (programSize := programSize) (memorySize := 8)
      testProgram h_programSize h_memorySize
      memoryValues initialState finalStateAfterEight 8 1000 with
  | .error error => .error error
  | .ok witness =>
    let memoryData := witness.data "memory" 2
    let memoryValue := match memoryData[5]? with
      | some row => (row[1]?.getD 0).val
      | none => 0
    .ok (witness.tables.map (fun table => table.table.length),
      constraintsHold witness,
      channelsBalanced witness, memoryData.size, memoryValue)

/--
The full channel-driven witness contains eight execution rows, the eight-row fixed
memory, and the 32-row fixed program. The derived prover data preserves the non-trivial
memory value used by the execution trace.
-/
example : result = .ok ([8, 8, 32], true, true, 8, 10) := by native_decide

end Examples.FemtoCairo.FlatAirTest
