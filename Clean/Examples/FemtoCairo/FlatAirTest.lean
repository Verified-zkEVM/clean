module

public import Clean.Examples.FemtoCairo.FlatAir
public import Clean.Examples.FemtoCairo.FlatAirTestData
public import Clean.Utils.Primes

-- `native_decide` runs compiled code from these modules.
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

/-- The program halts after eight steps at `pc = 32` with `ap = fp = 0`. -/
def result : Except String (List ℕ × Bool × Bool) :=
  match Witness.generate (p := pBabybear) (memorySize := 8) testProgram testProgram_valid
      memorySize_lt #v[0, 5, 3, 7, 2, 10, 0, 0] initialState (0, 0) 8 1000 with
  | .error error => .error (toString error)
  | .ok witness =>
    .ok (witness.tables.map (·.table.length), constraintsHold witness, channelsBalanced witness)

/-- The witness has eight execution rows, the eight-row memory, and the 32-row program. -/
example : result = .ok ([8, 8, 32], true, true) := by native_decide

end Examples.FemtoCairo.FlatAirTest
