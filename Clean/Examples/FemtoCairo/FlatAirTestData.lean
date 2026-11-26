module

public import Clean.Examples.FemtoCairo.FlatAir
public import Clean.Utils.Primes

@[expose] public section

/-!
# FemtoCairo Flat AIR test program

This program exercises AP-relative, FP-relative, and immediate memory addressing.
-/

namespace Examples.FemtoCairo.FlatAirTestData

open Types

/-- Seven instructions followed by one padding instruction. -/
def testProgram : Array (F pBabybear) :=
  #[212, 1, 2, 8,       -- ADD mem[ap+1] + mem[ap+2] = 8
     213, 3, 4, 14,      -- MUL mem[ap+3] * mem[ap+4] = 14
     244, 1, 10, 15,     -- ADD mem[ap+1] + 10 = 15
     233, 5, 2, 30,      -- MUL mem[fp+5] * mem[fp+2] = 30
     220, 100, 3, 107,   -- ADD 100 + mem[ap+3] = 107
     212, 4, 5, 12,      -- ADD mem[ap+4] + mem[ap+5] = 12
     252, 0, 0, 0,       -- ADD 0 + 0 = 0
     0, 0, 0, 0]

theorem testProgram_valid : Spec.ValidProgram testProgram where
  size_add_three_lt := by decide
  size_lt_u64 := by decide
  bytes_lt := by
    simp [testProgram, ZMod.val_ofNat, ZMod.val_one]
    decide

theorem memorySize_lt : (8 : UInt64).toNat < pBabybear := by decide

/-- The program starts at `pc = ap = fp = 0`, and halts after eight steps at `pc = 32` with
`ap = fp = 0`. -/
def publicInput : FlatAir.PublicInput (F pBabybear) :=
  { initialState := { pc := 0, ap := 0, fp := 0 }, finalAp := 0, finalFp := 0 }

end Examples.FemtoCairo.FlatAirTestData
