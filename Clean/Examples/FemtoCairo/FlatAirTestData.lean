module

public import Clean.Examples.FemtoCairo.Spec
public import Clean.Utils.Primes

@[expose] public section

/-!
# FemtoCairo Flat AIR test program

This program exercises AP-relative, FP-relative, and immediate memory addressing.
-/

open Examples.FemtoCairo
open Examples.FemtoCairo.Types

namespace Examples.FemtoCairo.FlatAirTestData

def programSize : UInt64 := 32

instance : NeZero programSize.toNat := ⟨by decide⟩

/-- Seven instructions followed by one padding instruction. -/
def programData : Vector (F pBabybear) programSize.toNat :=
  #v[212, 1, 2, 8,       -- ADD mem[ap+1] + mem[ap+2] = 8
     213, 3, 4, 14,      -- MUL mem[ap+3] * mem[ap+4] = 14
     244, 1, 10, 15,     -- ADD mem[ap+1] + 10 = 15
     233, 5, 2, 30,      -- MUL mem[fp+5] * mem[fp+2] = 30
     220, 100, 3, 107,   -- ADD 100 + mem[ap+3] = 107
     212, 4, 5, 12,      -- ADD mem[ap+4] + mem[ap+5] = 12
     252, 0, 0, 0,       -- ADD 0 + 0 = 0
     0, 0, 0, 0]

def testProgram : Fin programSize.toNat → F pBabybear := fun i => programData[i]

theorem programSize_lt : programSize.toNat < pBabybear := by decide

theorem memorySize_lt : (8 : UInt64).toNat < pBabybear := by decide

def initialState : State (F pBabybear) := { pc := 0, ap := 0, fp := 0 }

end Examples.FemtoCairo.FlatAirTestData
