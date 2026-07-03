/-
  Shared test data for FemtoCairo plonky3 backend tests with memory-reading instructions.
  Exercises AP-relative and FP-relative addressing modes with non-trivial memory values.
-/
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Table.Inductive
import Clean.Utils.Primes

open Examples.FemtoCairo
open Examples.FemtoCairo.Types

namespace Examples.FemtoCairo.Plonky3MemoryTestData

-- Test program: 7 instructions using AP-relative, FP-relative, and immediate addressing modes.
-- Program has 32 entries (7 instruction slots × 4 + 4 padding zeros).
-- 7 steps → 8 rows (power of 2, large enough for FRI).
def programSize : ℕ := 32

instance : NeZero programSize := ⟨by decide⟩

-- Instruction byte encoding: bits[0]+2*bits[1]=type, bits[2]+2*bits[3]=mode1, etc.
-- 212 = ADD(0), AP-rel(1), AP-rel(1), imm(3)
-- 213 = MUL(1), AP-rel(1), AP-rel(1), imm(3)
-- 244 = ADD(0), AP-rel(1), imm(3), imm(3)
-- 233 = MUL(1), FP-rel(2), FP-rel(2), imm(3)
-- 220 = ADD(0), imm(3), AP-rel(1), imm(3)
-- 252 = ADD(0), imm(3), imm(3), imm(3)
def programData : Vector (F pBabybear) 32 :=
  #v[212, 1, 2, 8,       -- pc=0:  ADD mem[ap+1] + mem[ap+2] = imm(8)   → 5+3=8
     213, 3, 4, 14,       -- pc=4:  MUL mem[ap+3] * mem[ap+4] = imm(14)  → 7*2=14
     244, 1, 10, 15,      -- pc=8:  ADD mem[ap+1] + imm(10) = imm(15)    → 5+10=15
     233, 5, 2, 30,       -- pc=12: MUL mem[fp+5] * mem[fp+2] = imm(30)  → 10*3=30
     220, 100, 3, 107,    -- pc=16: ADD imm(100) + mem[ap+3] = imm(107)  → 100+7=107
     212, 4, 5, 12,       -- pc=20: ADD mem[ap+4] + mem[ap+5] = imm(12)  → 2+10=12
     252, 0, 0, 0,        -- pc=24: ADD imm(0) + imm(0) = imm(0)         → padding step
     0, 0, 0, 0]          -- pc=28: padding

def testProgram : Fin programSize → F pBabybear :=
  fun i => programData[i]

theorem h_programSize : programSize < pBabybear := by native_decide

theorem h_testValidProgram :
    Spec.ValidProgramSize pBabybear programSize ∧ Spec.ValidProgram testProgram := by
  constructor
  · -- ValidProgramSize: programSize + 3 < pBabybear
    show programSize + 3 < pBabybear
    native_decide
  · -- ValidProgram: all entries have .val < 256
    intro i
    fin_cases i <;> native_decide

def initialState : State (F pBabybear) := { pc := 0, ap := 0, fp := 0 }
-- After 7 steps: pc = 28, ap = 0, fp = 0
def finalState : State (F pBabybear) := { pc := 28, ap := 0, fp := 0 }

def numSteps : ℕ := 7

-- Reuse the fully-proved femtoCairoTable from FemtoCairo.lean.
def femtoCairoTable : InductiveTable (F pBabybear) State unit :=
  Examples.FemtoCairo.femtoCairoTable testProgram h_programSize h_testValidProgram numSteps

-- Memory table: 8 entries with non-trivial values for memory-reading instructions
-- addr: 0  1  2  3  4  5   6  7
-- val:  0  5  3  7  2  10  0  0
def memData : ProverData (F pBabybear) := fun name n =>
  if name == "memory" then
    if h : n = 2 then
      h ▸ (#[#v[(0 : F pBabybear), 0], #v[(1 : F pBabybear), 5],
            #v[(2 : F pBabybear), 3], #v[(3 : F pBabybear), 7],
            #v[(4 : F pBabybear), 2], #v[(5 : F pBabybear), 10],
            #v[(6 : F pBabybear), 0], #v[(7 : F pBabybear), 0]]
           : Array (Vector (F pBabybear) 2))
    else #[]
  else #[]

end Examples.FemtoCairo.Plonky3MemoryTestData
