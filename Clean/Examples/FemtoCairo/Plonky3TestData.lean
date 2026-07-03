/-
  Shared test data for FemtoCairo plonky3 backend tests.
  Used by both FemtoCairoCircuitGen.lean and FemtoCairoTraceGen.lean.
-/
import Clean.Examples.FemtoCairo.FemtoCairo
import Clean.Table.Inductive
import Clean.Utils.Primes

open Examples.FemtoCairo
open Examples.FemtoCairo.Types

namespace Examples.FemtoCairo.Plonky3TestData

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
     252, 50, 100, 150,   -- pc=56: ADD 50 + 100 = 150
     0, 0, 0, 0]          -- pc=60: padding

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
-- After 15 steps: pc = 60, ap = 0, fp = 0
def finalState : State (F pBabybear) := { pc := 60, ap := 0, fp := 0 }

def numSteps : ℕ := 15

-- Reuse the fully-proved femtoCairoTable from FemtoCairo.lean.
-- Only `.step` is used at runtime (via `tableConstraints` / `inductiveConstraint`);
-- the proof fields ensure the kernel is sound (no sorry's).
def femtoCairoTable : InductiveTable (F pBabybear) State unit :=
  Examples.FemtoCairo.femtoCairoTable testProgram h_programSize h_testValidProgram numSteps

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

end Examples.FemtoCairo.Plonky3TestData
