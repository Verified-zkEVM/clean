import Clean.Orchard.Ecc.ScalarMul.Defs
import Clean.Orchard.Specs.Elliptic.CurveForms.ShortWeierstrass

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul_fixed/short.rs`.
-/

namespace Orchard.Ecc.ScalarMul.MulFixed.Short

structure Row (F : Type) where
  yP : F
  yA : F
  lastWindow : F
  sign : F
deriving ProvableStruct

def signCheck {K : Type} [One K] [Sub K] [Mul K] (row : Row K) : K :=
  row.sign * row.sign - 1

def yCheck {K : Type} [Add K] [Sub K] [Mul K] (row : Row K) : K :=
  (row.yP - row.yA) * (row.yP + row.yA)

def negationCheck {K : Type} [Sub K] [Mul K] (row : Row K) : K :=
  row.sign * row.yP - row.yA

def IsSign (sign : Fp) : Prop :=
  sign = 1 ∨ sign = 0 - 1

def SignedPointSelection (row : Row Fp) : Prop :=
  ∀ x : Fp,
    (row.sign = 1 → (x, row.yP) = (x, row.yA)) ∧
      (row.sign = 0 - 1 →
        (x, row.yP) = CompElliptic.CurveForms.ShortWeierstrass.neg (x, row.yA))

def Spec (row : Row Fp) : Prop :=
  IsBool row.lastWindow ∧ IsSign row.sign ∧ SignedPointSelection row

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (NoteCommit.boolPoly row.lastWindow)
  assertZero (signCheck row)
  assertZero (yCheck row)
  assertZero (negationCheck row)

def circuit : FormalAssertion Fp Row where
  name := "GATE Short fixed-base mul gate"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, IsSign, SignedPointSelection,
      CompElliptic.CurveForms.ShortWeierstrass.neg, NoteCommit.boolPoly, signCheck, yCheck,
      negationCheck]
    rcases h_holds with ⟨hLastWindow, hSign, _hY, hNegation⟩
    have hSignedY : input_yA = input_sign * input_yP :=
      (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hNegation)).symm
    refine ⟨?_, ?_, ?_⟩
    · exact isBool_of_boolPoly_eq_zero (by
        simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hLastWindow)
    · have hmul : (input_sign - 1) * (input_sign + 1) = 0 := by
        linear_combination hSign
      rcases mul_eq_zero.mp hmul with hPos | hNeg
      · exact Or.inl (sub_eq_zero.mp hPos)
      · exact Or.inr (by linear_combination hNeg)
    · intro x
      constructor
      · intro hPos
        apply Prod.ext
        · rfl
        · rw [hSignedY, hPos]
          simp
      · intro hNeg
        apply Prod.ext
        · rfl
        · rw [hSignedY, hNeg]
          simp
  completeness := by
    circuit_proof_start [main, Spec, IsSign, SignedPointSelection,
      CompElliptic.CurveForms.ShortWeierstrass.neg, NoteCommit.boolPoly, signCheck, yCheck,
      negationCheck]
    rcases h_spec with ⟨hLastWindow, hSign, hPoint⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using
        boolPoly_eq_zero_of_isBool hLastWindow
    · rcases hSign with hSign | hSign <;> rw [hSign] <;> ring
    · rcases hSign with hSign | hSign
      · have hY := congrArg Prod.snd ((hPoint 0).1 hSign)
        simp at hY
        rw [hY]
        ring
      · have hY := congrArg Prod.snd ((hPoint 0).2 hSign)
        simp at hY
        rw [hY]
        ring
    · rcases hSign with hSign | hSign
      · have hY := congrArg Prod.snd ((hPoint 0).1 hSign)
        simp at hY
        rw [hSign, hY]
        ring
      · have hY := congrArg Prod.snd ((hPoint 0).2 hSign)
        simp at hY
        rw [hSign, hY]
        ring

end Orchard.Ecc.ScalarMul.MulFixed.Short
