import Clean.Orchard.Ecc.ScalarMul.Defs
import Clean.Orchard.Specs.Elliptic.CurveForms.ShortWeierstrass

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul/complete.rs`.
-/

namespace Orchard.Ecc.ScalarMul.Mul.Complete

structure Row (F : Type) where
  zPrev : F
  zNext : F
  baseY : F
  yP : F
deriving ProvableStruct

def bit {K : Type} [Sub K] [Mul K] [OfNat K 2] (row : Row K) : K :=
  row.zNext - 2 * row.zPrev

def ySwitch {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (row : Row K) : K :=
  ternary (bit row) (row.baseY - row.yP) (row.baseY + row.yP)

def SelectedCompleteBitPointNegation (row : Row Fp) : Prop :=
  ∀ baseX : Fp,
    (bit row = 0 →
      (baseX, row.yP) =
        CompElliptic.CurveForms.ShortWeierstrass.neg (baseX, row.baseY)) ∧
      (bit row = 1 →
        (baseX, row.yP) = (baseX, row.baseY))

def Spec (row : Row Fp) : Prop :=
  IsBool (bit row) ∧ SelectedCompleteBitPointNegation row

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (NoteCommit.boolPoly (bit row))
  assertZero (ySwitch row)

def circuit : FormalAssertion Fp Row where
  name := "GATE Decompose scalar for complete bits of variable-base mul"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, SelectedCompleteBitPointNegation,
      NoteCommit.boolPoly, bit, ySwitch, CompElliptic.CurveForms.ShortWeierstrass.neg]
    rcases h_holds with ⟨hBool, hSwitch⟩
    rcases h_input with ⟨hzPrev, hzNext, hbaseY, hyP⟩
    constructor
    · exact isBool_of_boolPoly_eq_zero (by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hBool)
    · intro x
      constructor
      · intro hBit
        apply Prod.ext
        · rfl
        · have hSwitch' := hSwitch
          simp [circuit_norm, ternary, hzPrev, hzNext, hbaseY, hyP] at hSwitch'
          linear_combination hSwitch' + (2 * input_yP) * hBit
      · intro hBit
        apply Prod.ext
        · rfl
        · have hSwitch' := hSwitch
          simp [circuit_norm, ternary, hzPrev, hzNext, hbaseY, hyP] at hSwitch'
          have hBitNorm : input_zNext + -(2 * input_zPrev) = 1 := by
            linear_combination hBit
          have hCoeff : 1 + (2 * input_zPrev + -input_zNext) = 0 := by
            linear_combination -hBitNorm
          have hDiff : input_baseY + -input_yP = 0 := by
            linear_combination hSwitch' - (input_baseY + -input_yP) * hBitNorm -
              (input_baseY + input_yP) * hCoeff
          linear_combination -hDiff
  completeness := by
    circuit_proof_start [main, Spec, SelectedCompleteBitPointNegation,
      NoteCommit.boolPoly, bit, ySwitch, CompElliptic.CurveForms.ShortWeierstrass.neg]
    rcases h_spec with ⟨hBool, hSelect⟩
    rcases h_input with ⟨hzPrev, hzNext, hbaseY, hyP⟩
    constructor
    · exact by simpa [NoteCommit.boolPoly, sub_eq_add_neg] using boolPoly_eq_zero_of_isBool hBool
    · rcases hBool with hBit | hBit
      · exact by
          have hPoint := (hSelect 0).1 hBit
          have hy := congrArg Prod.snd hPoint
          simp at hy
          simp [circuit_norm, ternary, hzPrev, hzNext, hbaseY, hyP, hy]
          left
          simpa [sub_eq_add_neg] using hBit
      · exact by
          have hPoint := (hSelect 0).2 hBit
          have hy := congrArg Prod.snd hPoint
          simp at hy
          simp [circuit_norm, ternary, hzPrev, hzNext, hbaseY, hyP, hy]
          left
          linear_combination -hBit

end Orchard.Ecc.ScalarMul.Mul.Complete
