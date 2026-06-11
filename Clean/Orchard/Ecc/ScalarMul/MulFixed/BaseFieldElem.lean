import Clean.Orchard.Ecc.ScalarMul.MulFixed

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul_fixed/base_field_elem.rs`.
-/

namespace Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem

structure Row (F : Type) where
  alpha : F
  z84Alpha : F
  alpha1 : F
  alpha2 : F
  alpha0Prime : F
  z13Alpha0Prime : F
  z44Alpha : F
  z43Alpha : F
deriving ProvableStruct

def alpha0 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 252)] (row : Row K) : K :=
  row.alpha - row.z84Alpha * OfNat.ofNat (2 ^ 252)

def alpha1RangeCheck {K : Type} [One K] [Sub K] [Mul K] [OfNat K 2] [OfNat K 3]
    (row : Row K) : K :=
  row.alpha1 * (1 - row.alpha1) * (2 - row.alpha1) * (3 - row.alpha1)

def z84AlphaCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 4] (row : Row K) : K :=
  row.z84Alpha - (row.alpha1 + row.alpha2 * 4)

def alpha0PrimeCheck {K : Type} [Add K] [Sub K] [Mul K]
    [OfNat K (2 ^ 130)] [OfNat K (2 ^ 252)]
    [OfNat K 45560315531419706090280762371685220353] (row : Row K) : K :=
  row.alpha0Prime - (alpha0 row + OfNat.ofNat (2 ^ 130) - NoteCommit.tP)

def alpha0Hi120 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 120)] (row : Row K) : K :=
  row.z44Alpha - row.z84Alpha * OfNat.ofNat (2 ^ 120)

def a43 {K : Type} [Sub K] [Mul K] [OfNat K 8] (row : Row K) : K :=
  row.z43Alpha - row.z44Alpha * 8

def IsAlpha1 (alpha1 : Fp) : Prop :=
  alpha1 = 0 ∨ alpha1 = 1 ∨ alpha1 = 2 ∨ alpha1 = 3

def DecomposesBaseFieldElem (row : Row Fp) : Prop :=
  row.z84Alpha = row.alpha1 + row.alpha2 * 4 ∧
    row.alpha0Prime = alpha0 row + OfNat.ofNat (2 ^ 130) - NoteCommit.tP

def CanonicalHighBit (row : Row Fp) : Prop :=
  row.alpha2 = 1 →
    row.alpha1 = 0 ∧ alpha0Hi120 row = 0 ∧ IsBool (a43 row) ∧ row.z13Alpha0Prime = 0

def Spec (row : Row Fp) : Prop :=
  IsAlpha1 row.alpha1 ∧ IsBool row.alpha2 ∧ DecomposesBaseFieldElem row ∧
    CanonicalHighBit row

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.alpha2 * row.alpha1)
  assertZero (row.alpha2 * alpha0Hi120 row)
  assertZero (row.alpha2 * NoteCommit.boolPoly (a43 row))
  assertZero (row.alpha2 * row.z13Alpha0Prime)
  assertZero (alpha1RangeCheck row)
  assertZero (NoteCommit.boolPoly row.alpha2)
  assertZero (z84AlphaCheck row)
  assertZero (alpha0PrimeCheck row)

def circuit : FormalAssertion Fp Row where
  name := "GATE Canonicity checks"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, IsAlpha1, DecomposesBaseFieldElem,
      CanonicalHighBit, alpha0, alpha1RangeCheck, z84AlphaCheck, alpha0PrimeCheck,
      alpha0Hi120, a43, NoteCommit.boolPoly, NoteCommit.tP]
    rcases h_holds with ⟨hAlpha21, hAlpha2Hi, hAlpha2A43, hAlpha2Z13, hAlpha1Range,
      hAlpha2Bool, hZ84, hAlpha0Prime⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases mul_eq_zero.mp hAlpha1Range with hPrefix | h3
      · rcases mul_eq_zero.mp hPrefix with hPrefix | h2
        · rcases mul_eq_zero.mp hPrefix with h0 | h1
          · exact Or.inl h0
          · exact Or.inr (Or.inl (by linear_combination -h1))
        · exact Or.inr (Or.inr (Or.inl (by linear_combination -h2)))
      · exact Or.inr (Or.inr (Or.inr (by linear_combination -h3)))
    · rcases mul_eq_zero.mp hAlpha2Bool with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by linear_combination h1)
    · constructor
      · exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hZ84)
      · exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hAlpha0Prime)
    · intro hAlpha2
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hAlpha2] at hAlpha21
        simpa using hAlpha21
      · rw [hAlpha2] at hAlpha2Hi
        simpa [sub_eq_add_neg] using hAlpha2Hi
      · have hA43Poly : NoteCommit.boolPoly (input_z43Alpha - input_z44Alpha * 8) = 0 := by
          have hMul :
              input_alpha2 * NoteCommit.boolPoly (input_z43Alpha - input_z44Alpha * 8) = 0 := by
            simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hAlpha2A43
          rw [hAlpha2] at hMul
          simpa using hMul
        exact isBool_of_boolPoly_eq_zero hA43Poly
      · rw [hAlpha2] at hAlpha2Z13
        simpa using hAlpha2Z13
  completeness := by
    circuit_proof_start [main, Spec, IsAlpha1, DecomposesBaseFieldElem,
      CanonicalHighBit, alpha0, alpha1RangeCheck, z84AlphaCheck, alpha0PrimeCheck,
      alpha0Hi120, a43, NoteCommit.boolPoly, NoteCommit.tP]
    rcases h_spec with ⟨hAlpha1, hAlpha2, ⟨hZ84, hAlpha0Prime⟩, hCanon⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · exact by
          rw [h1, (hCanon h1).1]
          ring
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · rw [h1]
        simpa [sub_eq_add_neg] using (hCanon h1).2.1
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · exact by
          have hBoolA43 := boolPoly_eq_zero_of_isBool (hCanon h1).2.2.1
          rw [h1]
          simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hBoolA43
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · rw [h1, (hCanon h1).2.2.2]
        ring
    · rcases hAlpha1 with h0 | h1 | h2 | h3
      · rw [h0]
        ring
      · rw [h1]
        ring
      · rw [h2]
        ring
      · rw [h3]
        ring
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · rw [h1]
        ring
    · rw [hZ84]
      ring
    · rw [hAlpha0Prime]
      ring

end Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem
