import Clean.Orchard.Ecc.ScalarMul.Defs

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul/overflow.rs`.
-/

namespace Orchard.Ecc.ScalarMul.Mul.Overflow

structure Row (F : Type) where
  z0 : F
  z130 : F
  eta : F
  k254 : F
  alpha : F
  sMinusLo130 : F
  s : F
deriving ProvableStruct

def sCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 130)] (row : Row K) : K :=
  row.s - (row.alpha + row.k254 * OfNat.ofNat (2 ^ 130))

def recovery {K : Type} [Sub K] [OfNat K 2]
    [OfNat K 45560315531506369815346746415080538113] (row : Row K) : K :=
  row.z0 - row.alpha - tQ

def loZero {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 124)] (row : Row K) : K :=
  row.k254 * (row.z130 - OfNat.ofNat (2 ^ 124))

def sMinusLo130Check {K : Type} [Mul K] (row : Row K) : K :=
  row.k254 * row.sMinusLo130

def canonicity {K : Type} [One K] [Sub K] [Mul K] (row : Row K) : K :=
  (1 - row.k254) * (1 - row.z130 * row.eta) * row.sMinusLo130

def Spec (row : Row Fp) : Prop :=
  row.s = row.alpha + row.k254 * OfNat.ofNat (2 ^ 130) ∧
    row.z0 = row.alpha + tQ ∧
    (row.k254 = 0 ∨ row.z130 = OfNat.ofNat (2 ^ 124)) ∧
    (row.k254 = 0 ∨ row.sMinusLo130 = 0) ∧
    (row.k254 = 1 ∨ row.z130 * row.eta = 1 ∨ row.sMinusLo130 = 0)

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (sCheck row)
  assertZero (recovery row)
  assertZero (loZero row)
  assertZero (sMinusLo130Check row)
  assertZero (canonicity row)

def circuit : FormalAssertion Fp Row where
  name := "GATE overflow checks"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, sCheck, recovery, loZero,
      sMinusLo130Check, canonicity, tQ]
    rcases h_holds with ⟨hS, hRecovery, hLoZero, hSMinusLo130, hCanonicity⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hS)
    · apply sub_eq_zero.mp
      linear_combination hRecovery
    · rcases mul_eq_zero.mp hLoZero with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h))
    · rcases mul_eq_zero.mp hSMinusLo130 with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rcases mul_eq_zero.mp hCanonicity with hK | hRest
      · rcases mul_eq_zero.mp hK with hK | hEta
        · exact Or.inl (by linear_combination -hK)
        · exact Or.inr (Or.inl (by linear_combination -hEta))
      · exact Or.inr (Or.inr hRest)
  completeness := by
    circuit_proof_start [main, Spec, sCheck, recovery, loZero,
      sMinusLo130Check, canonicity, tQ]
    rcases h_spec with ⟨hS, hRecovery, hLoZero, hSMinusLo130, hCanonicity⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hS
    · exact by linear_combination hRecovery
    · exact by
        rcases hLoZero with h | h
        · rw [h]
          simp
        · rw [h]
          simp
    · exact by
        rcases hSMinusLo130 with h | h
        · rw [h]
          simp
        · rw [h]
          simp
    · exact by
        rcases hCanonicity with hK | hRest
        · rw [hK]
          simp
        · rcases hRest with hEta | hSMinusLo130
          · rw [hEta]
            simp
          · rw [hSMinusLo130]
            simp

end Orchard.Ecc.ScalarMul.Mul.Overflow
