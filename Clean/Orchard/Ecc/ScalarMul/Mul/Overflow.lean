import Clean.Orchard.Ecc.ScalarMul.Defs
import Clean.Orchard.Utilities

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

/-!
### `overflow.rs::Config::overflow_check`

Witnesses `s = alpha + k_254 ⋅ 2^130`, decomposes its low 130 bits with thirteen
10-bit lookups (`copy_check`, strict = false), witnesses `η = inv0(z_130)`, and applies
the overflow gate to the copied cells.
-/

namespace OverflowCheck

/-- Inputs: the original scalar cell and the running-sum cells the check inspects,
`z_0` (full sum), `z_130` (after the hi half), and `k_254 = z_254` (first bit). -/
structure Input (F : Type) where
  alpha : F
  z0 : F
  z130 : F
  k254 : F
deriving ProvableStruct

def main (input : Var Input Fp) : Circuit Fp Unit := do
  -- s = alpha + k_254 ⋅ 2^130
  let s ← witnessField fun env => env input.alpha + env input.k254 * (2 ^ 130 : Fp)
  -- decompose the low 130 bits of s using thirteen 10-bit lookups
  let zsDecomp ← Utilities.LookupRangeCheck.CopyCheck.circuit 13 s
  -- s_minus_lo_130 = (s - (2^0 s_0 + ... + 2^129 s_129)) / 2^130
  let sMinusLo130 := zsDecomp[13]
  -- η = inv0(z_130)
  let eta ← witnessField fun env =>
    if env input.z130 = 0 then 0 else (env input.z130)⁻¹
  Overflow.circuit {
    z0 := input.z0, z130 := input.z130, eta, k254 := input.k254,
    alpha := input.alpha, sMinusLo130, s }

/-- The semantic contract of the overflow check: `z_0` recovers `alpha + t_q`, and the
canonicity disjunctions over the 130-bit decomposition of `s = alpha + k_254 ⋅ 2^130`
hold. The decomposition is existential: some split `s = s_lo + 2^130 ⋅ s_hi` with
`s_lo < 2^130` satisfies the per-case vanishing. -/
def Spec (input : Input Fp) : Prop :=
  input.z0 = input.alpha + tQ ∧
  (input.k254 = 0 ∨ input.z130 = (2 ^ 124 : Fp)) ∧
  ∃ (sHi : Fp) (sLo : ℕ), sLo < 2 ^ 130 ∧
    input.alpha + input.k254 * (2 ^ 130 : Fp) = (sLo : Fp) + (2 ^ 130 : Fp) * sHi ∧
    (input.k254 = 0 ∨ sHi = 0) ∧
    (input.k254 = 1 ∨ input.z130 ≠ 0 ∨ sHi = 0)

instance elaborated : ElaboratedCircuit Fp Input unit main := by
  elaborate_circuit

theorem soundness : FormalAssertion.Soundness Fp main (fun _ => True) Spec := by
  sorry

theorem completeness : FormalAssertion.Completeness Fp main (fun _ => True) Spec := by
  sorry

/-- `overflow.rs::Config::overflow_check`. -/
def circuit : FormalAssertion Fp Input where
  main
  Assumptions _ := True
  Spec
  soundness
  completeness

end OverflowCheck

end Orchard.Ecc.ScalarMul.Mul.Overflow
