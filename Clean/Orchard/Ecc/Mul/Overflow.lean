import Clean.Orchard.Ecc.Defs
import Clean.Orchard.Utilities

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul/overflow.rs`.
-/

namespace Orchard.Ecc.Mul.Overflow

structure Input (F : Type) where
  z0 : F
  z130 : F
  eta : F
  k254 : F
  alpha : F
  sMinusLo130 : F
  s : F
deriving ProvableStruct

def sCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K (2 ^ 130)] (row : Input K) : K :=
  row.s - (row.alpha + row.k254 * OfNat.ofNat (2 ^ 130))

def recovery {K : Type} [Sub K] [OfNat K 2]
    [OfNat K 45560315531506369815346746415080538113] (row : Input K) : K :=
  row.z0 - row.alpha - tQ

def loZero {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 124)] (row : Input K) : K :=
  row.k254 * (row.z130 - OfNat.ofNat (2 ^ 124))

def sMinusLo130Check {K : Type} [Mul K] (row : Input K) : K :=
  row.k254 * row.sMinusLo130

def canonicity {K : Type} [One K] [Sub K] [Mul K] (row : Input K) : K :=
  (1 - row.k254) * (1 - row.z130 * row.eta) * row.sMinusLo130

def Spec (row : Input Fp) : Prop :=
  row.s = row.alpha + row.k254 * OfNat.ofNat (2 ^ 130) ∧
    row.z0 = row.alpha + tQ ∧
    (row.k254 = 0 ∨ row.z130 = OfNat.ofNat (2 ^ 124)) ∧
    (row.k254 = 0 ∨ row.sMinusLo130 = 0) ∧
    (row.k254 = 1 ∨ row.z130 * row.eta = 1 ∨ row.sMinusLo130 = 0)

def main (row : Var Input Fp) : Circuit Fp Unit := do
  assertZero (sCheck row)
  assertZero (recovery row)
  assertZero (loZero row)
  assertZero (sMinusLo130Check row)
  assertZero (canonicity row)

def circuit : FormalAssertion Fp Input where
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
  let s ← witness (input.alpha + input.k254 * (2 ^ 130 : Fp))
  -- decompose the low 130 bits of s using thirteen 10-bit lookups
  let zsDecomp ← Utilities.LookupRangeCheck.CopyCheck.circuit 13 s
  -- s_minus_lo_130 = (s - (2^0 s_0 + ... + 2^129 s_129)) / 2^130
  let sMinusLo130 := zsDecomp[13]
  -- η = inv0(z_130)
  let eta ← witness (.ite (input.z130 =? 0) 0 input.z130⁻¹)
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

/-- Name the evaluation of a vector's cell 13 opaquely; stating this over an abstract
`v` lets the caller instantiate it with a concrete append term whose `getElem` bound
would not elaborate inline. -/
private theorem eval_get13 (env : Environment Fp) (v : Vector (Expression Fp) 14) :
    ∃ z, Expression.eval env v[13] = z := ⟨_, rfl⟩

theorem soundness : FormalAssertion.Soundness Fp main (fun _ => True) Spec := by
  circuit_proof_start [main, Spec, Utilities.LookupRangeCheck.CopyCheck.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Spec, Overflow.circuit, Overflow.Spec]
  obtain ⟨⟨hS0, hChain⟩, hS, hRec, hLoZ, hSHiZ, hEta⟩ := h_holds
  have h2124 : (OfNat.ofNat (2 ^ 124) : Fp) = (2 : Fp) ^ 124 := by norm_num
  have h2130 : (OfNat.ofNat (2 ^ 130) : Fp) = (2 : Fp) ^ 130 := by norm_num
  rw [h2124] at hLoZ
  rw [h2130] at hS
  refine ⟨hRec, hLoZ, ?_⟩
  -- extract the thirteen 10-bit words of the running-sum chain at concrete indices
  obtain ⟨w0, hw0, he0⟩ := hChain ⟨0, by norm_num⟩
  obtain ⟨w1, hw1, he1⟩ := hChain ⟨1, by norm_num⟩
  obtain ⟨w2, hw2, he2⟩ := hChain ⟨2, by norm_num⟩
  obtain ⟨w3, hw3, he3⟩ := hChain ⟨3, by norm_num⟩
  obtain ⟨w4, hw4, he4⟩ := hChain ⟨4, by norm_num⟩
  obtain ⟨w5, hw5, he5⟩ := hChain ⟨5, by norm_num⟩
  obtain ⟨w6, hw6, he6⟩ := hChain ⟨6, by norm_num⟩
  obtain ⟨w7, hw7, he7⟩ := hChain ⟨7, by norm_num⟩
  obtain ⟨w8, hw8, he8⟩ := hChain ⟨8, by norm_num⟩
  obtain ⟨w9, hw9, he9⟩ := hChain ⟨9, by norm_num⟩
  obtain ⟨w10, hw10, he10⟩ := hChain ⟨10, by norm_num⟩
  obtain ⟨w11, hw11, he11⟩ := hChain ⟨11, by norm_num⟩
  obtain ⟨w12, hw12, he12⟩ := hChain ⟨12, by norm_num⟩
  clear hChain
  norm_num [Vector.getElem_append, Vector.getElem_mapRange, Expression.eval,
    Orchard.Specs.K] at hS0 hSHiZ hEta he0 he1 he2 he3 he4 he5 he6 he7 he8 he9 he10 he11 he12
  norm_num [Orchard.Specs.K] at hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hw8 hw9 hw10 hw11 hw12
  -- name the final decomposition cell opaquely
  obtain ⟨z13, hz13⟩ := eval_get13 env
    ((#v[var { index := i₀ + 1 }] : Vector (Expression Fp) 1) ++
      (Vector.mapRange 13 fun j => var { index := i₀ + 1 + 1 + j } :
        Vector (Expression Fp) 13))
  rw [hz13] at he12 hSHiZ hEta
  refine ⟨z13,
    w0 + 2 ^ 10 * w1 + 2 ^ 20 * w2 + 2 ^ 30 * w3 + 2 ^ 40 * w4 + 2 ^ 50 * w5 +
      2 ^ 60 * w6 + 2 ^ 70 * w7 + 2 ^ 80 * w8 + 2 ^ 90 * w9 + 2 ^ 100 * w10 +
      2 ^ 110 * w11 + 2 ^ 120 * w12,
    by omega, ?_, hSHiZ, ?_⟩
  · push_cast
    linear_combination -hS - hS0 + he0 + (2 ^ 10 : Fp) * he1 + (2 ^ 20 : Fp) * he2 +
      (2 ^ 30 : Fp) * he3 + (2 ^ 40 : Fp) * he4 + (2 ^ 50 : Fp) * he5 +
      (2 ^ 60 : Fp) * he6 + (2 ^ 70 : Fp) * he7 + (2 ^ 80 : Fp) * he8 +
      (2 ^ 90 : Fp) * he9 + (2 ^ 100 : Fp) * he10 + (2 ^ 110 : Fp) * he11 +
      (2 ^ 120 : Fp) * he12
  · rcases hEta with h | h | h
    · exact Or.inl h
    · refine Or.inr (Or.inl ?_)
      intro hz
      rw [hz, zero_mul] at h
      exact zero_ne_one h
    · exact Or.inr (Or.inr h)

theorem completeness : FormalAssertion.Completeness Fp main (fun _ => True) Spec := by
  circuit_proof_start [main, Spec, Utilities.LookupRangeCheck.CopyCheck.circuit,
    Utilities.LookupRangeCheck.CopyCheck.ProverSpec, Overflow.circuit, Overflow.Spec]
  obtain ⟨hRec, hLoZ, sHi, sLo, hsLo_lt, hkey, hHiZ, hEtaSpec⟩ := h_spec
  obtain ⟨hs_wit, ⟨_, h_values⟩, h_eta⟩ := h_env
  have h2124 : (OfNat.ofNat (2 ^ 124) : Fp) = (2 : Fp) ^ 124 := by norm_num
  have h2130 : (OfNat.ofNat (2 ^ 130) : Fp) = (2 : Fp) ^ 130 := by norm_num
  -- the honest final decomposition cell, and its vanishing when s fits in 130 bits
  have h13 := h_values ⟨13, by norm_num⟩
  norm_num [Orchard.Specs.K] at h13
  have hsmall : sHi = 0 → ZMod.val (env.get i₀) / 2 ^ 130 = 0 := by
    intro h0
    have hval : env.get i₀ = (sLo : Fp) := by
      rw [hs_wit, hkey, h0]
      ring
    rw [hval, ZMod.val_natCast_of_lt
      (lt_trans hsLo_lt (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))]
    exact Nat.div_eq_of_lt hsLo_lt
  refine ⟨by rw [h2130]; exact hs_wit, hRec, ?_, ?_, ?_⟩
  · rcases hLoZ with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      rw [h2124]
      exact h
  · rcases hHiZ with h | h0
    · exact Or.inl h
    · refine Or.inr ?_
      rw [h13, show (1361129467683753853853498429727072845824 : ℕ) = 2 ^ 130 from by
        norm_num, hsmall h0]
      norm_num
  · rcases hEtaSpec with h | hz | h0
    · exact Or.inl h
    · refine Or.inr (Or.inl ?_)
      rw [h_eta, if_neg (by simp [hz])]
      exact mul_inv_cancel₀ hz
    · refine Or.inr (Or.inr ?_)
      rw [h13, show (1361129467683753853853498429727072845824 : ℕ) = 2 ^ 130 from by
        norm_num, hsmall h0]
      norm_num

/-- `overflow.rs::Config::overflow_check`. -/
def circuit : FormalAssertion Fp Input where
  main
  Assumptions _ := True
  Spec
  soundness
  completeness

end OverflowCheck

end Orchard.Ecc.Mul.Overflow
