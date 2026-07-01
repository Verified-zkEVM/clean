import Clean.Gadgets.SHA256.BitwiseOps

namespace Gadgets.SHA256.And32
variable {p : ℕ} [Fact p.Prime]

/-!
# 32-bit Bitwise AND for SHA-256

Per bit: z = a · b  (correct when a, b ∈ {0, 1}).
Witnesses 32 output bits.
-/

structure Inputs (F : Type) where
  a : fields 32 F
  b : fields 32 F
deriving ProvableStruct

/-- Bitwise AND of two 32-bit words.
    Per bit: z = a · b  (correct when a, b ∈ {0, 1}). -/
def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let { a, b } := input
  let z <== Vector.ofFn fun i => a[i] * b[i]
  return z

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = valueBits input.a &&& valueBits input.b ∧ Normalized z

/-!
## Helper lemmas for valueBits and bitwise AND
-/

private lemma sum_bool_lt_two_pow (n : ℕ) (f : Fin n → ℕ) (hf : ∀ i, f i ≤ 1) :
    ∑ i : Fin n, f i * 2^i.val < 2^n := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
    have ihm : ∑ i : Fin m, f (Fin.castSucc i) * 2 ^ i.val < 2 ^ m :=
      ih (f ∘ Fin.castSucc) (fun i => hf _)
    have hfm : f (Fin.last m) ≤ 1 := hf _
    have hfm_bound : f (Fin.last m) * 2 ^ m ≤ 2 ^ m := by nlinarith [Nat.two_pow_pos m]
    have h2 : 2^m + 2^m = 2^(m+1) := by ring
    omega

private lemma testBit_binary_sum (n : ℕ) (f : Fin n → ℕ) (hf : ∀ i, f i = 0 ∨ f i = 1) (k : Fin n) :
    Nat.testBit (∑ i : Fin n, f i * 2^i.val) k.val = decide (f k = 1) := by
  induction n with
  | zero => exact k.elim0
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last]
    set S := ∑ i : Fin m, f (Fin.castSucc i) * 2 ^ i.val
    set fm := f (Fin.last m)
    have hS : S < 2 ^ m := sum_bool_lt_two_pow m (f ∘ Fin.castSucc) (fun i => by
      rcases hf (Fin.castSucc i) with h | h <;> simp [h])
    rw [show S + fm * 2^m = 2^m * fm + S from by ring, Nat.testBit_two_pow_mul_add _ hS]
    by_cases hk : k.val < m
    · simp only [hk, ite_true]
      have ih' := ih (f ∘ Fin.castSucc) (fun i => hf _) ⟨k.val, hk⟩
      simp only [Function.comp] at ih'; rw [ih']; congr 1
    · push_neg at hk
      have hkeq : k.val = m := Nat.le_antisymm (Nat.lt_succ_iff.mp k.isLt) hk
      simp only [hkeq, lt_irrefl, ite_false, Nat.sub_self]
      have hklast : k = Fin.last m := Fin.ext hkeq; subst hklast
      rcases hf (Fin.last m) with h | h <;> simp [h, fm]

private lemma bool_finsum_and (n : ℕ) (f g : Fin n → ℕ) (hf : ∀ i, f i = 0 ∨ f i = 1)
    (hg : ∀ i, g i = 0 ∨ g i = 1) :
    (∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, g i * 2^i.val)
    = ∑ i : Fin n, (f i &&& g i) * 2^i.val := by
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < n
  · have hfg : ∀ i : Fin n, (f i &&& g i) = 0 ∨ (f i &&& g i) = 1 := by
      intro i; rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi]
    rw [Nat.testBit_and, testBit_binary_sum n f hf ⟨j, hj⟩, testBit_binary_sum n g hg ⟨j, hj⟩,
        testBit_binary_sum n _ hfg ⟨j, hj⟩]
    rcases hf ⟨j, hj⟩ with hfi | hfi <;> rcases hg ⟨j, hj⟩ with hgi | hgi <;> simp [hfi, hgi]
  · push_neg at hj
    have pow_le : 2^n ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj
    have hgS := sum_bool_lt_two_pow n g (fun i => by rcases hg i with h|h <;> simp [h])
    have hfgS := sum_bool_lt_two_pow n (fun i => f i &&& g i) (fun i => by
      rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi])
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (Nat.and_lt_two_pow _ hgS) pow_le),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hfgS pow_le)]

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start
  rw [h_holds]; clear h_holds
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b⟩ := h_input
  simp_rw [Vector.ext_iff, Vector.getElem_map] at h_input_a h_input_b
  have h : Vector.map (Expression.eval env) (.ofFn fun i => input_var_a[i.val] * input_var_b[i.val])
      = .ofFn fun i => input_a[i.val] * input_b[i.val] := by
    simp [Vector.ext_iff, circuit_norm, h_input_a, h_input_b]
  rw [h]
  simp_all only [Normalized, valueBits, Fin.getElem_fin, Vector.getElem_ofFn]
  constructor; swap
  · intro i
    specialize ha i; specialize hb i
    grind
  simp_rw [IsBool.and_eq_val_and (ha _) (hb _)]
  apply (bool_finsum_and 32 (fun i => (input_a[i] : F p).val) (fun i => (input_b[i] : F p).val)
    (fun i => by rcases ha i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one])
    (fun i => by rcases hb i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one])).symm

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start
  simp_all [circuit_norm, Vector.ext_iff]
  grind

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Gadgets.SHA256.And32
