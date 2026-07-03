import Clean.Gadgets.SHA256.BitwiseOps

section
variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.SHA256

/-!
# 32-bit Bitwise XOR for SHA-256

Per bit: z = a + b − 2·a·b  (correct when a, b ∈ {0, 1}).
Witnesses 32 output bits.
-/

/-- Bitwise XOR of two 32-bit words.
    Per bit: z = a + b − 2·a·b  (correct when a, b ∈ {0, 1}).
    Witnesses 32 output bits. -/
def xor32 (a b : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witnessVector 32 (.lit <| .ofFn fun i => (a[i].val ^^^ b[i].val).toField)
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] - a[i] - b[i] + 2 * a[i] * b[i])
  return z

namespace Xor32

structure Inputs (F : Type) where
  a : fields 32 F
  b : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  xor32 input.a input.b

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = valueBits input.a ^^^ valueBits input.b ∧ Normalized z

/-!
## Helper lemmas for valueBits and bitwise XOR
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

private lemma bool_finsum_xor (n : ℕ) (f g : Fin n → ℕ) (hf : ∀ i, f i = 0 ∨ f i = 1)
    (hg : ∀ i, g i = 0 ∨ g i = 1) :
    (∑ i : Fin n, f i * 2^i.val) ^^^ (∑ i : Fin n, g i * 2^i.val)
    = ∑ i : Fin n, (f i ^^^ g i) * 2^i.val := by
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < n
  · have hfg : ∀ i : Fin n, (f i ^^^ g i) = 0 ∨ (f i ^^^ g i) = 1 := by
      intro i; rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi]
    rw [Nat.testBit_xor, testBit_binary_sum n f hf ⟨j, hj⟩, testBit_binary_sum n g hg ⟨j, hj⟩,
        testBit_binary_sum n _ hfg ⟨j, hj⟩]
    rcases hf ⟨j, hj⟩ with hfi | hfi <;> rcases hg ⟨j, hj⟩ with hgi | hgi <;> simp [hfi, hgi]
  · push_neg at hj
    have pow_le : 2^n ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj
    have hfS := sum_bool_lt_two_pow n f (fun i => by rcases hf i with h|h <;> simp [h])
    have hgS := sum_bool_lt_two_pow n g (fun i => by rcases hg i with h|h <;> simp [h])
    have hfgS := sum_bool_lt_two_pow n (fun i => f i ^^^ g i) (fun i => by
      rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi])
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow hfS hgS) pow_le),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hfgS pow_le)]

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [xor32]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b⟩ := h_input
  have h_ai : ∀ i : Fin 32, Expression.eval env input_var_a[i.val] = input_a[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_a i i.isLt
    simp [Vector.getElem_map] at this; exact this
  have h_bi : ∀ i : Fin 32, Expression.eval env input_var_b[i.val] = input_b[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_b i i.isLt
    simp [Vector.getElem_map] at this; exact this
  -- h_holds: env.get(i₀+i) = a[i] + b[i] - 2*a[i]*b[i]
  have h_eq : ∀ i : Fin 32, env.get (i₀ + i.val) = input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i] := by
    intro i
    have h := h_holds i; rw [h_ai i, h_bi i] at h
    -- h: env.get(i₀+i) + -a[i] + -b[i] + 2*a[i]*b[i] = 0
    have key : env.get (i₀ + i.val) - (input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i]) = 0 := by
      ring_nf; ring_nf at h; exact h
    exact sub_eq_zero.mp key
  have h_z : Vector.map (Expression.eval env) (Vector.mapRange 32 fun i =>
      (var {index := i₀ + i} : Expression (F p)))
      = Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) := by
    ext i; simp [Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  rw [h_z]
  have h_norm : ∀ i : Fin 32, env.get (i₀ + i.val) = 0 ∨ env.get (i₀ + i.val) = 1 := by
    intro i; rw [h_eq i]; exact IsBool.xor_is_bool (ha i) (hb i)
  refine ⟨?_, fun i => ?_⟩
  · simp only [valueBits]
    simp_rw [show ∀ i : Fin 32, (Vector.ofFn fun j : Fin 32 => env.get (i₀ + j.val))[i] =
        env.get (i₀ + i.val) from fun i => by simp [Vector.getElem_ofFn]]
    simp_rw [h_eq, IsBool.xor_eq_val_xor (ha _) (hb _)]
    exact (bool_finsum_xor 32 (fun i => (input_a[i] : F p).val) (fun i => (input_b[i] : F p).val)
      (fun i => by rcases ha i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one])
      (fun i => by rcases hb i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one])).symm
  · have : (Vector.ofFn fun j : Fin 32 => env.get (i₀ + j.val))[i] = env.get (i₀ + i.val) := by
      simp [Vector.getElem_ofFn]
    rw [this]; exact h_norm i

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [xor32]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b⟩ := h_input
  have h_ai : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_a[i.val] = input_a[i] := by
    intro i; have := Vector.ext_iff.mp h_input_a i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_bi : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_b[i.val] = input_b[i] := by
    intro i; have := Vector.ext_iff.mp h_input_b i i.isLt; simp [Vector.getElem_map] at this; exact this
  intro i
  have henv := h_env i
  simp only [circuit_norm] at henv
  rw [h_ai i, h_bi i] at henv
  have hcast : ((input_a[i].val ^^^ input_b[i].val : ℕ) : F p) =
      input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i] := by
    rw [← IsBool.xor_eq_val_xor (ha i) (hb i)]
    have := ZMod.natCast_val (R := ZMod p) (input_a[i] + input_b[i] - 2 * input_a[i] * input_b[i])
    rw [this]; exact ZMod.cast_id p _
  rw [henv, hcast, h_ai i, h_bi i]; ring

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Xor32
end Gadgets.SHA256
end
