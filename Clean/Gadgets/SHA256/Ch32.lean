import Clean.Gadgets.SHA256.BitwiseOps
import Clean.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.SHA256

/-!
# Choice function Ch(e, f, g) for SHA-256

Ch(e, f, g) = (e AND f) XOR (NOT e AND g) = g + e·(f − g).
Per bit: ch = g + e·(f − g), which equals f when e = 1 and g when e = 0.
One R1CS constraint per bit: e·(f − g) = ch − g.
Witnesses 32 output bits.
-/

/-- Choice function: Ch(e, f, g) = (e AND f) XOR (NOT e AND g) = g + e·(f − g).
    Per bit: ch = g + e·(f − g), which equals f when e = 1 and g when e = 0.
    One R1CS constraint per bit: e·(f − g) = ch − g. -/
def ch32 (e f g : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witness (Vector.ofFn fun (i : Fin 32) =>
    Witgen.FExpr.expr (g[i] + e[i] * (f[i] - g[i])))
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] - g[i] - e[i] * (f[i] - g[i]))
  return z

namespace Ch32

structure Inputs (F : Type) where
  e : fields 32 F
  f : fields 32 F
  g : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  ch32 input.e input.f input.g

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.e ∧ Normalized input.f ∧ Normalized input.g

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.Ch (valueBits input.e) (valueBits input.f) (valueBits input.g) ∧
  Normalized z

/-!
## Helper lemmas
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

/-- Per-bit: (g + e*(f-g)).val = (e.val &&& f.val) ^^^ ((e.val ^^^ 1) &&& g.val) for boolean e,f,g. -/
private lemma field_ch_val (ei fi gi : F p)
    (he : ei = 0 ∨ ei = 1) (hf : fi = 0 ∨ fi = 1) (hg : gi = 0 ∨ gi = 1) :
    (gi + ei * (fi - gi) : F p).val =
    (ei.val &&& fi.val) ^^^ ((ei.val ^^^ 1) &&& gi.val) := by
  rcases he with he | he <;> rcases hf with hf | hf <;> rcases hg with hg | hg <;>
    simp [he, hf, hg, ZMod.val_zero, ZMod.val_one]

/-- Ch at Nat finsum level: if z[i] = (e[i] &&& f[i]) ^^^ ((e[i] ^^^ 1) &&& g[i]) for boolean
    bit vectors, then Σ z[i]*2^i = Ch(Σ e[i]*2^i, Σ f[i]*2^i, Σ g[i]*2^i). -/
private lemma ch_finsum_eq (e f g z : Fin 32 → ℕ)
    (he : ∀ i, e i = 0 ∨ e i = 1) (hf : ∀ i, f i = 0 ∨ f i = 1)
    (hg : ∀ i, g i = 0 ∨ g i = 1) (hz : ∀ i, z i = 0 ∨ z i = 1)
    (h_eq : ∀ i : Fin 32, z i = (e i &&& f i) ^^^ ((e i ^^^ 1) &&& g i)) :
    ∑ i : Fin 32, z i * 2^i.val =
    (∑ i : Fin 32, e i * 2^i.val) &&& (∑ i : Fin 32, f i * 2^i.val) ^^^
    ((∑ i : Fin 32, e i * 2^i.val) ^^^ 4294967295) &&&
    (∑ i : Fin 32, g i * 2^i.val) := by
  have h4 : (4294967295 : ℕ) = 2^32 - 1 := by norm_num
  rw [h4]
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < 32
  · rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_xor,
        testBit_binary_sum 32 z hz ⟨j, hj⟩,
        testBit_binary_sum 32 e he ⟨j, hj⟩,
        testBit_binary_sum 32 f hf ⟨j, hj⟩,
        testBit_binary_sum 32 g hg ⟨j, hj⟩,
        Nat.testBit_two_pow_sub_one]
    simp only [hj, decide_true]
    rw [h_eq ⟨j, hj⟩]
    rcases he ⟨j, hj⟩ with hej|hej <;> rcases hf ⟨j, hj⟩ with hfj|hfj <;>
        rcases hg ⟨j, hj⟩ with hgj|hgj <;> simp [hej, hfj, hgj]
  · push_neg at hj
    have pow_le : 2^32 ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj
    have le1 : ∀ x : ℕ, x = 0 ∨ x = 1 → x ≤ 1 := fun x h => by rcases h with h|h <;> simp [h]
    have hzS := sum_bool_lt_two_pow 32 z (fun i => le1 _ (hz i))
    have hfS := sum_bool_lt_two_pow 32 f (fun i => le1 _ (hf i))
    have hgS := sum_bool_lt_two_pow 32 g (fun i => le1 _ (hg i))
    have hChS : (∑ i : Fin 32, e i * 2^i.val) &&& (∑ i : Fin 32, f i * 2^i.val) ^^^
        ((∑ i : Fin 32, e i * 2^i.val) ^^^ (2^32 - 1)) &&&
        (∑ i : Fin 32, g i * 2^i.val) < 2^32 :=
      Nat.xor_lt_two_pow (Nat.and_lt_two_pow _ hfS) (Nat.and_lt_two_pow _ hgS)
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hzS pow_le),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hChS pow_le)]

/-- Spec holds for any vector `z` whose bits satisfy the per-bit constraint. -/
private lemma spec_of_constraint
    (input_e input_f input_g z : fields 32 (F p))
    (he : Normalized input_e) (hf : Normalized input_f) (hg : Normalized input_g)
    (h_eq : ∀ i : Fin 32, z[i] = input_g[i] + input_e[i] * (input_f[i] - input_g[i])) :
    valueBits z = Specs.SHA256.Ch (valueBits input_e) (valueBits input_f) (valueBits input_g) ∧
    Normalized z := by
  have h_norm : ∀ i : Fin 32, z[i] = 0 ∨ z[i] = 1 := by
    intro i; rw [h_eq i]
    rcases he i with he | he <;> rcases hf i with hf | hf <;> rcases hg i with hg | hg <;>
      simp [he, hf, hg]
  have he_val : ∀ i : Fin 32, (input_e[i] : F p).val = 0 ∨ (input_e[i] : F p).val = 1 :=
    fun i => by rcases he i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hf_val : ∀ i : Fin 32, (input_f[i] : F p).val = 0 ∨ (input_f[i] : F p).val = 1 :=
    fun i => by rcases hf i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hg_val : ∀ i : Fin 32, (input_g[i] : F p).val = 0 ∨ (input_g[i] : F p).val = 1 :=
    fun i => by rcases hg i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hz_val : ∀ i : Fin 32, (z[i] : F p).val = 0 ∨ (z[i] : F p).val = 1 :=
    fun i => by rcases h_norm i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_bit_eq : ∀ i : Fin 32, (z[i] : F p).val =
      ((input_e[i] : F p).val &&& (input_f[i] : F p).val) ^^^
        (((input_e[i] : F p).val ^^^ 1) &&& (input_g[i] : F p).val) := by
    intro i; rw [h_eq i]; exact field_ch_val _ _ _ (he i) (hf i) (hg i)
  have Ch_def : ∀ a b c : ℕ, Specs.SHA256.Ch a b c = (a &&& b) ^^^ ((a ^^^ 4294967295) &&& c) := fun _ _ _ => rfl
  have h1 : valueBits z = ∑ i : Fin 32, (z[i] : F p).val * 2^i.val := rfl
  have he_eq : valueBits input_e = ∑ i : Fin 32, (input_e[i] : F p).val * 2^i.val := rfl
  have hf_eq : valueBits input_f = ∑ i : Fin 32, (input_f[i] : F p).val * 2^i.val := rfl
  have hg_eq : valueBits input_g = ∑ i : Fin 32, (input_g[i] : F p).val * 2^i.val := rfl
  have key' := ch_finsum_eq _ _ _ _ he_val hf_val hg_val hz_val h_bit_eq
  refine ⟨?_, h_norm⟩
  rw [Ch_def, he_eq, hf_eq, hg_eq, h1]
  exact key'

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [ch32]
  obtain ⟨he, hf, hg⟩ := h_assumptions
  obtain ⟨h_input_e, h_input_f, h_input_g⟩ := h_input
  have h_ei : ∀ i : Fin 32, Expression.eval env input_var_e[i.val] = input_e[i] := by
    intro i; have := Vector.ext_iff.mp h_input_e i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_fi : ∀ i : Fin 32, Expression.eval env input_var_f[i.val] = input_f[i] := by
    intro i; have := Vector.ext_iff.mp h_input_f i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_gi : ∀ i : Fin 32, Expression.eval env input_var_g[i.val] = input_g[i] := by
    intro i; have := Vector.ext_iff.mp h_input_g i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_eq : ∀ i : Fin 32, env.get (i₀ + i.val) = input_g[i] + input_e[i] * (input_f[i] - input_g[i]) := by
    intro i
    have h := h_holds i; rw [h_ei i, h_fi i, h_gi i] at h
    have key : env.get (i₀ + i.val) - (input_g[i] + input_e[i] * (input_f[i] - input_g[i])) = 0 := by
      ring_nf; ring_nf at h; exact h
    exact sub_eq_zero.mp key
  set z : fields 32 (F p) :=
    Vector.map (Expression.eval env) (Vector.mapRange 32 fun i =>
      (var {index := i₀ + i} : Expression (F p))) with hz_def
  have h_z : ∀ i : Fin 32, z[i] = env.get (i₀ + i.val) := by
    intro i; simp [z, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  have h_eq' : ∀ i : Fin 32, z[i] = input_g[i] + input_e[i] * (input_f[i] - input_g[i]) := by
    intro i; rw [h_z i]; exact h_eq i
  exact spec_of_constraint input_e input_f input_g z he hf hg h_eq'

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [ch32]
  obtain ⟨he, hf, hg⟩ := h_assumptions
  obtain ⟨h_input_e, h_input_f, h_input_g⟩ := h_input
  have h_ei : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_e[i.val] = input_e[i] := by
    intro i; have := Vector.ext_iff.mp h_input_e i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_fi : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_f[i.val] = input_f[i] := by
    intro i; have := Vector.ext_iff.mp h_input_f i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_gi : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_g[i.val] = input_g[i] := by
    intro i; have := Vector.ext_iff.mp h_input_g i i.isLt; simp [Vector.getElem_map] at this; exact this
  intro i
  have henv := h_env i
  simp only [circuit_norm, Vector.getElem_ofFn] at henv
  rw [h_ei i, h_fi i, h_gi i] at henv
  rw [henv, h_gi i, h_ei i, h_fi i]; ring

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end Ch32
end Gadgets.SHA256
end
