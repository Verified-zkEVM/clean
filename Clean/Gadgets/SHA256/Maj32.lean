import Clean.Gadgets.SHA256.BitwiseOps
import Clean.Gadgets.SHA256.CarrySave
import Clean.Specs.SHA256
import Mathlib.Tactic.LinearCombination

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Gadgets.SHA256

/-!
# Majority function Maj(a, b, c) for SHA-256

Maj(a, b, c) = (a AND b) XOR (a AND c) XOR (b AND c) = maj(a, b, c) bit-wise.

Carry-save arithmetization: witness one bit `q[i]` per position and impose

  (1)  q[i] · (q[i] − 1) = 0
  (2)  (a[i] + b[i] + c[i] − 2·q[i]) · (a[i] + b[i] + c[i] − 2·q[i] − 1) = 0.

By the full-adder identity these two boolean constraints pin `q[i] = maj(a[i], b[i], c[i])`
(`carry_eq_maj`).  Witnesses 32 variables (the majority output), down from 64.
-/

/-- Majority function via carry save: `q[i] = maj(a[i], b[i], c[i])` is the carry bit of the
    3-bit sum `a[i] + b[i] + c[i]`.  See `Gadgets.SHA256.carrySave`. -/
def maj3 (a b c : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  carrySave a b c

namespace Maj32

structure Inputs (F : Type) where
  a : fields 32 F
  b : fields 32 F
  c : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  maj3 input.a input.b input.c

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) where
  main := main
  localLength _ := 32
  output _ i0 := varFromOffset (fields 32) i0
  localLength_eq _ _ := by simp [circuit_norm, main, maj3, carrySave]
  output_eq _ _ := by dsimp only [main, maj3, carrySave, circuit_norm]
  subcircuitsConsistent _ _ := by simp +arith [circuit_norm, main, maj3, carrySave]
  channelsLawful := by intro x n; simp [circuit_norm, main, maj3, carrySave]

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.a ∧ Normalized input.b ∧ Normalized input.c

def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.Maj (valueBits input.a) (valueBits input.b) (valueBits input.c) ∧
  Normalized z

/-!
## Helper lemmas for valueBits and bitwise Maj
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

/-- For boolean field elements a, b, c: the field expression t + c*(a+b-2t) where t=a*b
    has val equal to the bitwise Nat majority of a.val, b.val, c.val -/
private lemma maj_eq_val_maj {p : ℕ} [Fact p.Prime]
    {a b c : F p} (ha : IsBool a) (hb : IsBool b) (hc : IsBool c) :
    (a * b + c * (a + b - 2 * (a * b))).val = (a.val &&& b.val) ^^^ (a.val &&& c.val) ^^^ (b.val &&& c.val) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
    norm_num [ha, hb, hc, ZMod.val_zero, ZMod.val_one]

private lemma bool_finsum_maj (n : ℕ) (f g k : Fin n → ℕ)
    (hf : ∀ i, f i = 0 ∨ f i = 1) (hg : ∀ i, g i = 0 ∨ g i = 1) (hk : ∀ i, k i = 0 ∨ k i = 1) :
    ((∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, g i * 2^i.val)) ^^^
    ((∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, k i * 2^i.val)) ^^^
    ((∑ i : Fin n, g i * 2^i.val) &&& (∑ i : Fin n, k i * 2^i.val))
    = ∑ i : Fin n, ((f i &&& g i) ^^^ (f i &&& k i) ^^^ (g i &&& k i)) * 2^i.val := by
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < n
  · have hfg : ∀ i : Fin n, (f i &&& g i) = 0 ∨ (f i &&& g i) = 1 := fun i => by
      rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi]
    have hfk : ∀ i : Fin n, (f i &&& k i) = 0 ∨ (f i &&& k i) = 1 := fun i => by
      rcases hf i with hfi | hfi <;> rcases hk i with hki | hki <;> simp [hfi, hki]
    have hgk : ∀ i : Fin n, (g i &&& k i) = 0 ∨ (g i &&& k i) = 1 := fun i => by
      rcases hg i with hgi | hgi <;> rcases hk i with hki | hki <;> simp [hgi, hki]
    have hmaj : ∀ i : Fin n, (f i &&& g i) ^^^ (f i &&& k i) ^^^ (g i &&& k i) = 0 ∨
        (f i &&& g i) ^^^ (f i &&& k i) ^^^ (g i &&& k i) = 1 := fun i => by
      rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> rcases hk i with hki | hki <;>
        simp [hfi, hgi, hki]
    rw [Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_and,
        testBit_binary_sum n f hf ⟨j, hj⟩, testBit_binary_sum n g hg ⟨j, hj⟩,
        testBit_binary_sum n k hk ⟨j, hj⟩,
        testBit_binary_sum n _ hmaj ⟨j, hj⟩]
    rcases hf ⟨j, hj⟩ with hfi | hfi <;> rcases hg ⟨j, hj⟩ with hgi | hgi <;>
      rcases hk ⟨j, hj⟩ with hki | hki <;> simp [hfi, hgi, hki]
  · push_neg at hj
    have pow_le : 2^n ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj
    have hfS := sum_bool_lt_two_pow n f (fun i => by rcases hf i with hx | hx <;> simp [hx])
    have hgS := sum_bool_lt_two_pow n g (fun i => by rcases hg i with hx | hx <;> simp [hx])
    have hkS := sum_bool_lt_two_pow n k (fun i => by rcases hk i with hx | hx <;> simp [hx])
    have hmajS := sum_bool_lt_two_pow n (fun i => (f i &&& g i) ^^^ (f i &&& k i) ^^^ (g i &&& k i))
        (fun i => by
          have hfi := hf i; have hgi := hg i; have hki := hk i
          rcases hfi with hfi | hfi <;> rcases hgi with hgi | hgi <;> rcases hki with hki | hki <;>
            simp [hfi, hgi, hki])
    have hand1 : (∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, g i * 2^i.val) < 2^n :=
      Nat.lt_of_le_of_lt Nat.and_le_left hfS
    have hand2 : (∑ i : Fin n, f i * 2^i.val) &&& (∑ i : Fin n, k i * 2^i.val) < 2^n :=
      Nat.lt_of_le_of_lt Nat.and_le_left hfS
    have hand3 : (∑ i : Fin n, g i * 2^i.val) &&& (∑ i : Fin n, k i * 2^i.val) < 2^n :=
      Nat.lt_of_le_of_lt Nat.and_le_left hgS
    have hxor12 := Nat.xor_lt_two_pow hand1 hand2
    have hxor_all := Nat.xor_lt_two_pow hxor12 hand3
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hxor_all pow_le),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hmajS pow_le)]

omit [Fact (p > 2^35)] in
/-- Spec holds for any vector `z` whose bits satisfy the per-bit constraint. -/
private lemma spec_of_constraint
    (input_a input_b input_c z : fields 32 (F p))
    (ha : Normalized input_a) (hb : Normalized input_b) (hc : Normalized input_c)
    (h_eq : ∀ i : Fin 32, z[i] =
      input_a[i] * input_b[i] + input_c[i] * (input_a[i] + input_b[i] - 2 * (input_a[i] * input_b[i]))) :
    valueBits z = Specs.SHA256.Maj (valueBits input_a) (valueBits input_b) (valueBits input_c) ∧
    Normalized z := by
  have ha_b : ∀ i : Fin 32, IsBool input_a[i] := fun i => ha i
  have hb_b : ∀ i : Fin 32, IsBool input_b[i] := fun i => hb i
  have hc_b : ∀ i : Fin 32, IsBool input_c[i] := fun i => hc i
  have h_norm : ∀ i : Fin 32, z[i] = 0 ∨ z[i] = 1 := by
    intro i; rw [h_eq i]; exact maj_is_bool (ha_b i) (hb_b i) (hc_b i)
  have ha_val : ∀ i : Fin 32, (input_a[i] : F p).val = 0 ∨ (input_a[i] : F p).val = 1 :=
    fun i => by rcases ha i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hb_val : ∀ i : Fin 32, (input_b[i] : F p).val = 0 ∨ (input_b[i] : F p).val = 1 :=
    fun i => by rcases hb i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have hc_val : ∀ i : Fin 32, (input_c[i] : F p).val = 0 ∨ (input_c[i] : F p).val = 1 :=
    fun i => by rcases hc i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_bit_eq : ∀ i : Fin 32, (z[i] : F p).val =
      ((input_a[i] : F p).val &&& (input_b[i] : F p).val) ^^^
      ((input_a[i] : F p).val &&& (input_c[i] : F p).val) ^^^
      ((input_b[i] : F p).val &&& (input_c[i] : F p).val) := by
    intro i; rw [h_eq i]; exact maj_eq_val_maj (ha_b i) (hb_b i) (hc_b i)
  have key' : ((∑ i : Fin 32, (input_a[i] : F p).val * 2^i.val) &&&
      (∑ i : Fin 32, (input_b[i] : F p).val * 2^i.val)) ^^^
      ((∑ i : Fin 32, (input_a[i] : F p).val * 2^i.val) &&&
      (∑ i : Fin 32, (input_c[i] : F p).val * 2^i.val)) ^^^
      ((∑ i : Fin 32, (input_b[i] : F p).val * 2^i.val) &&&
      (∑ i : Fin 32, (input_c[i] : F p).val * 2^i.val)) =
      ∑ i : Fin 32, (z[i] : F p).val * 2^i.val := by
    rw [bool_finsum_maj 32 _ _ _ ha_val hb_val hc_val]
    apply Finset.sum_congr rfl
    intro i _
    rw [h_bit_eq i]
  have Maj_def : ∀ a b c : ℕ, Specs.SHA256.Maj a b c = (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c) :=
    fun _ _ _ => rfl
  have h_z_eq : valueBits z = ∑ i : Fin 32, (z[i] : F p).val * 2^i.val := rfl
  have ha_eq : valueBits input_a = ∑ i : Fin 32, (input_a[i] : F p).val * 2^i.val := rfl
  have hb_eq : valueBits input_b = ∑ i : Fin 32, (input_b[i] : F p).val * 2^i.val := rfl
  have hc_eq : valueBits input_c = ∑ i : Fin 32, (input_c[i] : F p).val * 2^i.val := rfl
  refine ⟨?_, h_norm⟩
  rw [Maj_def, ha_eq, hb_eq, hc_eq, h_z_eq]
  exact key'.symm

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [maj3, carrySave]
  obtain ⟨ha, hb, hc⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_c⟩ := h_input
  have h_ai : ∀ i : Fin 32, Expression.eval env input_var_a[i.val] = input_a[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_a i i.isLt
    simp [Vector.getElem_map] at this; exact this
  have h_bi : ∀ i : Fin 32, Expression.eval env input_var_b[i.val] = input_b[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_b i i.isLt
    simp [Vector.getElem_map] at this; exact this
  have h_ci : ∀ i : Fin 32, Expression.eval env input_var_c[i.val] = input_c[i] := by
    intro i
    have := Vector.ext_iff.mp h_input_c i i.isLt
    simp [Vector.getElem_map] at this; exact this
  -- Extract the two boolean constraints from h_holds.
  obtain ⟨h_q_bool, h_out_bool⟩ := h_holds
  set z : fields 32 (F p) :=
    Vector.map (Expression.eval env) (Vector.mapRange 32 fun i =>
      (var {index := i₀ + i} : Expression (F p))) with hz_def
  have h_z_get : ∀ i : Fin 32, z[i] = env.get (i₀ + i.val) := by
    intro i; simp [z, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  -- q[i] is boolean.
  have hq_bool : ∀ i : Fin 32, IsBool z[i] := by
    intro i; rw [h_z_get i, IsBool.iff_mul_sub_one]
    have h := h_q_bool i; linear_combination h
  -- The parity a[i]+b[i]+c[i]-2·q[i] is boolean.
  have hout_bool : ∀ i : Fin 32,
      IsBool (input_a[i] + input_b[i] + input_c[i] - 2 * z[i]) := by
    intro i; rw [h_z_get i, IsBool.iff_mul_sub_one]
    have h := h_out_bool i; rw [h_ai i, h_bi i, h_ci i] at h; linear_combination h
  -- Bridge: the carry equals the majority expression.
  have h_eq' : ∀ i : Fin 32, z[i] =
      input_a[i] * input_b[i] + input_c[i] * (input_a[i] + input_b[i] - 2 * (input_a[i] * input_b[i])) :=
    fun i => carry_eq_maj (ha i) (hb i) (hc i) (hq_bool i) (hout_bool i)
  exact spec_of_constraint input_a input_b input_c z ha hb hc h_eq'

omit [Fact (p > 2^35)] in
theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [maj3, carrySave]
  obtain ⟨ha, hb, hc⟩ := h_assumptions
  obtain ⟨h_input_a, h_input_b, h_input_c⟩ := h_input
  have h_ai : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_a[i.val] = input_a[i] := by
    intro i; have := Vector.ext_iff.mp h_input_a i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_bi : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_b[i.val] = input_b[i] := by
    intro i; have := Vector.ext_iff.mp h_input_b i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_ci : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_c[i.val] = input_c[i] := by
    intro i; have := Vector.ext_iff.mp h_input_c i i.isLt; simp [Vector.getElem_map] at this; exact this
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hq := (h_env.1) i
    simp only [Vector.getElem_ofFn] at hq
    rw [hq, h_ai i, h_bi i, h_ci i]
    have hbool := maj_is_bool (ha i) (hb i) (hc i)
    rw [IsBool.iff_mul_sub_one] at hbool; linear_combination hbool
  · have hq := (h_env.1) i
    simp only [Vector.getElem_ofFn] at hq
    rw [hq, h_ai i, h_bi i, h_ci i]
    have hbool := parity_is_bool (ha i) (hb i) (hc i)
    rw [IsBool.iff_mul_sub_one] at hbool; linear_combination hbool

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  Assumptions := Assumptions; Spec := Spec
  soundness := soundness; completeness := completeness

end Maj32
end Gadgets.SHA256
end
