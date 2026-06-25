import Clean.Gadgets.SHA256.Xor32
import Clean.Specs.SHA256
import Clean.Utils.Rotation
import Clean.Utils.Bits
import Clean.Utils.Fin

section
variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.SHA256

/-!
# σ₀ (lower sigma 0) for SHA-256

σ₀(x) = ROTR7(x) XOR ROTR18(x) XOR SHR3(x)

Two xor32 calls = 64 witnesses total.
-/

/-- σ₀(x) = ROTR7(x) XOR ROTR18(x) XOR SHR3(x) -/
def lowerSigma0 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let r1 ← xor32 (rotr32 7  x) (rotr32 18 x)
  xor32 r1 (shr32 3 x)

namespace LowerSigma0

-- TODO: This circuit is written BADLY: it hides `main` behind `lowerSigma0`
-- and inlines `xor32` instead of calling `Xor32.circuit` as a subcircuit.
def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  lowerSigma0 x

def Assumptions (x : fields 32 (F p)) : Prop := Normalized x

def Spec (x : fields 32 (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.lowerSigma0 (valueBits x) ∧ Normalized z

/-! ## Helper lemmas (adapted from Xor32) -/

lemma sum_bool_lt_two_pow (n : ℕ) (f : Fin n → ℕ) (hf : ∀ i, f i ≤ 1) :
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

lemma testBit_binary_sum (n : ℕ) (f : Fin n → ℕ) (hf : ∀ i, f i = 0 ∨ f i = 1) (k : Fin n) :
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

lemma bool_finsum_xor_eq (n : ℕ) (f g : Fin n → ℕ) (hf : ∀ i, f i = 0 ∨ f i = 1)
    (hg : ∀ i, g i = 0 ∨ g i = 1) :
    ∑ i : Fin n, (f i ^^^ g i) * 2^i.val
    = (∑ i : Fin n, f i * 2^i.val) ^^^ (∑ i : Fin n, g i * 2^i.val) := by
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < n
  · have hfg : ∀ i : Fin n, (f i ^^^ g i) = 0 ∨ (f i ^^^ g i) = 1 := by
      intro i; rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi]
    rw [testBit_binary_sum n _ hfg ⟨j, hj⟩, Nat.testBit_xor,
        testBit_binary_sum n f hf ⟨j, hj⟩, testBit_binary_sum n g hg ⟨j, hj⟩]
    rcases hf ⟨j, hj⟩ with hfi | hfi <;> rcases hg ⟨j, hj⟩ with hgi | hgi <;> simp [hfi, hgi]
  · push_neg at hj
    have pow_le : 2^n ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj
    have hfS := sum_bool_lt_two_pow n f (fun i => by rcases hf i with h|h <;> simp [h])
    have hgS := sum_bool_lt_two_pow n g (fun i => by rcases hg i with h|h <;> simp [h])
    have hfgS := sum_bool_lt_two_pow n (fun i => f i ^^^ g i) (fun i => by
      rcases hf i with hfi | hfi <;> rcases hg i with hgi | hgi <;> simp [hfi, hgi])
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hfgS pow_le),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (Nat.xor_lt_two_pow hfS hgS) pow_le)]

/-- valueBits of a normalized vector is < 2^32 -/
lemma valueBits_lt_two_pow (x : fields 32 (F p)) (hx : Normalized x) :
    valueBits x < 2^32 :=
  sum_bool_lt_two_pow 32 (fun i => (x[i] : F p).val) (fun i => by
    show (x[i] : F p).val ≤ 1
    rcases hx i with h | h
    · rw [h, ZMod.val_zero]; exact Nat.zero_le _
    · rw [h, ZMod.val_one])

/-- Modular reduction of a boolean-weighted sum equals the sum of its lower `j` terms. -/
lemma sum_mod_two_pow (j : ℕ) {n : ℕ} (f : Fin n → ℕ)
    (hf : ∀ i, f i = 0 ∨ f i = 1) :
    (∑ i : Fin n, f i * 2^i.val) % 2^j =
    ∑ i : Fin n, (if i.val < j then f i else 0) * 2^i.val := by
  have hg_bool : ∀ i : Fin n, (if i.val < j then f i else 0) = 0 ∨
      (if i.val < j then f i else 0) = 1 := by
    intro i; split
    · exact hf i
    · left; rfl
  apply Nat.eq_of_testBit_eq
  intro k
  rw [Nat.testBit_mod_two_pow]
  by_cases hk : k < n
  · rw [testBit_binary_sum n f hf ⟨k, hk⟩,
        testBit_binary_sum n (fun i => if i.val < j then f i else 0) hg_bool ⟨k, hk⟩]
    by_cases hkj : k < j <;> simp [hkj]
  · push_neg at hk
    have pow_le : 2^n ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
    have hsum_lt : (∑ i : Fin n, f i * 2^i.val) < 2^n :=
      sum_bool_lt_two_pow n f (fun i => by rcases hf i with h | h <;> simp [h])
    have hgsum_lt : (∑ i : Fin n, (if i.val < j then f i else 0) * 2^i.val) < 2^n :=
      sum_bool_lt_two_pow n _ (fun i => by rcases hg_bool i with h | h <;> simp [h])
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hsum_lt pow_le),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hgsum_lt pow_le)]
    simp

/-! ## valueBits identities for rotr32 / shr32 (at vector level) -/
omit [Fact (Nat.Prime p)] in
lemma valueBits_eq_fromBits (x : fields 32 (F p)) :
    valueBits x = Utils.Bits.fromBits (x.map ZMod.val) := by
  simp only [valueBits, Utils.Bits.fromBits, Fin.foldl_to_sum]
  congr 1; ext (i : Fin 32); rw [Vector.getElem_map]; rfl

/-- `valueBits` of a rotated bit-vector equals `rotRight32` of the original `valueBits`. -/
lemma valueBits_rotate (x : fields 32 (F p)) (hx : Normalized x) (k : ℕ) :
    valueBits (x.rotate k) = rotRight32 (valueBits x) k := by
  set bits : Vector ℕ 32 := x.map ZMod.val with hbits_def
  have hbits_bool : ∀ (i : ℕ) (hi : i < 32), bits[i] = 0 ∨ bits[i] = 1 := by
    intro i hi
    have h_eq : bits[i] = ZMod.val (x[i]'hi) := by
      show (Vector.map ZMod.val x)[i] = _
      rw [Vector.getElem_map]; rfl
    rw [h_eq]
    have h := hx ⟨i, hi⟩
    rcases h with h | h
    · left; rw [show x[i]'hi = (0 : F p) from h, ZMod.val_zero]
    · right; rw [show x[i]'hi = (1 : F p) from h, ZMod.val_one]
  have hbits_lt : Utils.Bits.fromBits bits < 2^32 := Utils.Bits.fromBits_lt bits hbits_bool
  -- LHS = fromBits (bits.rotate k)
  have hLHS : valueBits (x.rotate k) = Utils.Bits.fromBits (bits.rotate k) := by
    rw [valueBits_eq_fromBits]
    congr 1
    ext i hi
    simp only [Vector.getElem_map, Vector.getElem_rotate, bits]
  rw [hLHS, valueBits_eq_fromBits x]
  -- Goal: fromBits (bits.rotate k) = rotRight32 (fromBits bits) k
  have hrot_lt : rotRight32 (Utils.Bits.fromBits bits) k < 2^32 :=
    Utils.Rotation.rotRight32_lt _ _ hbits_lt
  have hrot_bits_bool : ∀ (i : ℕ) (hi : i < 32),
      (bits.rotate k)[i] = 0 ∨ (bits.rotate k)[i] = 1 := by
    intro i hi; rw [Vector.getElem_rotate]
    exact hbits_bool _ (Nat.mod_lt _ (by norm_num))
  apply Utils.Bits.toBits_injective 32
  · exact Utils.Bits.fromBits_lt _ hrot_bits_bool
  · exact hrot_lt
  rw [Utils.Bits.toBits_fromBits _ hrot_bits_bool,
      Utils.Rotation.rotRight32_toBits _ _ hbits_lt,
      Utils.Bits.toBits_fromBits bits hbits_bool]

/-- Sum form: `∑ x[(i+k).val].val * 2^i = rotRight32 (valueBits x) k.val`. -/
lemma valueBits_rotr32_eq (k : Fin 32) (x : fields 32 (F p)) (hx : Normalized x) :
    ∑ i : Fin 32, (x[(i + k).val] : F p).val * 2^i.val = rotRight32 (valueBits x) k.val := by
  rw [← valueBits_rotate x hx k.val]
  -- LHS sum = valueBits (x.rotate k.val) by definition (modulo Fin add ↔ Nat mod)
  show ∑ i : Fin 32, (x[(i + k).val] : F p).val * 2^i.val =
       ∑ i : Fin 32, ((x.rotate k.val)[i.val] : F p).val * 2^i.val
  apply Finset.sum_congr rfl
  intro i _
  rw [Vector.getElem_rotate]
  congr 2

/-! ## eval helpers for rotr32 / shr32 -/

lemma eval_rotr32 (env : Environment (F p)) (input_var : fields 32 (Expression (F p)))
    (input : fields 32 (F p)) (h_input : Vector.map (Expression.eval env) input_var = input)
    (k : Fin 32) (i : Fin 32) :
    Expression.eval env (rotr32 k input_var)[i.val] = input[(i + k).val] := by
  unfold rotr32
  rw [Vector.getElem_rotate]
  subst h_input
  rw [Vector.getElem_map]
  congr 1

lemma valueBits_shr32_eq (k : Fin 32) (x : fields 32 (F p)) (hx : Normalized x) :
    ∑ i : Fin 32,
      ((if h : i.val + k.val < 32 then (x[i.val + k.val]'h : F p) else 0) : F p).val * 2^i.val
    = valueBits x / 2^k.val := by
  have hbool : ∀ i : Fin 32, (x[i] : F p).val = 0 ∨ (x[i] : F p).val = 1 :=
    fun i => by rcases hx i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have f_bool : ∀ i : Fin 32,
      ((if h : i.val + k.val < 32 then (x[i.val + k.val]'h : F p) else 0) : F p).val = 0 ∨
      ((if h : i.val + k.val < 32 then (x[i.val + k.val]'h : F p) else 0) : F p).val = 1 := by
    intro i; split
    · next h => exact hbool ⟨i.val + k.val, h⟩
    · simp [ZMod.val_zero]
  apply Nat.eq_of_testBit_eq; intro j
  by_cases hj : j < 32
  · rw [testBit_binary_sum 32 _ f_bool ⟨j, hj⟩, Nat.testBit_div_two_pow]
    by_cases hjk : j + k.val < 32
    · simp only [hjk, dite_true]
      rw [show valueBits x = ∑ i : Fin 32, (x[i] : F p).val * 2^i.val from rfl,
          testBit_binary_sum 32 _ hbool ⟨j + k.val, hjk⟩]
      simp only [decide_eq_decide]
      constructor <;> intro h <;> convert h using 2
    · simp only [hjk, dite_false, ZMod.val_zero]
      have hval_lt : valueBits x < 2^32 := valueBits_lt_two_pow x hx
      have : valueBits x < 2 ^ (j + k.val) :=
        lt_of_lt_of_le hval_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
      simp [Nat.testBit_eq_false_of_lt this]
  · push_neg at hj
    have pow_le : 2^32 ≤ 2^j := Nat.pow_le_pow_right (by norm_num) hj
    have hval_lt : valueBits x < 2^32 := valueBits_lt_two_pow x hx
    have lhs_lt : ∑ i : Fin 32,
        ((if h : i.val + k.val < 32 then (x[i.val + k.val]'h : F p) else 0) : F p).val * 2^i.val
        < 2^32 := by
      apply sum_bool_lt_two_pow
      intro i; rcases f_bool i with h | h <;> simp [h]
    rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le lhs_lt pow_le),
        Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le
          (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hval_lt) pow_le)]

lemma eval_shr32 (env : Environment (F p)) (input_var : fields 32 (Expression (F p)))
    (input : fields 32 (F p)) (h_input : Vector.map (Expression.eval env) input_var = input)
    (k : Fin 32) (i : Fin 32) :
    Expression.eval env (shr32 k input_var)[i.val] =
      if h : i.val + k.val < 32 then input[i.val + k.val]'h else 0 := by
  unfold shr32; rw [Vector.getElem_ofFn]; subst h_input
  split
  · next h => rw [Vector.getElem_map]
  · rfl

lemma shr_isbool (k : ℕ) (input : fields 32 (F p)) (ha : Normalized input) (i : Fin 32) :
    (if h : i.val + k < 32 then input[i.val + k]'h else (0 : F p)) = 0 ∨
    (if h : i.val + k < 32 then input[i.val + k]'h else (0 : F p)) = 1 := by
  split
  · next h => exact ha ⟨i.val + k, h⟩
  · left; rfl

/-! ## Spec proof factored out to avoid kernel deep recursion -/

private lemma spec_of_constraint
    (input z : fields 32 (F p))
    (hx : Normalized input)
    (h_z : ∀ i : Fin 32, z[i] =
      (input[(i + 7).val] + input[(i + 18).val] -
        2 * input[(i + 7).val] * input[(i + 18).val])
      + (if h : i.val + 3 < 32 then input[i.val + 3]'h else 0)
      - 2 * (input[(i + 7).val] + input[(i + 18).val] -
              2 * input[(i + 7).val] * input[(i + 18).val])
            * (if h : i.val + 3 < 32 then input[i.val + 3]'h else 0)) :
    valueBits z = Specs.SHA256.lowerSigma0 (valueBits input) ∧ Normalized z := by
  have ha_val : ∀ i : Fin 32, (input[i] : F p).val = 0 ∨ (input[i] : F p).val = 1 :=
    fun i => by rcases hx i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  -- intermediate r7[i] XOR r18[i] is boolean
  have h_r17_isbool : ∀ i : Fin 32,
      input[(i + 7).val] + input[(i + 18).val] -
        2 * input[(i + 7).val] * input[(i + 18).val] = 0 ∨
      input[(i + 7).val] + input[(i + 18).val] -
        2 * input[(i + 7).val] * input[(i + 18).val] = 1 :=
    fun i => IsBool.xor_is_bool (hx _) (hx _)
  -- shr3 element is boolean
  have h_s3_isbool : ∀ i : Fin 32,
      (if h : i.val + 3 < 32 then input[i.val + 3]'h else (0 : F p)) = 0 ∨
      (if h : i.val + 3 < 32 then input[i.val + 3]'h else (0 : F p)) = 1 :=
    fun i => shr_isbool 3 input hx i
  -- z[i] is boolean
  have h_z_isbool : ∀ i : Fin 32, z[i] = 0 ∨ z[i] = 1 := fun i => by
    rw [h_z i]; exact IsBool.xor_is_bool (h_r17_isbool i) (h_s3_isbool i)
  have h_z_val : ∀ i : Fin 32, (z[i] : F p).val = 0 ∨ (z[i] : F p).val = 1 :=
    fun i => by rcases h_z_isbool i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_r17_val : ∀ i : Fin 32,
      ((input[(i + 7).val] + input[(i + 18).val] -
        2 * input[(i + 7).val] * input[(i + 18).val] : F p)).val = 0 ∨
      ((input[(i + 7).val] + input[(i + 18).val] -
        2 * input[(i + 7).val] * input[(i + 18).val] : F p)).val = 1 :=
    fun i => by rcases h_r17_isbool i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  have h_s3_val : ∀ i : Fin 32,
      ((if h : i.val + 3 < 32 then (input[i.val + 3]'h : F p) else 0) : F p).val = 0 ∨
      ((if h : i.val + 3 < 32 then (input[i.val + 3]'h : F p) else 0) : F p).val = 1 :=
    fun i => by rcases h_s3_isbool i with h | h <;> simp [h, ZMod.val_zero, ZMod.val_one]
  -- z[i].val = (r7[i] XOR r18[i]) XOR s3[i] (at val level)
  have h_z_xor_val : ∀ i : Fin 32, (z[i] : F p).val =
      (input[(i + 7).val] + input[(i + 18).val] -
        2 * input[(i + 7).val] * input[(i + 18).val] : F p).val ^^^
      ((if h : i.val + 3 < 32 then (input[i.val + 3]'h : F p) else 0) : F p).val :=
    fun i => by rw [h_z i]; exact IsBool.xor_eq_val_xor (h_r17_isbool i) (h_s3_isbool i)
  have h_r17_xor_val : ∀ i : Fin 32,
      (input[(i + 7).val] + input[(i + 18).val] -
        2 * input[(i + 7).val] * input[(i + 18).val] : F p).val =
      (input[(i + 7).val] : F p).val ^^^ (input[(i + 18).val] : F p).val :=
    fun i => IsBool.xor_eq_val_xor (hx _) (hx _)
  -- Build the sum identity
  have key : ∑ i : Fin 32, (z[i] : F p).val * 2^i.val =
      ((rotRight32 (valueBits input) 7) ^^^ (rotRight32 (valueBits input) 18))
      ^^^ (valueBits input / 2^3) := by
    have step1 : ∑ i : Fin 32, (z[i] : F p).val * 2^i.val =
        ∑ i : Fin 32, ((input[(i + 7).val] + input[(i + 18).val] -
            2 * input[(i + 7).val] * input[(i + 18).val] : F p).val ^^^
          ((if h : i.val + 3 < 32 then (input[i.val + 3]'h : F p) else 0) : F p).val) * 2^i.val := by
      apply Finset.sum_congr rfl
      intro i _; rw [h_z_xor_val i]
    rw [step1, bool_finsum_xor_eq 32 _ _ h_r17_val h_s3_val]
    have step2 : ∑ i : Fin 32,
        (input[(i + 7).val] + input[(i + 18).val] -
          2 * input[(i + 7).val] * input[(i + 18).val] : F p).val * 2^i.val =
        ∑ i : Fin 32,
          ((input[(i + 7).val] : F p).val ^^^ (input[(i + 18).val] : F p).val) * 2^i.val := by
      apply Finset.sum_congr rfl
      intro i _; rw [h_r17_xor_val i]
    rw [step2, bool_finsum_xor_eq 32
      (fun i : Fin 32 => (input[(i + 7).val] : F p).val)
      (fun i : Fin 32 => (input[(i + 18).val] : F p).val)
      (fun i => ha_val ⟨(i + 7).val, (i + 7).isLt⟩)
      (fun i => ha_val ⟨(i + 18).val, (i + 18).isLt⟩)]
    rw [valueBits_rotr32_eq 7 input hx, valueBits_rotr32_eq 18 input hx]
    show _ ^^^ _ ^^^
      (∑ i : Fin 32, ((if h : i.val + ((3 : Fin 32).val) < 32
        then (input[i.val + ((3 : Fin 32).val)]'h : F p) else 0) : F p).val * 2^i.val) = _
    rw [valueBits_shr32_eq 3 input hx]
    rfl
  -- conclude
  have sigma0_def : ∀ x : ℕ, Specs.SHA256.lowerSigma0 x =
      rotRight32 x 7 ^^^ rotRight32 x 18 ^^^ (x / 2^3) := fun _ => rfl
  have h_z_eq : valueBits z = ∑ i : Fin 32, (z[i] : F p).val * 2^i.val := rfl
  refine ⟨?_, h_z_isbool⟩
  rw [sigma0_def, h_z_eq]
  exact key

/-! ## Soundness / Completeness -/

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [lowerSigma0, xor32]
  obtain ⟨h_holds1, h_holds2⟩ := h_holds
  have ha : ∀ i : Fin 32, input[i] = 0 ∨ input[i] = 1 := h_assumptions
  have h_r7  : ∀ i : Fin 32, Expression.eval env (rotr32 7 input_var)[i.val]  = input[(i + 7).val]  :=
    fun i => eval_rotr32 env input_var input h_input 7 i
  have h_r18 : ∀ i : Fin 32, Expression.eval env (rotr32 18 input_var)[i.val] = input[(i + 18).val] :=
    fun i => eval_rotr32 env input_var input h_input 18 i
  have h_s3  : ∀ i : Fin 32, Expression.eval env (shr32 3 input_var)[i.val] =
      if h : i.val + 3 < 32 then input[i.val + 3]'h else 0 :=
    fun i => eval_shr32 env input_var input h_input 3 i
  -- First xor32 output at i₀+i: r1[i] = r7[i] + r18[i] - 2*r7[i]*r18[i]
  have h_r1 : ∀ i : Fin 32, env.get (i₀ + i.val) =
      input[(i + 7).val] + input[(i + 18).val] -
        2 * input[(i + 7).val] * input[(i + 18).val] := by
    intro i
    have h := h_holds1 i; rw [h_r7 i, h_r18 i] at h
    have key : env.get (i₀ + i.val) -
        (input[(i + 7).val] + input[(i + 18).val] -
          2 * input[(i + 7).val] * input[(i + 18).val]) = 0 := by
      ring_nf; ring_nf at h; exact h
    exact sub_eq_zero.mp key
  -- Second xor32 output at i₀+32+i: z[i] = r1[i] + s3[i] - 2*r1[i]*s3[i]
  have h_z_raw : ∀ i : Fin 32, env.get (i₀ + (32 + 32 * 0) + i.val) =
      env.get (i₀ + i.val) + Expression.eval env (shr32 3 input_var)[i.val] -
      2 * env.get (i₀ + i.val) * Expression.eval env (shr32 3 input_var)[i.val] := by
    intro i
    have h := h_holds2 i
    have key : env.get (i₀ + (32 + 32 * 0) + i.val) -
        (env.get (i₀ + i.val) + Expression.eval env (shr32 3 input_var)[i.val] -
         2 * env.get (i₀ + i.val) * Expression.eval env (shr32 3 input_var)[i.val]) = 0 := by
      ring_nf; ring_nf at h; exact h
    exact sub_eq_zero.mp key
  -- Set z to the output vector
  set z : fields 32 (F p) :=
    Vector.map (Expression.eval env) (Vector.mapRange 32 fun i =>
      (var {index := i₀ + (32 + 32 * 0) + i} : Expression (F p))) with hz_def
  have h_z_get : ∀ i : Fin 32, z[i] = env.get (i₀ + (32 + 32 * 0) + i.val) := by
    intro i; simp [z, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  have h_z : ∀ i : Fin 32, z[i] =
      (input[(i + 7).val] + input[(i + 18).val] -
        2 * input[(i + 7).val] * input[(i + 18).val])
      + (if h : i.val + 3 < 32 then input[i.val + 3]'h else 0)
      - 2 * (input[(i + 7).val] + input[(i + 18).val] -
              2 * input[(i + 7).val] * input[(i + 18).val])
            * (if h : i.val + 3 < 32 then input[i.val + 3]'h else 0) := by
    intro i
    rw [h_z_get i, h_z_raw i, h_r1 i, h_s3 i]
  exact spec_of_constraint input z ha h_z

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [lowerSigma0, xor32]
  obtain ⟨h_env1, h_env2, -⟩ := h_env
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hr7 := eval_rotr32 env.toEnvironment input_var input h_input 7 i
    have hr18 := eval_rotr32 env.toEnvironment input_var input h_input 18 i
    have h1 := h_env1 i
    simp only [Vector.getElem_ofFn] at h1
    rw [h1, hr7, hr18]
    have b7 : input[(i + 7).val] = (0 : F p) ∨ input[(i + 7).val] = 1 := h_assumptions (i + 7)
    have b18 : input[(i + 18).val] = (0 : F p) ∨ input[(i + 18).val] = 1 := h_assumptions (i + 18)
    have hc : ((input[(i + 7).val].val ^^^ input[(i + 18).val].val : ℕ) : F p) =
        input[(i + 7).val] + input[(i + 18).val] -
          2 * input[(i + 7).val] * input[(i + 18).val] := by
      rw [← IsBool.xor_eq_val_xor b7 b18, ZMod.natCast_val]
      exact ZMod.cast_id p _
    rw [hc]; ring
  · have hr7 := eval_rotr32 env.toEnvironment input_var input h_input 7 i
    have hr18 := eval_rotr32 env.toEnvironment input_var input h_input 18 i
    have hs3 := eval_shr32 env.toEnvironment input_var input h_input 3 i
    have h1 := h_env1 i
    have h2 := h_env2 i
    simp only [Vector.getElem_ofFn, mul_zero, zero_add] at h2
    simp only [Vector.getElem_ofFn] at h1
    rw [show (i₀ + (32 + 32 * 0) + ↑i) = i₀ + 32 + ↑i from by ring, h2, h1, hr7, hr18, hs3]
    have b7 : input[(i + 7).val] = (0 : F p) ∨ input[(i + 7).val] = 1 := h_assumptions (i + 7)
    have b18 : input[(i + 18).val] = (0 : F p) ∨ input[(i + 18).val] = 1 := h_assumptions (i + 18)
    have bs3 : (if h : i.val + (3 : Fin 32).val < 32
          then (input[i.val + (3 : Fin 32).val]'h : F p) else 0) = 0 ∨
        (if h : i.val + (3 : Fin 32).val < 32
          then (input[i.val + (3 : Fin 32).val]'h : F p) else 0) = 1 :=
      shr_isbool _ input h_assumptions i
    set r7 : F p := input[(i + 7).val]
    set r18 : F p := input[(i + 18).val]
    set s3 : F p := if h : i.val + (3 : Fin 32).val < 32
      then input[i.val + (3 : Fin 32).val]'h else 0
    have hxor1 : ((r7.val ^^^ r18.val : ℕ) : F p) = r7 + r18 - 2 * r7 * r18 := by
      rw [← IsBool.xor_eq_val_xor b7 b18, ZMod.natCast_val]
      exact ZMod.cast_id p _
    have hxor1_bool : IsBool (((r7.val ^^^ r18.val : ℕ) : F p)) := by
      rw [hxor1]; exact IsBool.xor_is_bool b7 b18
    have hxor2 : (((r7.val ^^^ r18.val : ℕ) : F p).val ^^^ s3.val : ℕ) =
        ((r7.val ^^^ r18.val : ℕ) : F p).val ^^^ s3.val := rfl
    have hxor3 : (((((r7.val ^^^ r18.val : ℕ) : F p).val ^^^ s3.val) : ℕ) : F p) =
        ((r7.val ^^^ r18.val : ℕ) : F p) + s3 -
          2 * ((r7.val ^^^ r18.val : ℕ) : F p) * s3 := by
      rw [← IsBool.xor_eq_val_xor hxor1_bool bs3, ZMod.natCast_val]
      exact ZMod.cast_id p _
    rw [hxor3, hxor1]; ring

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end LowerSigma0
end Gadgets.SHA256
end
