/-
This file defines a conversion between a field element and its bit representation.
The bits are themselves typed as field elements, with values in { 0, 1 }.
-/
import Clean.Utils.Field
import Clean.Utils.Vector
import Clean.Circuit.Expression

namespace Utils.Bits
/--
  Convert a natural number to a vector of bits.
-/
def toBits (n : ℕ) (x : ℕ) : Vector ℕ n :=
  .mapRange n fun i => if x.testBit i then 1 else 0

/--
  Convert a vector of bits to a natural number.
-/
def fromBits {n : ℕ} (bits : Vector ℕ n) : ℕ :=
  Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * 2^i) 0

/--
  Main lemma which establishes the behaviour of `fromBits`
  and `toBits` by induction
-/
lemma toBits_fromBits_aux {n: ℕ} (bits : Vector ℕ n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (fromBits bits) < 2^n ∧ toBits n (fromBits bits) = bits := by
  rw [Vector.ext_iff]
  simp only [fromBits, toBits, Vector.getElem_mapRange]
  induction n with
  | zero => simp_all
  | succ n ih =>
    simp only [Fin.foldl_succ_last, Fin.coe_castSucc, Fin.val_last]
    let bits' : Vector ℕ n := bits.pop
    have h_bits' : ∀ j (hj : j < n), bits'[j] = 0 ∨ bits'[j] = 1
      | j, hj => by
        simp only [Vector.getElem_pop', bits']
        exact h_bits j (Nat.lt_succ_of_lt hj)

    have h_bits_n : bits[n] = 0 ∨ bits[n] = 1 := h_bits n (Nat.lt_succ_self _)
    obtain ⟨ ih_lt, ih_eq ⟩ := ih bits' h_bits'

    simp only [Vector.getElem_pop', bits'] at ih_eq ih_lt

    let xn : ℕ := Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * (2 ^ i)) 0
    have : bits[n] ≤ 1 := by rcases h_bits_n <;> simp only [zero_le, le_refl, *]
    have h_lt : xn + bits[n] * 2^n < 2^(n + 1) := by
      have : bits[n] * 2^n ≤ 1 * 2^n := Nat.mul_le_mul_right (2 ^ n) (by linarith)
      rw [Nat.pow_succ']
      linarith

    constructor
    · exact h_lt
    · intro i hi
      rw [mul_comm _ (2^n), add_comm _ (2^n * _), Nat.testBit_two_pow_mul_add _ ih_lt]
      by_cases hin : i < n <;> simp only [hin, reduceIte]
      · exact ih_eq i hin
      · have : n = i := by linarith
        subst this
        rcases h_bits_n <;> simp [*, ZMod.val_one]

/-- `toBits` is a left-inverse of `fromBits` -/
theorem toBits_fromBits {n: ℕ} (bits : Vector ℕ n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    toBits n (fromBits bits) = bits := (toBits_fromBits_aux bits h_bits).right

/-- The result of `fromBits` is less than 2^n -/
theorem fromBits_lt {n: ℕ} (bits : Vector ℕ n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (fromBits bits) < 2^n := (toBits_fromBits_aux bits h_bits).left

/-- On numbers less than `2^n`, `toBits n` is injective -/
theorem toBits_injective (n: ℕ) {x y : ℕ} : x < 2^n → y < 2^n →
    toBits n x = toBits n y → x = y := by
  intro hx hy h_eq
  rw [Vector.ext_iff] at h_eq
  simp only [toBits, Vector.getElem_mapRange] at h_eq
  have h_eq' : ∀ i (hi : i < n), x.testBit i = y.testBit i := by
    intro i hi
    specialize h_eq i hi
    by_cases hx_i : x.testBit i <;> by_cases hy_i : y.testBit i <;>
      simp_all

  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact h_eq' i hi
  · have : n ≤ i := by linarith
    have : 2^n ≤ 2^i := Nat.pow_le_pow_of_le (a:=2) (by norm_num) this
    replace hx : x < 2^i := by linarith
    replace hy : y < 2^i := by linarith
    rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]

/-- On numbers less than `2^n`, `toBits` is a right-inverse of `fromBits` -/
theorem fromBits_toBits {n: ℕ} {x : ℕ} (hx : x < 2^n) :
    fromBits (toBits n x) = x := by
  have h_bits : ∀ i (hi : i < n), (toBits n x)[i] = 0 ∨ (toBits n x)[i] = 1 := by
    intro i hi; simp [toBits, Vector.getElem_mapRange]
  apply toBits_injective n (fromBits_lt _ h_bits) hx
  rw [toBits_fromBits _ h_bits]


-- field variant of `toBits` and `fromBits`
variable {p : ℕ} [prime: Fact p.Prime]

/--
Convert a field element to a vector of bits, which are themselves field elements.
-/
def fieldToBits (n : ℕ) (x : F p) : Vector (F p) n :=
  .map (↑) (toBits n x.val)

/--
Convert a vector of bits to a field element.
-/
def fieldFromBits {n : ℕ} (bits : Vector (F p) n) : F p :=
  fromBits <| bits.map ZMod.val

def fieldFromBitsExpr {n: ℕ} (bits : Vector (Expression (F p)) n) : Expression (F p) :=
  Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * (2^i : F p)) 0

/-- Evaluation commutes with bits accumulation -/
theorem fieldFromBits_eval {n: ℕ} {eval : Environment (F p)} (bits : Vector (Expression (F p)) n) :
    eval (fieldFromBitsExpr bits) = fieldFromBits (bits.map eval) := by
  simp only [fieldFromBitsExpr, fieldFromBits, fromBits]
  induction n with
  | zero => simp only [Fin.foldl_zero, Expression.eval, Vector.map_map, Vector.getElem_map,
    Function.comp_apply, Nat.cast_zero]
  | succ n ih =>
    obtain ih := ih bits.pop
    simp [Vector.getElem_pop'] at ih
    simp [Fin.foldl_succ_last, ih, Expression.eval]
    apply Or.inl
    symm
    rw [ZMod.cast_id]

theorem fieldToBits_bits {n : ℕ} {x : F p} :
    ∀ i (_ : i < n), (fieldToBits n x)[i] = 0 ∨ (fieldToBits n x)[i] = 1 := by
  simp [fieldToBits, toBits, Vector.getElem_mapRange]

/--
Define the behaviour of `fieldFromBits` and `fieldToBits` by
lifting `toBits_fromBits_aux`
-/
lemma fieldToBits_fieldFromBits_aux {n: ℕ} (hn : 2^n < p) (bits : Vector (F p) n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (fieldFromBits bits).val < 2^n ∧ fieldToBits n (fieldFromBits bits) = bits := by
  rw [Vector.ext_iff]
  simp only [fieldFromBits, fieldToBits, Vector.getElem_mapRange]

  have h_bool : ∀ i (hi : i < n), (bits.map ZMod.val)[i] = 0 ∨ (bits.map ZMod.val)[i] = 1 := by
    intro i hi
    specialize h_bits i hi
    apply Or.elim h_bits
    · intro h; apply Or.inl; simp only [Vector.getElem_map, ZMod.val_eq_zero]; assumption
    · intro h; apply Or.inr; simp only [Vector.getElem_map]
      apply_fun ZMod.val at h
      simp only [ZMod.val_zero, ZMod.val_one] at h
      exact h

  obtain ⟨thm_lt, thm_val⟩ := toBits_fromBits_aux (bits.map ZMod.val) h_bool
  constructor
  · rw [ZMod.val_natCast_of_lt (by linarith)]
    exact thm_lt
  · intro i hi
    simp
    have h := ZMod.val_natCast p ((fromBits (Vector.map ZMod.val bits)))
    simp_rw [h]
    have h_lt : fromBits (Vector.map ZMod.val bits) < p := by linarith
    simp_rw [Nat.mod_eq_of_lt h_lt, thm_val]
    simp
    rw [ZMod.cast_id]
    rfl

/-- The result of `fieldFromBits` is less than 2^n -/
theorem fieldFromBits_lt {n: ℕ} (bits : Vector (F p) n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (fieldFromBits bits).val < 2^n := by
  by_cases hn : 2^n < p
  · exact (fieldToBits_fieldFromBits_aux hn bits h_bits).left
  have : p ≤ 2^n := Nat.le_of_not_lt hn
  have : (fieldFromBits bits).val < p := ZMod.val_lt _
  linarith

/-- `fieldToBits` is a left-inverse of `fieldFromBits` -/
theorem fieldToBits_fieldFromBits {n: ℕ} (hn : 2^n < p) (bits : Vector (F p) n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    fieldToBits n (fieldFromBits bits) = bits := (fieldToBits_fieldFromBits_aux hn bits h_bits).right

/-- On field elements less than `2^n`, `fieldToBits n` is injective -/
theorem fieldToBits_injective (n : ℕ) {x y : F p} : x.val < 2^n → y.val < 2^n →
    fieldToBits n x = fieldToBits n y → x = y := by
  intro hx hy h_eq
  simp only [fieldToBits] at h_eq
  rw [Vector.ext_iff] at h_eq
  simp only [toBits, Vector.getElem_map, Vector.getElem_mapRange, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero] at h_eq

  have h_eq' : ∀ i (hi : i < n), x.val.testBit i = y.val.testBit i := by
    intro i hi
    specialize h_eq i hi
    by_cases hx_i : x.val.testBit i <;> by_cases hy_i : y.val.testBit i <;>
      simp_all
  apply FieldUtils.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < n
  · exact h_eq' i hi
  have : n ≤ i := by linarith
  have : 2^n ≤ 2^i := Nat.pow_le_pow_of_le (a:=2) (by norm_num) this
  replace hx : x.val < 2^i := by linarith
  replace hy : y.val < 2^i := by linarith
  rw [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]

lemma val_natCast_toBits {n} {x : ℕ} :
    Vector.map (ZMod.val ∘ Nat.cast (R:=F p)) (toBits n x) = toBits n x := by
  rw [Vector.ext_iff]
  intro i hi
  simp only [Vector.getElem_map, Function.comp_apply, id_eq]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  simp only [toBits, Vector.getElem_mapRange]
  split
  · exact prime.elim.one_lt
  · exact prime.elim.pos

/-- On field elements less than `2^n`, `fieldToBits` is a right-inverse of `fieldFromBits` -/
theorem fieldFromBits_fieldToBits {n: ℕ} {x : F p} (hx : x.val < 2^n) :
    fieldFromBits (fieldToBits n x) = x := by
  simp only [fieldToBits, fieldFromBits]
  rw [Vector.map_map, val_natCast_toBits, fromBits_toBits hx, ZMod.natCast_zmod_val]

/-! ## Additional lemmas about fieldFromBits -/

/-- fieldFromBits decomposes as sum of first n bits + bit_n * 2^n -/
lemma fieldFromBits_succ (n : ℕ) (bits : Vector (F p) (n + 1)) :
    fieldFromBits bits =
    fieldFromBits (bits.take n) + bits[n] * (2^n : F p) := by
  simp only [fieldFromBits, fromBits, Fin.foldl_succ_last, Fin.coe_castSucc, Fin.val_last]
  have h_min : min n (n + 1) = n := min_eq_left (Nat.le_succ n)
  simp only [Vector.getElem_map, Nat.cast_add, Nat.cast_mul, ZMod.natCast_val, Nat.cast_pow,
    Nat.cast_ofNat, Vector.take_eq_extract, add_tsub_cancel_right, Vector.extract_eq_pop,
    Nat.add_one_sub_one, Nat.sub_zero, Vector.getElem_cast, Vector.getElem_pop']
  congr
  · norm_num
  · -- Show the function equality via HEq
    -- The two functions are equal - they just have different variable names
    -- But we need to handle the type equality: Fin n vs Fin (min n (n + 1))
    have h_min : min n (n + 1) = n := min_eq_left (Nat.le_succ n)
    apply Function.hfunext
    · rfl
    · intro a0 a1 h_a
      have : a0 = a1 := by
        apply eq_of_heq
        assumption
      rw[this]
      apply Function.hfunext
      · rw [h_min]
      · intros b0 b1 h_b
        simp only [heq_eq_eq]
        congr
        rw [h_min]
        rw [h_min]
  · -- Show bits[n].cast = bits[n]
    -- The cast here is ZMod.cast from F p to F p, which should be identity
    rw [ZMod.cast_id']
    rfl

/-- The sum Σ_k bits[k] * 2^k equals fieldFromBits(bits) -/
lemma fieldFromBits_as_sum {n : ℕ} (bits : Vector (F p) n) :
    fieldFromBits bits =
    Fin.foldl n (fun acc k => acc + bits[k] * (2^k.val : F p)) 0 := by
  -- fieldFromBits uses fromBits which sums bits[k].val * 2^k
  -- We need to show this equals the sum of bits[k] * 2^k (without .val)
  induction n
  · -- Base case: n = 0
    simp only [fieldFromBits, fromBits, Fin.foldl_zero]
    norm_cast
  · rename_i pre_n ih
    rw [fieldFromBits_succ]
    have min_pre_h : (min pre_n (pre_n + 1)) = pre_n := by omega
    calc
      _ = fieldFromBits (Vector.cast min_pre_h (bits.take pre_n)) + bits[pre_n] * 2 ^ pre_n := by
        congr
        simp only [Vector.take_eq_extract, add_tsub_cancel_right, Vector.extract_eq_pop,
          Nat.add_one_sub_one, Nat.sub_zero, Vector.cast_cast, Vector.cast_rfl]
        apply Vector.cast_heq
      _ = _ := by
        rw [ih]
        simp only [Fin.foldl_succ_last]
        congr
        ext acc k
        simp only [Vector.take_eq_extract, add_tsub_cancel_right, Vector.extract_eq_pop,
          Nat.add_one_sub_one, Nat.sub_zero, Fin.getElem_fin, Fin.coe_castSucc, add_right_inj,
          mul_eq_mul_right_iff, pow_eq_zero_iff', ne_eq]
        left
        repeat rw[Vector.getElem_cast]
        simp only [Vector.getElem_pop']

/-- fieldFromBits of empty vector (Expression version) -/
lemma fieldFromBits_empty_expr (bits : Vector (Expression (F p)) 0) (env : Environment (F p)) :
    fieldFromBits (Vector.map (Expression.eval env) bits) = 0 := by
  -- For a vector of length 0, fieldFromBits should return 0
  simp only [fieldFromBits, fromBits]
  -- Fin.foldl 0 returns the initial value 0
  simp only [Fin.foldl_zero]
  -- ↑0 = 0
  norm_cast

end Utils.Bits
