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
def to_bits (n : ℕ) (x : ℕ) : Vector ℕ n :=
  .mapRange n fun i => if x.testBit i then 1 else 0

/--
  Convert a vector of bits to a natural number.
-/
def from_bits {n : ℕ} (bits : Vector ℕ n) : ℕ :=
  Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * 2^i) 0

/--
  Main lemma which establishes the behaviour of `from_bits`
  and `to_bits` by induction
-/
lemma to_bits_from_bits_aux {n: ℕ} (bits : Vector ℕ n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (from_bits bits) < 2^n ∧ to_bits n (from_bits bits) = bits := by
  rw [Vector.ext_iff]
  simp only [from_bits, to_bits, Vector.getElem_mapRange]
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

/-- `to_bits` is a left-inverse of `from_bits` -/
theorem to_bits_from_bits {n: ℕ} (bits : Vector ℕ n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    to_bits n (from_bits bits) = bits := (to_bits_from_bits_aux bits h_bits).right

/-- The result of `from_bits` is less than 2^n -/
theorem from_bits_lt {n: ℕ} (bits : Vector ℕ n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (from_bits bits) < 2^n := (to_bits_from_bits_aux bits h_bits).left

/-- On numbers less than `2^n`, `to_bits n` is injective -/
theorem to_bits_injective (n: ℕ) {x y : ℕ} : x < 2^n → y < 2^n →
    to_bits n x = to_bits n y → x = y := by
  intro hx hy h_eq
  rw [Vector.ext_iff] at h_eq
  simp only [to_bits, Vector.getElem_mapRange] at h_eq
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

/-- On numbers less than `2^n`, `to_bits` is a right-inverse of `from_bits` -/
theorem from_bits_to_bits {n: ℕ} {x : ℕ} (hx : x < 2^n) :
    from_bits (to_bits n x) = x := by
  have h_bits : ∀ i (hi : i < n), (to_bits n x)[i] = 0 ∨ (to_bits n x)[i] = 1 := by
    intro i hi; simp [to_bits]
  apply to_bits_injective n (from_bits_lt _ h_bits) hx
  rw [to_bits_from_bits _ h_bits]


-- field variant of `to_bits` and `from_bits`
variable {p : ℕ} [prime: Fact p.Prime]

/--
  Convert a field element to a vector of bits, which are themselves field elements.
-/
def field_to_bits (n : ℕ) (x : F p) : Vector (F p) n :=
  .map (↑) (to_bits n x.val)

/--
  Convert a vector of bits to a field element.
-/
def field_from_bits {n : ℕ} (bits : Vector (F p) n) : F p :=
  from_bits <| bits.map ZMod.val

def field_from_bits_expr {n: ℕ} (bits : Vector (Expression (F p)) n) : Expression (F p) :=
  Fin.foldl n (fun acc ⟨i, _⟩ => acc + bits[i] * (2^i : F p)) 0

/-- Evaluation commutes with bits accumulation -/
theorem field_from_bits_eval {n: ℕ} {eval : Environment (F p)} (bits : Vector (Expression (F p)) n) :
    eval (field_from_bits_expr bits) = field_from_bits (bits.map eval) := by
  simp only [field_from_bits_expr, field_from_bits, from_bits]
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

/--
  Define the behaviour of `field_from_bits` and `field_to_bits` by
  lifting `to_bits_from_bits_aux`
-/
lemma field_to_bits_field_from_bits_aux {n: ℕ} (hn : 2^n < p) (bits : Vector (F p) n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (field_from_bits bits).val < 2^n ∧ field_to_bits n (field_from_bits bits) = bits := by
  rw [Vector.ext_iff]
  simp only [field_from_bits, field_to_bits, Vector.getElem_mapRange]

  have h_bool : ∀ i (hi : i < n), (bits.map ZMod.val)[i] = 0 ∨ (bits.map ZMod.val)[i] = 1 := by
    intro i hi
    specialize h_bits i hi
    apply Or.elim h_bits
    · intro h; apply Or.inl; simp only [Vector.getElem_map, ZMod.val_eq_zero]; assumption
    · intro h; apply Or.inr; simp only [Vector.getElem_map]
      apply_fun ZMod.val at h
      simp only [ZMod.val_zero, ZMod.val_one] at h
      exact h

  obtain ⟨thm_lt, thm_val⟩ := to_bits_from_bits_aux (bits.map ZMod.val) h_bool
  constructor
  · rw [ZMod.val_natCast_of_lt (by linarith)]
    exact thm_lt
  · intro i hi
    simp
    have h := ZMod.val_natCast p ((from_bits (Vector.map ZMod.val bits)))
    simp_rw [h]
    have h_lt : from_bits (Vector.map ZMod.val bits) < p := by linarith
    simp_rw [Nat.mod_eq_of_lt h_lt, thm_val]
    simp
    rw [ZMod.cast_id]
    rfl

/-- The result of `field_from_bits` is less than 2^n -/
theorem field_from_bits_lt {n: ℕ} (hn : 2^n < p) (bits : Vector (F p) n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    (field_from_bits bits).val < 2^n := (field_to_bits_field_from_bits_aux hn bits h_bits).left

/-- `field_to_bits` is a left-inverse of `field_from_bits` -/
theorem field_to_bits_field_from_bits {n: ℕ} (hn : 2^n < p) (bits : Vector (F p) n)
  (h_bits : ∀ (i : ℕ) (hi : i < n), bits[i] = 0 ∨ bits[i] = 1) :
    field_to_bits n (field_from_bits bits) = bits := (field_to_bits_field_from_bits_aux hn bits h_bits).right

/-- On field elements less than `2^n`, `field_to_bits n` is injective -/
theorem field_to_bits_injective (n: ℕ) {x y : F p} : x.val < 2^n → y.val < 2^n →
    field_to_bits n x = field_to_bits n y → x = y := by
  intro hx hy h_eq
  simp only [field_to_bits] at h_eq
  rw [Vector.ext_iff] at h_eq
  simp only [to_bits, Vector.getElem_map, Vector.getElem_mapRange, Nat.cast_ite, Nat.cast_one,
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

/-- On field elements less than `2^n`, `field_to_bits` is a right-inverse of `field_from_bits` -/
theorem field_from_bits_field_to_bits {n: ℕ} (hn : 2^n < p) {x : F p} (hx : x.val < 2^n) :
    field_from_bits (field_to_bits n x) = x := by
  have h_bits : ∀ i (hi : i < n), (field_to_bits n x)[i] = 0 ∨ (field_to_bits n x)[i] = 1 := by
    intro i hi
    simp [field_to_bits, to_bits]

  apply field_to_bits_injective n (field_from_bits_lt hn _ h_bits) hx
  rw [field_to_bits_field_from_bits hn _ h_bits]

end Utils.Bits
