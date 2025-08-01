import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas

-- main field definition
def F p := ZMod p
instance (p : ℕ) [Fact p.Prime]: Field (F p) := ZMod.instField p
instance (p : ℕ) [Fact p.Prime] : Fintype (F p) := ZMod.fintype p
instance (p : ℕ) [Fact p.Prime] : Inhabited (F p) := ⟨0⟩
instance (p : ℕ) : CommRing (F p) := ZMod.commRing p

instance {p : ℕ} : DecidableEq (F p) := ZMod.decidableEq p

namespace FieldUtils
variable {p : ℕ} [p_prime: Fact p.Prime]

instance : NeZero p := ⟨p_prime.elim.ne_zero⟩

theorem p_ne_zero : p ≠ 0 := p_prime.elim.ne_zero

theorem ext {x y : F p} (h : x.val = y.val) : x = y := by
  cases p; cases p_ne_zero rfl
  exact Fin.ext h

theorem ext_iff {x y : F p} : x = y ↔ x.val = y.val := by
  constructor; simp_all; apply ext

theorem val_lt_p {p : ℕ} (x: ℕ) : (x < p) → (x : F p).val = x := by
  intro x_lt_p
  have p_ne_zero : p ≠ 0 := Nat.ne_zero_of_lt x_lt_p
  have x_mod_is_x : x % p = x := (Nat.mod_eq_iff_lt p_ne_zero).mpr x_lt_p
  rw [ZMod.val_natCast, x_mod_is_x]

lemma val_eq_256 [p_large_enough: Fact (p > 512)] : (256 : F p).val = 256 := val_lt_p 256 (by linarith [p_large_enough.elim])

/--
tactic script to fully rewrite a ZMod expression to its Nat version, given that
the expression is smaller than the modulus.

```
example (x y : F p) (hx: x.val < 256) (hy: y.val < 2) :
  (x + y * 256).val = x.val + y.val * 256 := by field_to_nat
```

expected context:
- the equation to prove as the goal
- size assumptions on variables and a sufficient `p > ...` instance

if no sufficient inequalities are in the context, then the tactic will leave an equation of the form `expr : Nat < p` unsolved.

note: this version is optimized specifically for byte arithmetic:
- specifically handles field constant 256
- expects `[Fact (p > 512)]` in the context
-/
syntax "field_to_nat" : tactic
macro_rules
  | `(tactic|field_to_nat) =>
    `(tactic|(
      intros
      repeat rw [ZMod.val_add] -- (a + b).val = (a.val + b.val) % p
      repeat rw [ZMod.val_mul] -- (a * b).val = (a.val * b.val) % p
      repeat rw [val_eq_256]
      try simp only [Nat.add_mod_mod, Nat.mod_add_mod, Nat.mul_mod_mod, Nat.mod_mul_mod]
      rw [Nat.mod_eq_of_lt _]
      repeat linarith [‹Fact (_ > 512)›.elim]))

example [Fact (p > 512)] (x y : F p) (hx: x.val < 256) (hy: y.val < 2) :
    (x + y * 256).val = x.val + y.val * 256 := by field_to_nat

def natToField (n: ℕ) (lt: n < p) : F p :=
  match p with
  | 0 => False.elim (Nat.not_lt_zero n lt)
  | _ + 1 => ⟨ n, lt ⟩

theorem natToField_zero : natToField 0 (p_prime.elim.pos) = 0 := by
  dsimp [natToField]
  cases p
  · exact False.elim (Nat.not_lt_zero 0 p_prime.elim.pos)
  · simp only

theorem natToField_eq {n: ℕ} {lt: n < p} (x : F p) (hx: x = natToField n lt) : x.val = n := by
  cases p
  · exact False.elim (Nat.not_lt_zero n lt)
  · rw [hx]; rfl

theorem natToField_of_val_eq_iff {x : F p} {lt: x.val < p} : natToField (x.val) lt = x := by
  cases p
  · exact False.elim (Nat.not_lt_zero x.val lt)
  · dsimp only [natToField]; rfl

theorem natToField_eq_natCast {n: ℕ} (lt: n < p) : ↑n = FieldUtils.natToField n lt := by
  cases p with
  | zero => exact False.elim (Nat.not_lt_zero n lt)
  | succ n' => {
    simp only [FieldUtils.natToField]
    rw [Fin.natCast_def]
    apply_fun Fin.val
    · simp only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      exact lt
    · apply Fin.val_injective
  }

theorem val_of_natToField_eq {n: ℕ} (lt: n < p) : (natToField n lt).val = n := by
  cases p
  · exact False.elim (Nat.not_lt_zero n lt)
  · rfl

def less_than_p (x: F p) : x.val < p := by
  rcases p with _ | n; cases p_ne_zero rfl
  exact x.is_lt

def mod (x: F p) (c: ℕ+) (lt: c < p) : F p :=
  FieldUtils.natToField (x.val % c) (by linarith [Nat.mod_lt x.val c.pos, lt])

def floorDiv (x: F p) (c: ℕ+) : F p :=
  FieldUtils.natToField (x.val / c) (by linarith [Nat.div_le_self x.val c, less_than_p x])

theorem mod_lt {x : F p} {c: ℕ+} {lt : c < p} : (mod x c lt).val < c := by
  rcases p with _ | p; cases p_ne_zero rfl
  show (x.val % c) < c
  exact Nat.mod_lt x.val (by norm_num)

theorem floorDiv_lt {x : F p} {c: ℕ+} {d : ℕ} (h : x.val < c * d) : (floorDiv x c).val < d := by
  rcases p with _ | n; cases p_ne_zero rfl
  exact Nat.div_lt_of_lt_mul h

lemma val_mul_floorDiv_self {x : F p} {c: ℕ+} (lt : c < p) : (c * (floorDiv x c)).val = c * (x.val / c) := by
  rcases p with _ | n; cases p_ne_zero rfl
  have : c * (x.val / c) ≤ x.val := Nat.mul_div_le (ZMod.val x) ↑c
  have h : x.val < n + 1 := x.is_lt
  rw [ZMod.val_mul, ZMod.val_cast_of_lt lt,
    show ZMod.val (floorDiv x c) = x.val / c by rfl, Nat.mod_eq_of_lt (by linarith)]

theorem mod_add_floorDiv {x : F p} {c: ℕ+} (lt : c < p) :
    mod x c lt + c * (floorDiv x c) = x := by
  rcases p with _ | n; cases p_ne_zero rfl
  have h : x.val < n + 1 := x.is_lt
  apply ext
  suffices x.val % c + (c * (floorDiv x c)).val = x.val by
    change (mod x c lt).val + _ = _ at this
    rwa [ZMod.val_add_of_lt]
    rwa [this]
  rw [val_mul_floorDiv_self lt, Nat.mod_add_div x.val c]

theorem mul_val_of_dvd {x c : F p} :
    c.val ∣ (c * x).val → (c * x).val = c.val * x.val := by
  by_cases c_pos? : c = 0
  · subst c_pos?; simp
  intro ⟨x', h_eq⟩
  have h_lt : c.val * x' < p := by
    rw [←h_eq]
    apply ZMod.val_lt
  have c_pos : c.val > 0 := ZMod.val_pos.mpr c_pos?
  have x'_lt : x' < p := calc x'
    _ = 1 * x' := by ring
    _ ≤ c.val * x' := by apply Nat.mul_le_mul_right x' (Nat.succ_le_of_lt c_pos)
    _ < p := h_lt
  let x'_f : F p := natToField x' x'_lt
  have x'_val_eq : x'_f.val = x' := natToField_eq x'_f rfl
  have cx_val_eq : (c * x'_f).val = c.val * x' := by
    rw [←x'_val_eq]
    apply ZMod.val_mul_of_lt
    rw [x'_val_eq]
    exact h_lt
  rw [←cx_val_eq] at h_eq
  obtain h_eq := ext h_eq
  rw [mul_right_inj' c_pos?] at h_eq
  rw [h_eq, x'_val_eq, cx_val_eq]

theorem mul_nat_val_of_dvd {x: F p} (c: ℕ) (c_lt : c < p) {z : ℕ} :
    (c * x).val = c * z → (c * x).val = c * x.val := by
  have c_val_eq : c = (c : F p).val := by rw [ZMod.val_cast_of_lt c_lt]
  rw (occs := .pos [2, 4]) [c_val_eq]
  intro h_dvd
  exact mul_val_of_dvd ⟨ z, h_dvd ⟩

theorem mul_nat_val_eq_iff {x: F p} (c: ℕ) (c_pos : c > 0) (c_lt : c < p) {z : ℕ} :
    (c * x).val = c * z ↔ (x.val = z ∧ c * x.val < p) := by
  constructor
  · intro h_dvd
    constructor
    · apply (mul_right_inj' (Nat.ne_zero_iff_zero_lt.mpr c_pos)).mp
      rw [←h_dvd, mul_nat_val_of_dvd c c_lt h_dvd]
    · rw [←mul_nat_val_of_dvd c c_lt h_dvd]
      apply ZMod.val_lt
  · intro ⟨ h_eq, h_lt ⟩
    have c_val_eq : c = (c : F p).val := by rw [ZMod.val_cast_of_lt c_lt]
    rw [←h_eq, ZMod.val_mul_of_lt, ←c_val_eq]
    rw [←c_val_eq]
    exact h_lt

-- some helper lemmas about 2, using the common assumption that p > 512

section
variable [Fact (p > 512)]

omit p_prime in
lemma two_lt : 2 < p := by
  linarith [‹Fact (p > 512)›.elim]

lemma two_val : (2 : F p).val = 2 :=
  FieldUtils.val_lt_p 2 two_lt

omit p_prime in
lemma two_pow_lt (n : ℕ) (hn : n ≤ 8) : 2^n < p := by
  have h : 2^n ≤ 2^8 := Nat.pow_le_pow_of_le (a := 2) Nat.one_lt_ofNat hn
  linarith [‹Fact (p > 512)›.elim]

lemma two_pow_val (n : ℕ) (hn : n ≤ 8) : (2^n : F p).val = 2^n := by
  rw [ZMod.val_pow, two_val]
  rw [two_val]
  exact two_pow_lt _ hn
end

end FieldUtils

-- utils related to bytes, and specifically field elements that are bytes (< 256)
namespace ByteUtils
open FieldUtils
variable {p : ℕ} [p_prime: Fact p.Prime]

def mod256 (x: F p) [p_large_enough: Fact (p > 512)] : F p :=
  mod x 256 (by linarith [p_large_enough.elim])

def floorDiv256 (x: F p) : F p := floorDiv x 256

theorem mod256_lt [Fact (p > 512)] (x : F p) : (mod256 x).val < 256 := mod_lt

theorem floorDiv256_bool [Fact (p > 512)] {x: F p} (h : x.val < 512) :
  floorDiv256 x = 0 ∨ floorDiv256 x = 1 := by
  rcases p with _ | n; cases p_ne_zero rfl
  let z := x.val / 256
  have : z < 2 := Nat.div_lt_of_lt_mul h
  -- show z = 0 ∨ z = 1
  rcases (Nat.lt_trichotomy z 1) with _ | h1 | _
  · left; apply ext; show z = 0; linarith
  · right; apply ext; show z = ZMod.val 1; rw [h1, ZMod.val_one]
  · linarith -- contradiction

theorem mod_add_div256 [Fact (p > 512)] (x : F p) : x = mod256 x + 256 * (floorDiv256 x) := by
  rcases p with _ | n; cases p_ne_zero rfl
  let p := n + 1
  apply ext
  rw [ZMod.val_add, ZMod.val_mul]
  have : ZMod.val 256 = 256 := val_lt_p (p := p) 256 (by linarith [‹Fact (p > 512)›.elim])
  rw [this, Nat.add_mod_mod]
  show x.val = (x.val % 256 + 256 * (x.val / 256)) % p
  rw [Nat.mod_add_div, (Nat.mod_eq_of_lt x.is_lt : x.val % p = x.val)]

def splitTwoBytes (i : Fin (256 * 256)) : Fin 256 × Fin 256 :=
  let x := i.val / 256
  let y := i.val % 256
  have x_lt : x < 256 := by simp [x, Nat.div_lt_iff_lt_mul]
  have y_lt : y < 256 := Nat.mod_lt i.val (by norm_num)
  (⟨ x, x_lt ⟩, ⟨ y, y_lt ⟩)

def concatTwoBytes (x y : Fin 256) : Fin (256 * 256) :=
  let i := x.val * 256 + y.val
  have i_lt : i < 256 * 256 := by
    unfold i
    linarith [x.is_lt, y.is_lt]
  ⟨ i, i_lt ⟩

theorem splitTwoBytes_concatTwoBytes (x y : Fin 256) : splitTwoBytes (concatTwoBytes x y) = (x, y) := by
  dsimp [splitTwoBytes, concatTwoBytes]
  ext
  simp only
  rw [mul_comm]
  have h := Nat.mul_add_div (by norm_num : 256 > 0) x.val y.val
  rw [h]
  simp
  simp only [Nat.mul_add_mod_of_lt y.is_lt]

theorem byte_sum_do_not_wrap (x y: F p) [Fact (p > 512)]:
    x.val < 256 -> y.val < 256 -> (x + y).val = x.val + y.val := by field_to_nat

theorem byte_sum_le_bound (x y : F p) [Fact (p > 512)]:
    x.val < 256 -> y.val < 256 -> (x + y).val < 511 := by field_to_nat

theorem byte_sum_and_bit_do_not_wrap (x y b: F p) [Fact (p > 512)]:
    x.val < 256 -> y.val < 256 -> b.val < 2 -> (b + x + y).val = b.val + x.val + y.val := by field_to_nat

theorem byte_sum_and_bit_do_not_wrap' (x y b: F p) [Fact (p > 512)]:
    x.val < 256 -> y.val < 256 -> b.val < 2 -> (x + y + b).val = x.val + y.val + b.val := by field_to_nat

theorem byte_sum_and_bit_lt_512 (x y b: F p) [Fact (p > 512)]:
    x.val < 256 -> y.val < 256 -> b.val < 2 -> (x + y + b).val < 512 := by field_to_nat

theorem byte_plus_256_do_not_wrap (x: F p) [Fact (p > 512)]:
    x.val < 256 -> (x + 256).val = x.val + 256 := by field_to_nat

section
variable [p_large_enough: Fact (p > 512)]

def fromByte (x: Fin 256) : F p :=
  FieldUtils.natToField x.val (by linarith [x.is_lt, p_large_enough.elim])

lemma fromByte_lt (x: Fin 256) : (fromByte (p := p) x).val < 256 := by
  dsimp [fromByte]
  rw [FieldUtils.val_of_natToField_eq]
  exact x.is_lt

lemma fromByte_eq (x : F p) (x_lt : x.val < 256) : fromByte ⟨ x.val, x_lt ⟩ = x := by
  dsimp [fromByte]
  apply FieldUtils.natToField_of_val_eq_iff

lemma fromByte_cast_eq {z: F p} (z_lt : z.val < 256) : fromByte z.cast = z := by
  simp only [fromByte]
  have : (z.cast : Fin 256).val = z.val := ZMod.val_cast_eq_val_of_lt z_lt
  simp only [this]
  apply FieldUtils.natToField_of_val_eq_iff

end
end ByteUtils
