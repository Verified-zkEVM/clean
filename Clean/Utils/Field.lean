import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod

-- main field definition
def F p := ZMod p
instance (p : ℕ) [Fact p.Prime]: Field (F p) := ZMod.instField p
instance (p : ℕ) [Fact p.Prime] : Fintype (F p) := ZMod.fintype p
instance (p : ℕ) [Fact p.Prime] : Inhabited (F p) := ⟨0⟩
instance (p : ℕ) : CommRing (F p) := ZMod.commRing p

namespace FieldUtils
variable {p : ℕ} [p_prime: Fact p.Prime]

instance : NeZero p := ⟨p_prime.elim.ne_zero⟩

theorem p_neq_zero : p ≠ 0 := p_prime.elim.ne_zero

theorem ext {x y : F p} (h : x.val = y.val) : x = y := by
  cases p; cases p_neq_zero rfl
  exact Fin.ext h

theorem val_lt_p {p : ℕ} (x: ℕ) : (x < p) → (x : F p).val = x := by
  intro x_lt_p
  have p_neq_zero : p ≠ 0 := Nat.not_eq_zero_of_lt x_lt_p
  have x_mod_is_x : x % p = x := (Nat.mod_eq_iff_lt p_neq_zero).mpr x_lt_p
  rw [ZMod.val_natCast x, x_mod_is_x]

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

theorem boolean_lt_2 {b : F p} (hb : b = 0 ∨ b = 1) : b.val < 2 := by
  rcases hb with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp only [ZMod.val_one, Nat.one_lt_ofNat]

def nat_to_field (n: ℕ) (lt: n < p) : F p :=
  match p with
  | 0 => False.elim (Nat.not_lt_zero n lt)
  | _ + 1 => ⟨ n, lt ⟩

theorem nat_to_field_eq {n: ℕ} {lt: n < p} (x : F p) (hx: x = nat_to_field n lt) : x.val = n := by
  cases p
  · exact False.elim (Nat.not_lt_zero n lt)
  · rw [hx]; rfl

theorem nat_to_field_of_val_eq_iff {x : F p} {lt: x.val < p} : nat_to_field (x.val) lt = x := by
  cases p
  · exact False.elim (Nat.not_lt_zero x.val lt)
  · dsimp only [nat_to_field]; rfl

theorem nat_to_field_eq_natcast {n: ℕ} (lt: n < p) : ↑n = FieldUtils.nat_to_field n lt := by
  cases p with
  | zero => exact False.elim (Nat.not_lt_zero n lt)
  | succ n' => {
    simp only [FieldUtils.nat_to_field]
    rw [Fin.natCast_def]
    apply_fun Fin.val
    · simp only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
      exact lt
    · apply Fin.val_injective
  }

theorem val_of_nat_to_field_eq {n: ℕ} (lt: n < p) : (nat_to_field n lt).val = n := by
  cases p
  · exact False.elim (Nat.not_lt_zero n lt)
  · rfl

def less_than_p [p_pos: NeZero p] (x: F p) : x.val < p := by
  rcases p
  · have : 0 ≠ 0 := p_pos.out; contradiction
  · exact x.is_lt

def mod (x: F p) (c: ℕ+) (lt: c < p) : F p :=
  FieldUtils.nat_to_field (x.val % c) (by linarith [Nat.mod_lt x.val c.pos, lt])

def floordiv [NeZero p] (x: F p) (c: ℕ+) : F p :=
  FieldUtils.nat_to_field (x.val / c) (by linarith [Nat.div_le_self x.val c, less_than_p x])

end FieldUtils

-- utils related to bytes, and specifically field elements that are bytes (< 256)
namespace ByteUtils
open FieldUtils
variable {p : ℕ} [p_prime: Fact p.Prime]

def mod_256 (x: F p) [p_large_enough: Fact (p > 512)] : F p :=
  mod x 256 (by linarith [p_large_enough.elim])

def floordiv_256 (x: F p) : F p := floordiv x 256

theorem mod_256_lt [Fact (p > 512)] (x : F p) : (mod_256 x).val < 256 := by
  rcases p with _ | n; cases p_neq_zero rfl
  show (x.val % 256) < 256
  exact Nat.mod_lt x.val (by norm_num)

theorem floordiv_256_bool [Fact (p > 512)] {x: F p} (h : x.val < 512) :
  floordiv_256 x = 0 ∨ floordiv_256 x = 1 := by
  rcases p with _ | n; cases p_neq_zero rfl
  let z := x.val / 256
  have : z < 2 := Nat.div_lt_of_lt_mul h
  -- show z = 0 ∨ z = 1
  rcases (Nat.lt_trichotomy z 1) with _ | h1 | _
  · left; apply ext; show z = 0; linarith
  · right; apply ext; show z = ZMod.val 1; rw [h1, ZMod.val_one]
  · linarith -- contradiction

theorem mod_add_div_256 [Fact (p > 512)] (x : F p) : x = mod_256 x + 256 * (floordiv_256 x) := by
  rcases p with _ | n; cases p_neq_zero rfl
  let p := n + 1
  apply ext
  rw [ZMod.val_add, ZMod.val_mul]
  have : ZMod.val 256 = 256 := val_lt_p (p:=p) 256 (by linarith [‹Fact (p > 512)›.elim])
  rw [this, Nat.add_mod_mod]
  show x.val = (x.val % 256 + 256 * (x.val / 256)) % p
  rw [Nat.mod_add_div, (Nat.mod_eq_of_lt x.is_lt : x.val % p = x.val)]

def split_two_bytes (i : Fin (256 * 256)) : Fin 256 × Fin 256 :=
  let x := i.val / 256
  let y := i.val % 256
  have x_lt : x < 256 := by simp [x, Nat.div_lt_iff_lt_mul]
  have y_lt : y < 256 := Nat.mod_lt i.val (by norm_num)
  (⟨ x, x_lt ⟩, ⟨ y, y_lt ⟩)

def concat_two_bytes (x y : Fin 256) : Fin (256 * 256) :=
  let i := x.val * 256 + y.val
  have i_lt : i < 256 * 256 := by
    unfold i
    linarith [x.is_lt, y.is_lt]
  ⟨ i, i_lt ⟩

theorem concat_split (x y : Fin 256) : split_two_bytes (concat_two_bytes x y) = (x, y) := by
  dsimp [split_two_bytes, concat_two_bytes]
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

def from_byte (x: Fin 256) : F p :=
  FieldUtils.nat_to_field x.val (by linarith [x.is_lt, p_large_enough.elim])

lemma from_byte_lt (x: Fin 256) : (from_byte (p:=p) x).val < 256 := by
  dsimp [from_byte]
  rw [FieldUtils.val_of_nat_to_field_eq]
  exact x.is_lt

lemma from_byte_eq (x : F p) (x_lt : x.val < 256) : from_byte ⟨ x.val, x_lt ⟩ = x := by
  dsimp [from_byte]
  apply FieldUtils.nat_to_field_of_val_eq_iff

lemma from_byte_cast_eq {z: F p} (z_lt : z.val < 256) : from_byte z.cast = z := by
  simp only [from_byte]
  have : (z.cast : Fin 256).val = z.val := ZMod.val_cast_eq_val_of_lt z_lt
  simp only [this]
  apply FieldUtils.nat_to_field_of_val_eq_iff

end
end ByteUtils
