import Mathlib.Data.ZMod.Basic

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

theorem sum_do_not_wrap_around (x y: F p) :
    x.val + y.val < p -> (x + y).val = x.val + y.val := by
  intro h
  have sum_eq_over_naturals : (x.val + y.val) % p = x.val + y.val
    := (Nat.mod_eq_iff_lt p_neq_zero).mpr h
  rw [ZMod.val_add, sum_eq_over_naturals]

theorem byte_sum_do_not_wrap (x y: F p) [p_large_enough: Fact (p > 512)]:
    x.val < 256 -> y.val < 256 -> (x + y).val = x.val + y.val := by
  intros hx hy
  have sum_lt_512 : x.val + y.val < 512 := Nat.add_lt_add hx hy
  have sum_lt_p : x.val + y.val < p := Nat.lt_trans sum_lt_512 p_large_enough.elim
  apply sum_do_not_wrap_around x y sum_lt_p

theorem byte_sum_le_bound (x y : F p) [p_large_enough: Fact (p > 512)]:
    x.val < 256 -> y.val < 256 -> (x + y).val < 511 := by
  intros hx hy
  apply Nat.le_sub_one_of_lt at hx
  apply Nat.le_sub_one_of_lt at hy
  have sum_bound := Nat.add_le_add hx hy
  simp at sum_bound
  apply Nat.lt_add_one_of_le at sum_bound
  rw [ZMod.val_add]
  simp at sum_bound

  have val_511_lt_p : 511 < p := Nat.lt_trans (by norm_num) p_large_enough.elim
  have sum_le_p : (x.val + y.val) < p := Nat.lt_trans sum_bound val_511_lt_p
  have sum_eq_over_naturals : (x.val + y.val) % p = x.val + y.val
    := (Nat.mod_eq_iff_lt p_neq_zero).mpr sum_le_p
  rw [sum_eq_over_naturals]
  exact sum_bound

theorem byte_sum_and_bit_do_not_wrap (x y b: F p) [p_large_enough: Fact (p > 512)]:
    x.val < 256 -> y.val < 256 -> b.val < 2 -> (b + x + y).val = b.val + x.val + y.val := by
  intros hx hy hb
  have sum_bound := byte_sum_le_bound x y hx hy
  have sum_lt_512 : b.val + (x + y).val ≤ 511 := by
    apply Nat.le_sub_one_of_lt at sum_bound
    apply Nat.le_sub_one_of_lt at hb
    simp at sum_bound
    simp at hb
    apply Nat.add_le_add hb sum_bound
  have sum_lt_p : b.val + (x + y).val < p := Nat.lt_trans
    (by apply Nat.lt_add_one_of_le at sum_lt_512; assumption) p_large_enough.elim
  rw [add_assoc, sum_do_not_wrap_around b (x + y) sum_lt_p,
    byte_sum_do_not_wrap x y hx hy, ←add_assoc]

theorem byte_sum_and_bit_do_not_wrap' (x y b: F p) [p_large_enough: Fact (p > 512)]:
    x.val < 256 -> y.val < 256 -> b.val < 2 -> (x + y + b).val = x.val + y.val + b.val := by
  intros hx hy hb
  have sum_bound := byte_sum_le_bound x y hx hy
  have sum_lt_512 : b.val + (x + y).val ≤ 511 := by
    apply Nat.le_sub_one_of_lt at sum_bound
    apply Nat.le_sub_one_of_lt at hb
    simp at sum_bound
    simp at hb
    apply Nat.add_le_add hb sum_bound
  have sum_lt_p : b.val + (x + y).val < p := Nat.lt_trans
    (by apply Nat.lt_add_one_of_le at sum_lt_512; assumption) p_large_enough.elim
  rw [add_comm] at sum_lt_p
  rw [sum_do_not_wrap_around (x + y) b sum_lt_p,
    byte_sum_do_not_wrap x y hx hy]

theorem byte_plus_256_do_not_wrap (x: F p) [p_large_enough: Fact (p > 512)]:
    x.val < 256 -> (x + 256).val = x.val + 256 := by
  intro hx
  have val_256_lt_p : 256 < p := Nat.lt_trans (by norm_num) p_large_enough.elim
  have mod_256_is_256 : 256 % p = 256 := (Nat.mod_eq_iff_lt (FieldUtils.p_neq_zero)).mpr val_256_lt_p
  have val_256_is_256 : (256 : F p).val = 256 % p := ZMod.val_natCast _
  have out_plus_256_lt_512 : x.val + 256 < 512 := Nat.add_lt_add_right hx 256
  have out_plus_256_lt_p : x.val + 256 < p := Nat.lt_trans out_plus_256_lt_512 p_large_enough.elim
  rw [← mod_256_is_256, ←val_256_is_256] at out_plus_256_lt_p
  have thm := sum_do_not_wrap_around x 256 out_plus_256_lt_p
  rw [val_256_is_256, mod_256_is_256] at thm
  apply thm

theorem val_lt_p {p : ℕ} (x: ℕ) : (x < p) → (x : F p).val = x := by
  intro x_lt_p
  have p_neq_zero : p ≠ 0 := Nat.not_eq_zero_of_lt x_lt_p
  have x_mod_is_x : x % p = x := (Nat.mod_eq_iff_lt p_neq_zero).mpr x_lt_p
  rw [ZMod.val_natCast x, x_mod_is_x]

theorem boolean_lt_2 {b : F p} (hb : b = 0 ∨ b = 1) : b.val < 2 := by
  rcases hb with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp [ZMod.val_one]

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
  · dsimp [nat_to_field]; aesop

theorem val_of_nat_to_field_eq {n: ℕ} {lt: n < p} : (nat_to_field n lt).val = n := by
  cases p
  · exact False.elim (Nat.not_lt_zero n lt)
  · rfl

def less_than_p [p_pos: NeZero p] (x: F p) : x.val < p := by
  rcases p
  · have : 0 ≠ 0 := p_pos.out; contradiction
  · exact x.is_lt

def mod (x: F p) (c: ℕ+) (lt: c < p) : F p :=
  FieldUtils.nat_to_field (x.val % c) (by linarith [Nat.mod_lt x.val c.pos, lt])

def mod_256 (x: F p) [p_large_enough: Fact (p > 512)] : F p :=
  mod x 256 (by linarith [p_large_enough.elim])

def floordiv [NeZero p] (x: F p) (c: ℕ+) : F p :=
  FieldUtils.nat_to_field (x.val / c) (by linarith [Nat.div_le_self x.val c, less_than_p x])

theorem mod_256_lt [Fact (p > 512)] (x : F p) : (mod_256 x).val < 256 := by
  rcases p with _ | n; cases p_neq_zero rfl
  show (x.val % 256) < 256
  exact Nat.mod_lt x.val (by norm_num)

theorem floordiv_bool [Fact (p > 512)] {x: F p} (h : x.val < 512) :
  floordiv x 256 = 0 ∨ floordiv x 256 = 1 := by
  rcases p with _ | n; cases p_neq_zero rfl
  let z := x.val / 256
  have : z < 2 := Nat.div_lt_of_lt_mul h
  -- show z = 0 ∨ z = 1
  rcases (Nat.lt_trichotomy z 1) with _ | h1 | _
  · left; apply ext; show z = 0; linarith
  · right; apply ext; show z = ZMod.val 1; rw [h1, ZMod.val_one]
  · linarith -- contradiction

theorem mod_add_div_256 [Fact (p > 512)] (x : F p) : x = mod_256 x + 256 * (floordiv x 256) := by
  rcases p with _ | n; cases p_neq_zero rfl
  let p := n + 1
  apply ext
  rw [ZMod.val_add, ZMod.val_mul]
  have : ZMod.val 256 = 256 := val_lt_p (p:=p) 256 (by linarith [‹Fact (p > 512)›.elim])
  rw [this, Nat.add_mod_mod]
  show x.val = (x.val % 256 + 256 * (x.val / 256)) % p
  rw [Nat.mod_add_div, (Nat.mod_eq_of_lt x.is_lt : x.val % p = x.val)]
end FieldUtils
