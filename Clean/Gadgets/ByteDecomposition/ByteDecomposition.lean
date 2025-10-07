import Clean.Utils.Primes
import Clean.Utils.Field
import Clean.Gadgets.ByteDecomposition.Theorems
import Init.Data.Nat.Div.Basic

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

namespace Gadgets.ByteDecomposition
open FieldUtils (mod floorDiv two_lt two_pow_lt two_val two_pow_val)

structure Outputs (F : Type) where
  low : F
  high : F

instance : ProvableStruct Outputs where
  components := [field, field]
  toComponents := fun { low, high } => .cons low (.cons high .nil)
  fromComponents := fun (.cons low (.cons high .nil)) => { low, high }

/--
  Decompose a byte into a low and a high part.
  The low part is the least significant `offset` bits,
  and the high part is the most significant `8 - offset` bits.
-/
def main (offset : Fin 8) (x : Expression (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let low ← witness fun env => mod (env x) (2^offset.val) (by simp [two_pow_lt])
  let high ← witness fun env => floorDiv (env x) (2^offset.val)

  lookup ByteTable ((2^(8-offset.val) : F p) * low)
  lookup ByteTable high

  x === low + high * (2^offset.val : F p)

  return { low, high }

def Assumptions (x : F p) := x.val < 256

def Spec (offset : Fin 8) (x : F p) (out : Outputs (F p)) :=
  let ⟨low, high⟩ := out
  (low.val = x.val % (2^offset.val) ∧ high.val = x.val / (2^offset.val))
  ∧ (low.val < 2^offset.val ∧ high.val < 2^(8-offset.val))

def elaborated (offset : Fin 8) : ElaboratedCircuit (F p) field Outputs where
  main := main offset
  localLength _ := 2
  output _ i0 := varFromOffset Outputs i0

theorem soundness (offset : Fin 8) : Soundness (F p) (circuit := elaborated offset) Assumptions (Spec offset) := by
  intro i0 env yielded x_var (x : F p) h_input (x_byte : x.val < 256) h_holds
  simp only [id_eq, circuit_norm] at h_input
  simp only [circuit_norm, elaborated, main, Spec, ByteTable, h_input] at h_holds ⊢
  clear h_input

  obtain ⟨low_lt, high_lt, h_eq⟩ := h_holds
  set low := env.get i0
  set high := env.get (i0 + 1)

  have : 2^16 < p := by linarith [p_large_enough.elim]
  let n : ℕ := 8 - offset.val
  have neg_off_le : n ≤ 8 := by omega
  have pow_8 : 2^n * 2^offset.val = (2^8 : F p) := by simp [n, ←pow_add]
  have pow_8_nat : 2^n * 2^offset.val = 2^8 := by simp [n, ←pow_add]

  -- we first work with the equation multiplied by `2^n`, where we can make use of the range check on `2^n * low`
  -- the goal is to apply `FieldUtils.mul_nat_val_of_dvd` to get to the stronger inequality `low < 2^offset`
  have h_eq_mul : 2^n * x = 2^n * low + 2^n * 2^offset.val * high := by rw [h_eq, mul_add, mul_comm high, mul_assoc]
  replace h_eq_mul := congrArg ZMod.val h_eq_mul

  have h_lt_mul {x n} (hn : n ≤ 8) (hx : x < 2^8) : 2^n * x < 2^16 := by
    have : 2^(n+8) ≤ 2^16 := Nat.pow_le_pow_of_le (by norm_num) (by omega)
    suffices 2^n * x < 2^(n+8) by linarith
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_left hx (Nat.two_pow_pos n)

  have h_lt_mul_x : 2^n * x.val < 2^16 := h_lt_mul neg_off_le x_byte
  have h_pow8_val : (2^8 : F p).val = 2^8 := two_pow_val _ (by norm_num)
  have h_lt_mul_low : (2 ^ n * low).val < 2^8 := low_lt

  have h_mul_x : (2^n : F p).val * x.val = 2^n * ZMod.val x := by rw [two_pow_val _ neg_off_le]
  have : (2 ^ n * x).val = 2^n * x.val := by rw [ZMod.val_mul_of_lt (by linarith), h_mul_x]
  rw [this] at h_eq_mul

  have : (2^n * low + 2^n * 2^offset.val * high).val = (2^n * low).val + 2^n * 2^offset.val * high.val := by
    rw [ZMod.val_add, ZMod.val_mul _ high, Nat.add_mod_mod, pow_8_nat, pow_8, h_pow8_val, Nat.mod_eq_of_lt]
    linarith
  rw [this, mul_assoc (2^n)] at h_eq_mul
  replace h_eq_mul := Nat.sub_eq_of_eq_add h_eq_mul |>.symm
  have two_pow_cast : 2^n = ((2^n : ℕ) : F p) := by simp
  rw [←Nat.mul_sub, two_pow_cast] at h_eq_mul
  have h_eq_mul_low := FieldUtils.mul_nat_val_of_dvd (2^n) (two_pow_lt n ‹_›) h_eq_mul
  rw [←two_pow_cast] at h_eq_mul_low
  rw [h_eq_mul_low, ←pow_8_nat, Nat.mul_lt_mul_left (show 2^n > 0 by simp)] at h_lt_mul_low

  -- finally we have the desired inequality on `low`
  have h_lt_low : low.val < 2^offset.val := h_lt_mul_low
  have ⟨ low_eq, high_eq ⟩ := Theorems.soundness offset x low high x_byte h_lt_low high_lt h_eq
  use ⟨ low_eq, high_eq ⟩, h_lt_low
  rwa [high_eq, Nat.div_lt_iff_lt_mul (by simp), pow_8_nat]

theorem completeness (offset : Fin 8) : Completeness (F p) (elaborated offset) Assumptions := by
  rintro i0 env yielded x_var henv (x : F p) h_input (x_byte : x.val < 256)
  simp only [ProvableType.eval_field] at h_input
  simp only [circuit_norm, main, elaborated, h_input, ByteTable] at henv ⊢
  simp only [henv]
  have pow_8_nat : 2^8 = 2^(8-offset.val) * 2^offset.val := by simp [←pow_add]

  and_intros

  · show (2^(8-offset.val) * mod x (2^offset.val) _).val < 2^8
    suffices ((2 : F p)^(8-offset.val)).val * (mod x (2^offset.val) _).val < 2^8 by
      rwa [ZMod.val_mul_of_lt (by linarith [p_large_enough.elim])]
    rw [two_pow_val _ (by omega), pow_8_nat]
    exact Nat.mul_lt_mul_of_pos_left FieldUtils.mod_lt (Nat.pow_pos (by norm_num))

  · show (floorDiv x (2^offset.val)).val < 2^8
    apply FieldUtils.floorDiv_lt
    rw [PNat.pow_coe, PNat.val_ofNat]
    suffices 1 * 2^8 ≤ 2^offset.val * 2^8 by linarith
    apply Nat.mul_le_mul_right
    exact Nat.succ_le_of_lt (by norm_num)

  · have : (2^offset.val : F p) = ((2^offset.val : ℕ+) : F p) := by simp
    rw [this, mul_comm, FieldUtils.mod_add_floorDiv]

def circuit (offset : Fin 8) : FormalCircuit (F p) field Outputs := {
  elaborated offset with
  main := main offset
  Assumptions
  Spec := Spec offset
  soundness := soundness offset
  completeness := completeness offset
}
end Gadgets.ByteDecomposition
