import Clean.Utils.Primes
import Clean.Utils.Field
import Clean.Gadgets.TwoPowerLookup
import Clean.Gadgets.ByteDecomposition.Theorems
import Init.Data.Nat.Div.Basic

namespace Gadgets.ByteDecomposition
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 2^16 + 2^8)]
instance : Fact (p > 512) := .mk (by linarith [p_large_enough.elim])

open Gadgets.ByteDecomposition.Theorems (byte_decomposition_lift)
open FieldUtils (mod floordiv two_lt two_pow_lt two_val two_pow_val)

structure Outputs (F : Type) where
  low : F
  high : F

instance : ProvableStruct Outputs where
  components := [field, field]
  to_components := fun { low, high } => .cons low (.cons high .nil)
  from_components := fun (.cons low (.cons high .nil)) => { low, high }

/--
  Decompose a byte into a low and a high part.
  The low part is the least significant `offset` bits,
  and the high part is the most significant `8 - offset` bits.
-/
def byte_decomposition (offset : Fin 8) (x :  Expression (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let low ← witness fun env => mod (env x) (2^offset.val) (by simp [two_pow_lt])
  let high ← witness fun env => floordiv (env x) (2^offset.val)

  lookup (ByteLookup ((2^(8 - offset.val) : F p) * low))
  lookup (ByteLookup high)

  x.assert_equals (low + high * (2^offset.val : F p))

  return { low, high }

def assumptions (x : field (F p)) := x.val < 256

def spec (offset : Fin 8) (x : field (F p)) (out: Outputs (F p)) :=
  let ⟨low, high⟩ := out
  low.val = x.val % (2^offset.val) ∧
  high.val = x.val / (2^offset.val)

def elaborated (offset : Fin 8) : ElaboratedCircuit (F p) field Outputs where
  main := byte_decomposition offset
  local_length _ := 2
  output _ i0 := var_from_offset Outputs i0

theorem soundness (offset : Fin 8) : Soundness (F p) (circuit := elaborated offset) assumptions (spec offset) := by
  intro i0 env x_var (x : F p) h_input (x_byte : x.val < 256) h_holds
  simp only [id_eq, circuit_norm] at h_input
  simp only [circuit_norm, elaborated, byte_decomposition, spec, ByteLookup, ByteTable.equiv, h_input] at h_holds ⊢
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

  have h_lt_mul {x n} (hn : n ≤ 8) (hx: x < 2^8) : 2^n * x < 2^16 := by
    have : 2^(n + 8) ≤ 2^16 := Nat.pow_le_pow_of_le (by norm_num) (by omega)
    suffices 2^n * x < 2^(n + 8) by linarith
    rw [pow_add]
    exact Nat.mul_lt_mul_of_pos_left hx (Nat.two_pow_pos n)

  have h_lt_mul_x : 2^n * x.val < 2^16 := h_lt_mul neg_off_le x_byte
  have h_pow8_val : (2^8 : F p).val = 2^8 := two_pow_val _ (by norm_num)
  have h_lt_mul_high : 2^n * 2^offset.val * high.val < 2^16 := by rw [pow_8_nat]; exact h_lt_mul (by norm_num) high_lt
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
  exact Theorems.soundness offset x low high x_byte h_lt_low high_lt h_eq

theorem completeness (offset : Fin 8) : Completeness (F p) (elaborated offset) assumptions := by
  rintro i0 env x_var henv x h_eval as
  simp only [assumptions] at as
  simp [circuit_norm, byte_decomposition, elaborated] at henv
  simp only [field, id] at x

  let ⟨ h0, h1 ⟩ := henv

  simp only [id_eq, ↓eval_field] at h_eval
  simp [circuit_norm, byte_decomposition, elaborated, ByteLookup, TwoPowerLookup.lookup]
  -- rw [TwoPowerLookup.equiv, TwoPowerLookup.equiv, h_eval, h0, h1]
  sorry

def circuit (offset : Fin 8) : FormalCircuit (F p) field Outputs := {
  elaborated offset with
  main := byte_decomposition offset
  assumptions
  spec := spec offset
  soundness := soundness offset
  completeness := completeness offset
}
end Gadgets.ByteDecomposition

namespace Gadgets.U64ByteDecomposition
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

structure Outputs (F : Type) where
  low : U64 F
  high : U64 F

instance : ProvableStruct Outputs where
  components := [U64, U64]
  to_components := fun { low, high } => .cons low (.cons high .nil)
  from_components := fun (.cons low (.cons high .nil)) => { low, high }

/--
  Decompose every limb of a u64 into a low and a high part.
  The low part is the least significant `offset` bits, and the high part is the most significant `8 - offset` bits.
-/
def u64_byte_decomposition (offset : Fin 8) (x : Var U64 (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := x

  let ⟨x0_l, x0_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit offset) x0
  let ⟨x1_l, x1_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit offset) x1
  let ⟨x2_l, x2_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit offset) x2
  let ⟨x3_l, x3_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit offset) x3
  let ⟨x4_l, x4_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit offset) x4
  let ⟨x5_l, x5_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit offset) x5
  let ⟨x6_l, x6_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit offset) x6
  let ⟨x7_l, x7_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit offset) x7

  let low := U64.mk x0_l x1_l x2_l x3_l x4_l x5_l x6_l x7_l
  let high := U64.mk x0_h x1_h x2_h x3_h x4_h x5_h x6_h x7_h

  return ⟨ low, high ⟩

def assumptions (x : U64 (F p)) := x.is_normalized

def spec (offset : Fin 8) (input : U64 (F p)) (out: Outputs (F p)) :=
  let ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := input
  let ⟨⟨x0_l, x1_l, x2_l, x3_l, x4_l, x5_l, x6_l, x7_l⟩,
        ⟨x0_h, x1_h, x2_h, x3_h, x4_h, x5_h, x6_h, x7_h⟩⟩ := out
  x0_l.val = x0.val % (2^offset.val) ∧ x0_h.val = x0.val / (2^offset.val) ∧
  x1_l.val = x1.val % (2^offset.val) ∧ x1_h.val = x1.val / (2^offset.val) ∧
  x2_l.val = x2.val % (2^offset.val) ∧ x2_h.val = x2.val / (2^offset.val) ∧
  x3_l.val = x3.val % (2^offset.val) ∧ x3_h.val = x3.val / (2^offset.val) ∧
  x4_l.val = x4.val % (2^offset.val) ∧ x4_h.val = x4.val / (2^offset.val) ∧
  x5_l.val = x5.val % (2^offset.val) ∧ x5_h.val = x5.val / (2^offset.val) ∧
  x6_l.val = x6.val % (2^offset.val) ∧ x6_h.val = x6.val / (2^offset.val) ∧
  x7_l.val = x7.val % (2^offset.val) ∧ x7_h.val = x7.val / (2^offset.val)

-- #eval! (u64_byte_decomposition (p:=p_babybear) 0) default |>.operations.local_length
-- #eval! (u64_byte_decomposition (p:=p_babybear) 0) default |>.output
def elaborated (offset : Fin 8) : ElaboratedCircuit (F p) U64 Outputs where
  main := u64_byte_decomposition offset
  local_length _ := 16
  output _ i0 := {
    low := ⟨var ⟨i0 + 0⟩, var ⟨i0 + 2⟩, var ⟨i0 + 4⟩, var ⟨i0 + 6⟩, var ⟨i0 + 8⟩, var ⟨i0 + 10⟩, var ⟨i0 + 12⟩, var ⟨i0 + 14⟩⟩,
    high := ⟨var ⟨i0 + 1⟩, var ⟨i0 + 3⟩, var ⟨i0 + 5⟩, var ⟨i0 + 7⟩, var ⟨i0 + 9⟩, var ⟨i0 + 11⟩, var ⟨i0 + 13⟩, var ⟨i0 + 15⟩⟩
  }

theorem soundness (offset : Fin 8) : Soundness (F p) (elaborated offset) assumptions (spec offset) := by
  intro i0 env x_var ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_input ⟨x_byte, offset_positive⟩ h_holds
  simp [circuit_norm, elaborated, u64_byte_decomposition, ByteLookup, ByteTable.equiv, h_input] at h_holds
  simp [subcircuit_norm, ByteDecomposition.circuit, ByteDecomposition.elaborated,
    ByteDecomposition.assumptions, ByteDecomposition.spec, eval, circuit_norm, var_from_offset, Vector.mapRange] at h_holds

  simp [assumptions, U64.is_normalized] at x_byte
  simp [eval, circuit_norm] at h_input

  simp only [spec, ↓ProvableStruct.eval_eq_eval_struct, ProvableStruct.eval, from_components,
    ProvableStruct.eval.go, eval, from_elements, size, to_vars, to_elements, elaborated, add_zero,
    ElaboratedCircuit.output, Vector.map_mk, List.map_toArray, List.map_cons, Expression.eval,
    List.map_nil, Vector.mapRange]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h_input
  simp [h0, h1, h2, h3, h4, h5, h6, h7, and_assoc, var_from_offset] at h_holds
  clear h0 h1 h2 h3 h4 h5 h6 h7

  obtain ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩ := h_holds
  simp_all only [gt_iff_lt, Fin.val_pos_iff, forall_const, and_self]


theorem completeness (offset : Fin 8) : Completeness (F p) (elaborated offset) assumptions := by
  rintro i0 env ⟨x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var⟩ henv ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_eval as
  simp only [assumptions] at as
  sorry

def circuit (offset : Fin 8) : FormalCircuit (F p) U64 Outputs := {
  elaborated offset with
  main := u64_byte_decomposition offset
  assumptions
  spec := spec offset
  soundness := soundness offset
  completeness := completeness offset
}
end Gadgets.U64ByteDecomposition
