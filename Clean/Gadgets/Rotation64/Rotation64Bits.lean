import Clean.Types.U64
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Rotation64.Theorems
import Clean.Gadgets.Rotation64.Rotation64Bytes
import Clean.Gadgets.Rotation64.ByteRotationTable
import Clean.Gadgets.ByteDecomposition.ByteDecomposition
import Clean.Gadgets.ByteDecomposition.Theorems
import Clean.Circuit.Provable

namespace Gadgets.Rotation64Bits
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Bitwise (rot_right64)
open Gadgets.ByteDecomposition.Theorems (byte_decomposition_lift)

/--
  Rotate the 64-bit integer by `offset` bits
-/
def rot64_bits (offset : Fin 8) (x : Var U64 (F p)) : Circuit (F p) (Var U64 (F p)) := do

  let base : F p := (2^(8 - offset.val) % 256 : ℕ)

  let ⟨low, high⟩ ← subcircuit (Gadgets.U64ByteDecomposition.circuit offset) x
  let ⟨x0_l, x1_l, x2_l, x3_l, x4_l, x5_l, x6_l, x7_l⟩ := low
  let ⟨x0_h, x1_h, x2_h, x3_h, x4_h, x5_h, x6_h, x7_h⟩ := high

  let ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩ ← U64.witness fun _env => U64.mk 0 0 0 0 0 0 0 0

  assert_zero (x1_l * base + x0_h - y0)
  assert_zero (x2_l * base + x1_h - y1)
  assert_zero (x3_l * base + x2_h - y2)
  assert_zero (x4_l * base + x3_h - y3)
  assert_zero (x5_l * base + x4_h - y4)
  assert_zero (x6_l * base + x5_h - y5)
  assert_zero (x7_l * base + x6_h - y6)
  assert_zero (x0_l * base + x7_h - y7)
  return ⟨y0, y1, y2, y3, y4, y5, y6, y7⟩

instance lawful (off : Fin 8) : ConstantLawfulCircuits (F := (F p)) (rot64_bits off) := by infer_constant_lawful_circuits

def assumptions (input : U64 (F p)) := input.is_normalized

def spec (offset : Fin 8) (x : U64 (F p)) (y: U64 (F p)) :=
  y.value = rot_right64 x.value offset.val
  ∧ y.is_normalized

-- #eval! (rot64_bits (p:=p_babybear) 0) default |>.operations.local_length
-- #eval! (rot64_bits (p:=p_babybear) 0) default |>.output
def elaborated (off : Fin 8) : ElaboratedCircuit (F p) U64 U64 where
  main := rot64_bits off
  local_length _ := 24
  output _inputs i0 := var_from_offset U64 (i0 + 16)
  initial_offset_eq := by
    intros
    simp only [rot64_bits]
    rfl
  local_length_eq := by
    intros
    simp only [rot64_bits]
    rfl

lemma mul_mod_256_off (offset : Fin 8) (x i : ℕ) (h : i > 0):
    (x * 256^i) % 2^offset.val = 0 := by
  rw [Nat.mul_mod, Nat.pow_mod]
  fin_cases offset <;>
  simp only [Nat.reducePow, Nat.reduceMod, Nat.zero_pow h, Nat.zero_mod, mul_zero]

lemma two_off_eq_mod (offset : Fin 8) (h : offset.val ≠ 0):
    (2 ^ (8 - offset.val) % 256) = 2 ^ (8 - offset.val) := by
  apply Nat.mod_eq_of_lt
  fin_cases offset <;>
    first
    | contradiction
    | simp

lemma Nat.pow_minus_one_mul {x y : ℕ} (hy : y > 0) : x ^ y = x * x ^ (y - 1) := by
  nth_rw 2 [←Nat.pow_one x]
  rw [←Nat.pow_add, Nat.add_sub_of_le (by linarith [hy])]

lemma shifted_decomposition_eq {offset : Fin 8} {x1 x2 : ℕ} :
    (x1 / 2 ^ offset.val + x2 % 2 ^ offset.val * 2 ^ (8 - offset.val)) * 256 =
    (2^offset.val * (x1 / 2^offset.val) + (x2 % 2^offset.val) * 256) * 2^(8 - offset.val) := by
  ring_nf
  simp only [Nat.add_left_inj]
  rw [Nat.mul_assoc, ←Nat.pow_add, Nat.add_sub_of_le (by linarith [offset.is_lt])]
  rfl

lemma shifted_decomposition_eq' {offset : Fin 8} {x1 x2 i : ℕ} (hi : i > 0) :
    (x1 / 2 ^ offset.val + x2 % 2 ^ offset.val * 2 ^ (8 - offset.val)) * 256^i =
    (2^offset.val * (x1 / 2^offset.val) + (x2 % 2^offset.val) * 256) * 2^(8 - offset.val) * 256^(i-1) := by
  rw [Nat.pow_minus_one_mul hi, ←Nat.mul_assoc, shifted_decomposition_eq]

lemma shifted_decomposition_eq'' {offset : Fin 8} {x1 x2 i : ℕ} (hi : i > 0) :
    (x1 / 2 ^ offset.val + x2 % 2 ^ offset.val * 2 ^ (8 - offset.val)) * 256^i =
    (2^offset.val * (x1 / 2^offset.val) * 2^(8 - offset.val) * 256^(i-1) +
    (x2 % 2^offset.val) * 2^(8 - offset.val) * 256^i) := by
  rw [shifted_decomposition_eq' hi]
  ring_nf
  rw [Nat.mul_assoc _ _ 256, Nat.mul_comm _ 256, Nat.pow_minus_one_mul hi]


theorem rotation64_bits_soundness (offset : Fin 8) {
      x0 x1 x2 x3 x4 x5 x6 x7
      y0 y1 y2 y3 y4 y5 y6 y7
      x0_l x1_l x2_l x3_l x4_l x5_l x6_l x7_l
      x0_h x1_h x2_h x3_h x4_h x5_h x6_h x7_h : F p
    }
    (h_x0 : x0.val < 256)
    (h_x1 : x1.val < 256)
    (h_x2 : x2.val < 256)
    (h_x3 : x3.val < 256)
    (h_x4 : x4.val < 256)
    (h_x5 : x5.val < 256)
    (h_x6 : x6.val < 256)
    (h_x7 : x7.val < 256)
    (h_x0_l : x0_l.val = x0.val % 2 ^ offset.val)
    (h_x0_h : x0_h.val = x0.val / 2 ^ offset.val)
    (h_x1_l : x1_l.val = x1.val % 2 ^ offset.val)
    (h_x1_h : x1_h.val = x1.val / 2 ^ offset.val)
    (h_x2_l : x2_l.val = x2.val % 2 ^ offset.val)
    (h_x2_h : x2_h.val = x2.val / 2 ^ offset.val)
    (h_x3_l : x3_l.val = x3.val % 2 ^ offset.val)
    (h_x3_h : x3_h.val = x3.val / 2 ^ offset.val)
    (h_x4_l : x4_l.val = x4.val % 2 ^ offset.val)
    (h_x4_h : x4_h.val = x4.val / 2 ^ offset.val)
    (h_x5_l : x5_l.val = x5.val % 2 ^ offset.val)
    (h_x5_h : x5_h.val = x5.val / 2 ^ offset.val)
    (h_x6_l : x6_l.val = x6.val % 2 ^ offset.val)
    (h_x6_h : x6_h.val = x6.val / 2 ^ offset.val)
    (h_x7_l : x7_l.val = x7.val % 2 ^ offset.val)
    (h_x7_h : x7_h.val = x7.val / 2 ^ offset.val)
    (eq0 : x1_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x0_h + -y0 = 0)
    (eq1 : x2_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x1_h + -y1 = 0)
    (eq2 : x3_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x2_h + -y2 = 0)
    (eq3 : x4_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x3_h + -y3 = 0)
    (eq4 : x5_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x4_h + -y4 = 0)
    (eq5 : x6_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x5_h + -y5 = 0)
    (eq6 : x7_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x6_h + -y6 = 0)
    (eq7 : x0_l * ↑(2 ^ (8 - offset.val) % 256 : ℕ) + x7_h + -y7 = 0):
    let x_val := x0.val + x1.val * 256 + x2.val * 256 ^ 2 + x3.val * 256 ^ 3 + x4.val * 256 ^ 4 +
      x5.val * 256 ^ 5 + x6.val * 256 ^ 6 + x7.val * 256 ^ 7
    let y_val := y0.val + y1.val * 256 + y2.val * 256 ^ 2 + y3.val * 256 ^ 3 + y4.val * 256 ^ 4 +
      y5.val * 256 ^ 5 + y6.val * 256 ^ 6 + y7.val * 256 ^ 7
    y_val = (x_val) % 2 ^ (offset.val % 64) * 2 ^ (64 - offset.val % 64) + (x_val) / 2 ^ (offset.val % 64) := by

  rw [add_comm (_ * _)] at eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7

  have x0_l_byte : x0_l.val < 256 := by rw [h_x0_l]; apply Nat.mod_lt_of_lt; assumption
  have x0_h_byte : x0_h.val < 256 := by rw [h_x0_h]; apply Nat.div_lt_of_lt; assumption
  have x1_l_byte : x1_l.val < 256 := by rw [h_x1_l]; apply Nat.mod_lt_of_lt; assumption
  have x1_h_byte : x1_h.val < 256 := by rw [h_x1_h]; apply Nat.div_lt_of_lt; assumption
  have x2_l_byte : x2_l.val < 256 := by rw [h_x2_l]; apply Nat.mod_lt_of_lt; assumption
  have x2_h_byte : x2_h.val < 256 := by rw [h_x2_h]; apply Nat.div_lt_of_lt; assumption
  have x3_l_byte : x3_l.val < 256 := by rw [h_x3_l]; apply Nat.mod_lt_of_lt; assumption
  have x3_h_byte : x3_h.val < 256 := by rw [h_x3_h]; apply Nat.div_lt_of_lt; assumption
  have x4_l_byte : x4_l.val < 256 := by rw [h_x4_l]; apply Nat.mod_lt_of_lt; assumption
  have x4_h_byte : x4_h.val < 256 := by rw [h_x4_h]; apply Nat.div_lt_of_lt; assumption
  have x5_l_byte : x5_l.val < 256 := by rw [h_x5_l]; apply Nat.mod_lt_of_lt; assumption
  have x5_h_byte : x5_h.val < 256 := by rw [h_x5_h]; apply Nat.div_lt_of_lt; assumption
  have x6_l_byte : x6_l.val < 256 := by rw [h_x6_l]; apply Nat.mod_lt_of_lt; assumption
  have x6_h_byte : x6_h.val < 256 := by rw [h_x6_h]; apply Nat.div_lt_of_lt; assumption
  have x7_l_byte : x7_l.val < 256 := by rw [h_x7_l]; apply Nat.mod_lt_of_lt; assumption
  have x7_h_byte : x7_h.val < 256 := by rw [h_x7_h]; apply Nat.div_lt_of_lt; assumption

  have two_power_byte : ZMod.val ((2 ^ (8 - offset.val) % 256 : ℕ) : F p) < 256 := by
    rw [ZMod.val_natCast]
    apply Nat.mod_lt_of_lt
    apply Nat.mod_lt
    linarith

  have two_power_val : ZMod.val ((2 ^ (8 - offset.val) % 256 : ℕ) : F p) = 2 ^ (8 - offset.val) % 256 := by
    rw [ZMod.val_natCast]
    apply Nat.mod_eq_of_lt
    have h : 2 ^ (8 - offset.val) % 256 < 256 := by apply Nat.mod_lt; linarith
    linarith [h, p_large_enough.elim]

  replace eq0 := byte_decomposition_lift x0_h_byte x1_l_byte two_power_byte eq0
  replace eq1 := byte_decomposition_lift x1_h_byte x2_l_byte two_power_byte eq1
  replace eq2 := byte_decomposition_lift x2_h_byte x3_l_byte two_power_byte eq2
  replace eq3 := byte_decomposition_lift x3_h_byte x4_l_byte two_power_byte eq3
  replace eq4 := byte_decomposition_lift x4_h_byte x5_l_byte two_power_byte eq4
  replace eq5 := byte_decomposition_lift x5_h_byte x6_l_byte two_power_byte eq5
  replace eq6 := byte_decomposition_lift x6_h_byte x7_l_byte two_power_byte eq6
  replace eq7 := byte_decomposition_lift x7_h_byte x0_l_byte two_power_byte eq7

  simp only [two_power_val, ZMod.val_natCast] at eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7
  rw [eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7]
  dsimp only

  have offset_mod_64 : offset.val % 64 = offset.val := by
    apply Nat.mod_eq_of_lt
    linarith [offset.is_lt]

  simp [h_x0_l, h_x0_h, h_x1_l, h_x1_h, h_x2_l, h_x2_h, h_x3_l, h_x3_h,
    h_x4_l, h_x4_h, h_x5_l, h_x5_h, h_x6_l, h_x6_h, h_x7_l, h_x7_h,
    offset_mod_64, -Nat.reducePow]

  set x0 := x0.val
  set x1 := x1.val
  set x2 := x2.val
  set x3 := x3.val
  set x4 := x4.val
  set x5 := x5.val
  set x6 := x6.val
  set x7 := x7.val

  have h_mod : (x0 + x1 * 256 + x2 * 256 ^ 2 + x3 * 256 ^ 3 + x4 * 256 ^ 4 + x5 * 256 ^ 5 + x6 * 256 ^ 6 + x7 * 256 ^ 7) %
        2 ^ offset.val = x0 % 2 ^ offset.val := by
    simp only [pow_one, Nat.add_mod, dvd_refl, Nat.mod_mod_of_dvd, gt_iff_lt, Nat.ofNat_pos,
      mul_mod_256_off, add_zero]
    rw [←Nat.pow_one 256, Nat.mod_mod, Nat.mod_mod, mul_mod_256_off _ _ _ (by linarith)]
    simp only [add_zero, dvd_refl, Nat.mod_mod_of_dvd]

  rw [h_mod]
  if h_offset : offset = 0 then
    rw [h_offset]
    simp only [Fin.isValue, Fin.val_zero, pow_zero, Nat.div_one, Nat.mod_one, tsub_zero,
      Nat.reducePow, Nat.mod_self, mul_zero, add_zero, zero_mul, zero_add, Nat.add_left_inj]
  else
    rw [two_off_eq_mod _ (by simp only [ne_eq, Fin.val_eq_zero_iff, Fin.isValue, h_offset,
      not_false_eq_true])]
    rw [shifted_decomposition_eq]
    repeat rw [shifted_decomposition_eq'' (by linarith)]
    simp only [Nat.add_assoc, Nat.add_one_sub_one, pow_one]


    repeat sorry

theorem soundness (offset : Fin 8) : Soundness (F p) (elaborated offset) assumptions (spec offset) := by
  intro i0 env ⟨x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩ ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_input x_normalized h_holds

  dsimp only [circuit_norm, elaborated, rot64_bits, U64.witness, var_from_offset] at h_holds
  simp only [subcircuit_norm, U64.AssertNormalized.assumptions, U64.AssertNormalized.circuit, circuit_norm] at h_holds
  simp only [U64ByteDecomposition.circuit, U64ByteDecomposition.elaborated, add_zero,
    ElaboratedCircuit.local_length, ElaboratedCircuit.output, eval, from_elements, size, to_vars,
    to_elements, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
    U64ByteDecomposition.assumptions, Expression.eval, U64ByteDecomposition.spec,
    U64.AssertNormalized.spec, Vector.mapRange_succ, Vector.mapRange_zero, Vector.push_mk,
    Nat.reduceAdd, List.push_toArray, List.nil_append, List.cons_append, forall_const,
    Expression.eval.eq_1] at h_holds

  simp only [assumptions] at x_normalized
  simp [circuit_norm, spec, rot_right64, eval, elaborated, var_from_offset, Vector.mapRange]

  rw [
    show Expression.eval env x0_var = x0 by injections h_input,
    show Expression.eval env x1_var = x1 by injections h_input,
    show Expression.eval env x2_var = x2 by injections h_input,
    show Expression.eval env x3_var = x3 by injections h_input,
    show Expression.eval env x4_var = x4 by injections h_input,
    show Expression.eval env x5_var = x5 by injections h_input,
    show Expression.eval env x6_var = x6 by injections h_input,
    show Expression.eval env x7_var = x7 by injections h_input,
  ] at h_holds
  simp only [and_assoc] at h_holds
  obtain ⟨h_decomposition, y_normalized, eq0, eq1, eq2, eq3, eq4, eq5, eq6, eq7⟩ := h_holds
  specialize h_decomposition x_normalized
  obtain ⟨h_x0_l, h_x0_h, h_x1_l, h_x1_h, h_x2_l, h_x2_h, h_x3_l, h_x3_h,
    h_x4_l, h_x4_h, h_x5_l, h_x5_h, h_x6_l, h_x6_h, h_x7_l, h_x7_h⟩ := h_decomposition
  simp only [U64.value, y_normalized, and_true]

  dsimp [U64.is_normalized] at x_normalized
  obtain ⟨h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7⟩ := x_normalized
  rw [rotation64_bits_soundness offset
    h_x0 h_x1 h_x2 h_x3 h_x4 h_x5 h_x6 h_x7
    h_x0_l h_x0_h h_x1_l h_x1_h h_x2_l h_x2_h h_x3_l h_x3_h
    h_x4_l h_x4_h h_x5_l h_x5_h h_x6_l h_x6_h h_x7_l h_x7_h
    eq0 eq1 eq2 eq3 eq4 eq5 eq6 eq7]


theorem completeness (offset : Fin 8) : Completeness (F p) (elaborated offset) assumptions := by
  sorry

def circuit (offset : Fin 8) : FormalCircuit (F p) U64 U64 := {
  elaborated offset with
  assumptions := assumptions
  spec := spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.Rotation64Bits
