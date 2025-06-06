import Clean.Types.U32
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Rotation32.Theorems
import Clean.Gadgets.Rotation32.Rotation32Bytes
import Clean.Gadgets.Rotation32.ByteRotationTable
import Clean.Gadgets.ByteDecomposition.ByteDecomposition
import Clean.Circuit.Provable

namespace Gadgets.Rotation32Bits
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Bitwise (rot_right32)

/--
  Rotate the 32-bit integer by `offset` bits
-/
def rot32_bits (offset : Fin 8) (x : Var U32 (F p)) : Circuit (F p) (Var U32 (F p)) := do

  let two_power : F p := 2^offset.val

  let ⟨low, high⟩ ← subcircuit (Gadgets.U32ByteDecomposition.circuit offset) x
  let ⟨x0_l, x1_l, x2_l, x3_l⟩ := low
  let ⟨x0_h, x1_h, x2_h, x3_h⟩ := high

  let ⟨y0, y1, y2, y3⟩ ← U32.witness fun _env => U32.mk 0 0 0 0

  assert_zero (x1_l * two_power + x0_h - y0)
  assert_zero (x2_l * two_power + x1_h - y1)
  assert_zero (x3_l * two_power + x2_h - y2)
  assert_zero (x0_l * two_power + x3_h - y3)

  return ⟨y0, y1, y2, y3⟩

instance lawful (off : Fin 8) : ConstantLawfulCircuits (F := (F p)) (rot32_bits off) := by infer_constant_lawful_circuits

def assumptions (input : U32 (F p)) := input.is_normalized

def spec (offset : Fin 8) (x : U32 (F p)) (y: U32 (F p)) :=
  y.value = rot_right32 x.value offset.val
  ∧ y.is_normalized

-- #eval! (rot32_bits (p:=p_babybear) 0) default |>.operations.local_length
-- #eval! (rot32_bits (p:=p_babybear) 0) default |>.output
def elaborated (off : Fin 8) : ElaboratedCircuit (F p) U32 U32 where
  main := rot32_bits off
  local_length _ := 12
  output _inputs i0 := var_from_offset U32 (i0 + 8)
  initial_offset_eq := by
    intros
    simp only [rot32_bits]
    rfl
  local_length_eq := by
    intros
    simp only [rot32_bits]
    rfl

theorem rotation32_bits_soundness (offset : Fin 8) {
      x0 x1 x2 x3
      y0 y1 y2 y3
      x0_l x1_l x2_l x3_l
      x0_h x1_h x2_h x3_h : F p
    }
    (h_x0_l : x0_l.val = x0.val % 2 ^ offset.val)
    (h_x0_h : x0_h.val = x0.val / 2 ^ offset.val)
    (h_x1_l : x1_l.val = x1.val % 2 ^ offset.val)
    (h_x1_h : x1_h.val = x1.val / 2 ^ offset.val)
    (h_x2_l : x2_l.val = x2.val % 2 ^ offset.val)
    (h_x2_h : x2_h.val = x2.val / 2 ^ offset.val)
    (h_x3_l : x3_l.val = x3.val % 2 ^ offset.val)
    (h_x3_h : x3_h.val = x3.val / 2 ^ offset.val)
    (eq0 : x1_l * 2 ^ offset.val + (x0_h - y0) = 0)
    (eq1 : x2_l * 2 ^ offset.val + (x1_h - y1) = 0)
    (eq2 : x3_l * 2 ^ offset.val + (x2_h - y2) = 0)
    (eq3 : x0_l * 2 ^ offset.val + (x3_h - y3) = 0) :
    let x_val := x0.val + x1.val * 256 + x2.val * 256^2 + x3.val * 256^3
    let y_val := y0.val + y1.val * 256 + y2.val * 256^2 + y3.val * 256^3
    y_val = (x_val) % 2 ^ (offset.val % 32) * 2 ^ (32 - offset.val % 32) + (x_val) / 2 ^ (offset.val % 32) := by

  rw [←add_sub_assoc, sub_eq_add_neg] at eq0 eq1 eq2 eq3
  sorry

theorem soundness (offset : Fin 8) : Soundness (F p) (elaborated offset) assumptions (spec offset) := by
  intro i0 env ⟨ x0_var, x1_var, x2_var, x3_var ⟩ ⟨ x0, x1, x2, x3 ⟩ h_input x_normalized h_holds

  dsimp only [circuit_norm, elaborated, rot32_bits, U32.witness, var_from_offset] at h_holds
  simp only [subcircuit_norm, U32.AssertNormalized.assumptions, U32.AssertNormalized.circuit, circuit_norm] at h_holds
  simp only [U32ByteDecomposition.circuit, U32ByteDecomposition.elaborated, add_zero,
    ElaboratedCircuit.local_length, ElaboratedCircuit.output, eval, from_elements, size, to_vars,
    to_elements, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
    U32ByteDecomposition.assumptions, Expression.eval, U32ByteDecomposition.spec,
    U32.AssertNormalized.spec, Vector.mapRange_succ, Vector.mapRange_zero, Vector.push_mk,
    Nat.reduceAdd, List.push_toArray, List.nil_append, List.cons_append, forall_const,
    Expression.eval.eq_1] at h_holds

  simp only [assumptions] at x_normalized
  simp [circuit_norm, spec, rot_right32, eval, elaborated, var_from_offset, Vector.mapRange]
  ring_nf at h_input h_holds ⊢

  rw [
    show Expression.eval env x0_var = x0 by injections h_input,
    show Expression.eval env x1_var = x1 by injections h_input,
    show Expression.eval env x2_var = x2 by injections h_input,
    show Expression.eval env x3_var = x3 by injections h_input,
  ] at h_holds
  simp only [and_assoc] at h_holds
  -- TODO: clarify why there's a difference between 32 and 64 bit version
  -- for y_normalized. At some point above, h_holds seems to be rewritten differently...
  obtain ⟨h_decomposition, y_normalized, eq0, eq1, eq2, eq3⟩ := h_holds
  specialize h_decomposition x_normalized
  obtain ⟨h_x0_l, h_x0_h, h_x1_l, h_x1_h, h_x2_l, h_x2_h, h_x3_l, h_x3_h⟩ := h_decomposition
  simp only [U32.value, y_normalized, and_true]

  -- rw [rotation32_bits_soundness offset
  --   h_x0_l h_x0_h h_x1_l h_x1_h h_x2_l h_x2_h h_x3_l h_x3_h
  --   eq0 eq1 eq2 eq3]

theorem completeness (offset : Fin 8) : Completeness (F p) (elaborated offset) assumptions := by
  sorry

def circuit (offset : Fin 8) : FormalCircuit (F p) U32 U32 := {
  elaborated offset with
  assumptions := assumptions
  spec := spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.Rotation32Bits
