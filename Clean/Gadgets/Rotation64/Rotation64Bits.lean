import Clean.Types.U64
import Clean.Circuit.SubCircuit
import Clean.Gadgets.Rotation64.Theorems
import Clean.Circuit.Provable

namespace Gadgets.Rotation64Bits
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Bitwise (rot_right64)
open Gadgets.Rotation64.Theorems (rotation64_bits_soundness)
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
  local_length_eq := by
    intros
    simp only [rot64_bits]
    rfl


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
