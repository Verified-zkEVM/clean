import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic
import Clean.Utils.Primes
import Clean.Utils.Vector
import Clean.Circuit.Expression
import Clean.Circuit.Provable
import Clean.Circuit.Basic
import Clean.Utils.Field
import Clean.Types.U64
import Clean.Gadgets.Xor.ByteXorTable

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.Xor
structure Inputs (F : Type) where
  x: U64 F
  y: U64 F

instance : ProvableStruct Inputs where
  components := [U64, U64]
  to_components := fun { x, y } => .cons x (.cons y .nil)
  from_components := fun (.cons x (.cons y .nil)) => { x, y }

def xor_u64 (input : Var Inputs (F p)) : Circuit (F p) (Var U64 (F p))  := do
  let ⟨x, y⟩ := input
  let z ← ProvableType.witness (fun env =>
    let z0 := (env x.x0).val ^^^ (env y.x0).val
    let z1 := (env x.x1).val ^^^ (env y.x1).val
    let z2 := (env x.x2).val ^^^ (env y.x2).val
    let z3 := (env x.x3).val ^^^ (env y.x3).val
    let z4 := (env x.x4).val ^^^ (env y.x4).val
    let z5 := (env x.x5).val ^^^ (env y.x5).val
    let z6 := (env x.x6).val ^^^ (env y.x6).val
    let z7 := (env x.x7).val ^^^ (env y.x7).val
    U64.mk z0 z1 z2 z3 z4 z5 z6 z7)

  lookup (ByteXorLookup x.x0 y.x0 z.x0)
  lookup (ByteXorLookup x.x1 y.x1 z.x1)
  lookup (ByteXorLookup x.x2 y.x2 z.x2)
  lookup (ByteXorLookup x.x3 y.x3 z.x3)
  lookup (ByteXorLookup x.x4 y.x4 z.x4)
  lookup (ByteXorLookup x.x5 y.x5 z.x5)
  lookup (ByteXorLookup x.x6 y.x6 z.x6)
  lookup (ByteXorLookup x.x7 y.x7 z.x7)
  return z

def assumptions (input: Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.is_normalized ∧ y.is_normalized

def spec (input: Inputs (F p)) (z : U64 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = x.value ^^^ y.value ∧ z.is_normalized

instance elaborated : ElaboratedCircuit (F p) Inputs U64 where
  main := xor_u64
  local_length _ := 8
  output _ i0 := var_from_offset U64 i0

omit [Fact (Nat.Prime p)] p_large_enough in
theorem soundness_to_u64 {x y z : U64 (F p)}
  (x_norm : x.is_normalized) (y_norm : y.is_normalized)
  (h_eq :
    z.x0.val = x.x0.val ^^^ y.x0.val ∧
    z.x1.val = x.x1.val ^^^ y.x1.val ∧
    z.x2.val = x.x2.val ^^^ y.x2.val ∧
    z.x3.val = x.x3.val ^^^ y.x3.val ∧
    z.x4.val = x.x4.val ^^^ y.x4.val ∧
    z.x5.val = x.x5.val ^^^ y.x5.val ∧
    z.x6.val = x.x6.val ^^^ y.x6.val ∧
    z.x7.val = x.x7.val ^^^ y.x7.val) : spec { x, y } z := by
  simp only [spec]
  have ⟨ hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7 ⟩ := x_norm
  have ⟨ hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7 ⟩ := y_norm

  have z_norm : z.is_normalized := by
    simp only [U64.is_normalized, h_eq]
    exact ⟨ Nat.xor_lt_two_pow (n:=8) hx0 hy0, Nat.xor_lt_two_pow (n:=8) hx1 hy1,
      Nat.xor_lt_two_pow (n:=8) hx2 hy2, Nat.xor_lt_two_pow (n:=8) hx3 hy3,
      Nat.xor_lt_two_pow (n:=8) hx4 hy4, Nat.xor_lt_two_pow (n:=8) hx5 hy5,
      Nat.xor_lt_two_pow (n:=8) hx6 hy6, Nat.xor_lt_two_pow (n:=8) hx7 hy7 ⟩

  suffices z.value = x.value ^^^ y.value from ⟨ this, z_norm ⟩
  simp only [U64.value_xor_horner, x_norm, y_norm, z_norm, h_eq, Bitwise.xor_mul_two_pow]
  ac_rfl

theorem soundness : Soundness (F p) elaborated assumptions spec := by
  intro i0 env input_var input h_input h_as h_holds

  let ⟨⟨ x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩,
       ⟨ y0_var, y1_var, y2_var, y3_var, y4_var, y5_var, y6_var, y7_var ⟩⟩ := input_var
  let ⟨⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩,
       ⟨ y0, y1, y2, y3, y4, y5, y6, y7 ⟩⟩ := input

  simp only [circuit_norm, eval, Inputs.mk.injEq, U64.mk.injEq] at h_input
  obtain ⟨ hx, hy ⟩ := h_input
  obtain ⟨ h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7 ⟩ := hx
  obtain ⟨ h_y0, h_y1, h_y2, h_y3, h_y4, h_y5, h_y6, h_y7 ⟩ := hy

  simp only [circuit_norm, assumptions] at h_as
  obtain ⟨ x_norm, y_norm ⟩ := h_as

  dsimp only [circuit_norm, xor_u64, ByteXorLookup] at h_holds
  simp only [circuit_norm, add_zero, List.push_toArray, List.nil_append, List.cons_append,
    List.map_toArray, List.map_cons, List.map_nil] at h_holds
  simp only [h_x0, h_y0, h_x1, h_y1, h_x2, h_y2, h_x3, h_y3, h_x4, h_y4, h_x5, h_y5,
    h_x6, h_y6, h_x7, h_y7] at h_holds
  repeat rw [ByteXorTable.equiv] at h_holds

  apply soundness_to_u64 x_norm y_norm
  simp only [circuit_norm, var_from_offset, eval]
  simp [h_holds]

lemma xor_cast {x y : F p} (hx : x.val < 256) (hy : y.val < 256) :
  (x.val ^^^ y.val : F p).val = x.val ^^^ y.val := by
  apply FieldUtils.val_lt_p
  have h_byte : x.val ^^^ y.val < 256 := Nat.xor_lt_two_pow (n:=8) hx hy
  linarith [p_large_enough.elim]

theorem completeness : Completeness (F p) elaborated assumptions := by
  intro i0 env input_var h_env input h_input as
  let ⟨⟨ x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩,
       ⟨ y0_var, y1_var, y2_var, y3_var, y4_var, y5_var, y6_var, y7_var ⟩⟩ := input_var
  let ⟨⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩,
       ⟨ y0, y1, y2, y3, y4, y5, y6, y7 ⟩⟩ := input
  simp only [circuit_norm, eval, Inputs.mk.injEq, U64.mk.injEq] at h_input
  obtain ⟨ hx, hy ⟩ := h_input
  obtain ⟨ h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7 ⟩ := hx
  obtain ⟨ h_y0, h_y1, h_y2, h_y3, h_y4, h_y5, h_y6, h_y7 ⟩ := hy

  simp only [assumptions, circuit_norm, U64.is_normalized] at as
  obtain ⟨ x_bytes, y_bytes ⟩ := as
  obtain ⟨ x0_byte, x1_byte, x2_byte, x3_byte, x4_byte, x5_byte, x6_byte, x7_byte ⟩ := x_bytes
  obtain ⟨ y0_byte, y1_byte, y2_byte, y3_byte, y4_byte, y5_byte, y6_byte, y7_byte ⟩ := y_bytes

  dsimp only [circuit_norm, xor_u64, ByteXorLookup] at h_env
  simp [circuit_norm] at h_env
  dsimp only [circuit_norm, xor_u64, ByteXorLookup]
  simp only [circuit_norm, add_zero, List.push_toArray, List.nil_append, List.cons_append,
    List.map_toArray, List.map_cons, List.map_nil]
  simp only [h_x0, h_y0, h_x1, h_y1, h_x2, h_y2, h_x3, h_y3, h_x4, h_y4, h_x5, h_y5,
    h_x6, h_y6, h_x7, h_y7] at h_env ⊢
  repeat rw [ByteXorTable.equiv]
  have h_env0 := by let h := h_env 0; simp at h; exact h
  have h_env1 := by let h := h_env 1; simp at h; exact h
  have h_env2 := by let h := h_env 2; simp at h; exact h
  have h_env3 := by let h := h_env 3; simp [show ↑(3: Fin 8) = 3 from rfl] at h; exact h
  have h_env4 := by let h := h_env 4; simp [show ↑(4: Fin 8) = 4 from rfl] at h; exact h
  have h_env5 := by let h := h_env 5; simp [show ↑(5: Fin 8) = 5 from rfl] at h; exact h
  have h_env6 := by let h := h_env 6; simp [show ↑(6: Fin 8) = 6 from rfl] at h; exact h
  have h_env7 := by let h := h_env 7; simp [show ↑(7: Fin 8) = 7 from rfl] at h; exact h
  rw [h_env0, h_env1, h_env2, h_env3, h_env4, h_env5, h_env6, h_env7]
  rw [xor_cast x0_byte y0_byte, xor_cast x1_byte y1_byte,
      xor_cast x2_byte y2_byte, xor_cast x3_byte y3_byte,
      xor_cast x4_byte y4_byte, xor_cast x5_byte y5_byte,
      xor_cast x6_byte y6_byte, xor_cast x7_byte y7_byte]
  simp only [x0_byte, y0_byte, x1_byte, y1_byte, x2_byte, y2_byte,
    x3_byte, y3_byte, x4_byte, y4_byte, x5_byte, y5_byte,
    x6_byte, y6_byte, x7_byte, y7_byte, and_true]

def circuit : FormalCircuit (F p) Inputs U64 where
  assumptions
  spec
  soundness
  completeness
end Gadgets.Xor
