import Clean.Circuit
import Clean.Utils.Primes
import Clean.Utils.Field
import Clean.Types.U64
import Clean.Gadgets.Xor.ByteXorTable

section
variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.Xor64
open Gadgets.Xor

structure Inputs (F : Type) where
  x: U64 F
  y: U64 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var U64 (F p))  := do
  let ⟨x, y⟩ := input
  let xorByte (a b : Expression (F p)) : Witgen.FExpr (F p) :=
    (a.val ^^^ b.val).toField
  let z ← witness (U64.mk
    (xorByte x.x0 y.x0) (xorByte x.x1 y.x1) (xorByte x.x2 y.x2) (xorByte x.x3 y.x3)
    (xorByte x.x4 y.x4) (xorByte x.x5 y.x5) (xorByte x.x6 y.x6) (xorByte x.x7 y.x7))

  lookup ByteXorTable (x.x0, y.x0, z.x0)
  lookup ByteXorTable (x.x1, y.x1, z.x1)
  lookup ByteXorTable (x.x2, y.x2, z.x2)
  lookup ByteXorTable (x.x3, y.x3, z.x3)
  lookup ByteXorTable (x.x4, y.x4, z.x4)
  lookup ByteXorTable (x.x5, y.x5, z.x5)
  lookup ByteXorTable (x.x6, y.x6, z.x6)
  lookup ByteXorTable (x.x7, y.x7, z.x7)
  return z

def Assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.Normalized ∧ y.Normalized

def Spec (input : Inputs (F p)) (z : U64 (F p)) :=
  let ⟨x, y⟩ := input
  z.value = x.value ^^^ y.value ∧ z.Normalized

@[reducible]
instance elaborated : ElaboratedCircuit (F p) Inputs U64 main := by
  elaborate_circuit

omit [Fact (Nat.Prime p)] p_large_enough in
theorem soundness_to_u64 {x y z : U64 (F p)}
  (x_norm : x.Normalized) (y_norm : y.Normalized)
  (h_eq :
    z.x0.val = x.x0.val ^^^ y.x0.val ∧
    z.x1.val = x.x1.val ^^^ y.x1.val ∧
    z.x2.val = x.x2.val ^^^ y.x2.val ∧
    z.x3.val = x.x3.val ^^^ y.x3.val ∧
    z.x4.val = x.x4.val ^^^ y.x4.val ∧
    z.x5.val = x.x5.val ^^^ y.x5.val ∧
    z.x6.val = x.x6.val ^^^ y.x6.val ∧
    z.x7.val = x.x7.val ^^^ y.x7.val) : Spec { x, y } z := by
  simp only [Spec]
  have ⟨ hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7 ⟩ := x_norm
  have ⟨ hy0, hy1, hy2, hy3, hy4, hy5, hy6, hy7 ⟩ := y_norm

  have z_norm : z.Normalized := by
    simp only [U64.Normalized, h_eq]
    exact ⟨ Nat.xor_lt_two_pow (n:=8) hx0 hy0, Nat.xor_lt_two_pow (n:=8) hx1 hy1,
      Nat.xor_lt_two_pow (n:=8) hx2 hy2, Nat.xor_lt_two_pow (n:=8) hx3 hy3,
      Nat.xor_lt_two_pow (n:=8) hx4 hy4, Nat.xor_lt_two_pow (n:=8) hx5 hy5,
      Nat.xor_lt_two_pow (n:=8) hx6 hy6, Nat.xor_lt_two_pow (n:=8) hx7 hy7 ⟩

  suffices z.value = x.value ^^^ y.value from ⟨ this, z_norm ⟩
  simp only [U64.value_xor_horner, x_norm, y_norm, z_norm, h_eq, xor_mul_two_pow]
  ac_rfl

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [ByteXorTable]
  rcases input_x with ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩
  rcases input_y with ⟨ y0, y1, y2, y3, y4, y5, y6, y7 ⟩
  simp only [circuit_norm, explicit_provable_type, U64.mk.injEq] at h_input
  obtain ⟨ x_norm, y_norm ⟩ := h_assumptions
  simp only [h_input, circuit_norm, explicit_provable_type] at h_holds
  apply soundness_to_u64 x_norm y_norm
  simp only [circuit_norm, explicit_provable_type]
  simp [h_holds]

lemma xor_val {x y : F p} (hx : x.val < 256) (hy : y.val < 256) :
    (x.val ^^^ y.val : F p).val = x.val ^^^ y.val := by
  apply FieldUtils.val_lt_p
  have h_byte : x.val ^^^ y.val < 256 := Nat.xor_lt_two_pow (n:=8) hx hy
  linarith [p_large_enough.elim]

theorem completeness : Completeness (F p) main Assumptions := by
  intro i0 env input_var h_env input h_input as
  let ⟨⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩, ⟨ y0, y1, y2, y3, y4, y5, y6, y7 ⟩⟩ := input
  simp only [circuit_norm, explicit_provable_type, Inputs.mk.injEq, U64.mk.injEq] at h_input
  simp only [Assumptions, circuit_norm, U64.Normalized] at as
  simp only [h_input, circuit_norm, main, ByteXorTable, Fin.forall_iff] at h_env ⊢
  simp only [circuit_norm, explicit_provable_type] at h_env ⊢
  have h_env0 : env.get i0 = ↑(ZMod.val x0 ^^^ ZMod.val y0) := by simpa [circuit_norm, h_input] using h_env 0
  simp_all [circuit_norm, xor_val]

def circuit : FormalCircuit (F p) Inputs U64 where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness
end Gadgets.Xor64
