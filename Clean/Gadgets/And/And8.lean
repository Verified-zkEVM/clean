import Clean.Circuit.Basic
import Clean.Types.U64
import Clean.Gadgets.Xor.ByteXorTable
import Clean.Utils.Primes

variable {p : ℕ} [Fact p.Prime] [p_large_enough: Fact (p > 512)]

namespace Gadgets.And.And8
open Gadgets.Xor (ByteXorLookup ByteXorTable)
open FieldUtils

structure Inputs (F : Type) where
  x: F
  y: F

instance : ProvableStruct Inputs where
  components := [field, field]
  to_components := fun { x, y } => .cons x (.cons y .nil)
  from_components := fun (.cons x (.cons y .nil)) => { x, y }

def assumptions (input : Inputs (F p)) :=
  let ⟨x, y⟩ := input
  x.val < 256 ∧ y.val < 256

def spec (input : Inputs (F p)) (z : F p) :=
  let ⟨x, y⟩ := input
  z.val = Nat.land x.val y.val

def main (input : Var Inputs (F p)) : Circuit (F p) (Expression (F p)) := do
  let ⟨x, y⟩ := input
  let z ← witness (fun eval => Nat.xor (eval x).val (eval y).val)
  lookup (ByteXorLookup x y z)
  return (x + y - z) / 2

-- main theorem about AND that justifies the circuit
theorem and_times_two_add_xor {x y : ℕ} (hx : x < 256) (hy : y < 256) : 2 * (x &&& y) + (x ^^^ y) = x + y := by
  -- proof strategy: prove a UInt16 version of the identity using `bv_decide`,
  -- and show that the UInt16 identity is the same as the Nat version since everything is small enough
  let x16 := x.toUInt16
  let y16 := y.toUInt16
  have h_u16 : (2 * (x16 &&& y16) + (x16 ^^^ y16)).toNat = (x16 + y16).toNat := by
    apply congrArg UInt16.toNat
    bv_decide

  have hx16 : x.toUInt16.toNat = x := UInt16.toNat_ofNat_of_lt (by linarith)
  have hy16 : y.toUInt16.toNat = y := UInt16.toNat_ofNat_of_lt (by linarith)

  have h_mod_2_to_16 : (2 * (x &&& y) + (x ^^^ y)) % 2^16 = (x + y) % 2^16 := by
    rw [←hx16, ←hy16]
    simp only [x16, y16] at h_u16
    simpa using h_u16

  have h_and_byte : x &&& y < 256 := Nat.and_lt_two_pow (n:=8) x hy
  have h_xor_byte : x ^^^ y < 256 := Nat.xor_lt_two_pow (n:=8) hx hy
  have h_lhs : 2 * (x &&& y) + (x ^^^ y) < 2^16 := by linarith
  have h_rhs : x + y < 2^16 := by linarith
  rw [Nat.mod_eq_of_lt h_lhs, Nat.mod_eq_of_lt h_rhs] at h_mod_2_to_16
  exact h_mod_2_to_16

-- corollary that we also need
theorem xor_le_add {x y : ℕ} (hx : x < 256) (hy : y < 256) : x ^^^ y ≤ x + y := by
  rw [←and_times_two_add_xor hx hy]; linarith

-- some helper lemmas about 2
lemma val_two : (2 : F p).val = 2 := val_lt_p 2 (by linarith [p_large_enough.elim])

lemma two_non_zero : (2 : F p) ≠ 0 := by
  apply_fun ZMod.val
  rw [val_two, ZMod.val_zero]
  trivial

-- TODO where is this in mathlib? seems like an obvious theorem to have
theorem mul_left_inj {F: Type} [Field F] : ∀ {x y z : F}, x ≠ 0 → x * y = x * z → y = z := by
  intro x y z hx h
  rw [←one_mul y, ←Field.mul_inv_cancel x hx, mul_comm x, mul_assoc, h,
    ←mul_assoc, mul_comm _ x, Field.mul_inv_cancel x hx, one_mul]

instance elaborated : ElaboratedCircuit (F p) Inputs (Var field (F p)) where
  main
  local_length _ := 1
  output := fun ⟨ x, y ⟩ i => (x + y - var ⟨i⟩) / 2

theorem soundness : Soundness (F p) (circuit:=elaborated) assumptions spec := by
  intro i env ⟨ x_var, y_var ⟩ ⟨ x, y ⟩ h_input _ h_holds
  simp_all only [circuit_norm, main, assumptions, spec, ByteXorLookup]
  simp only [Inputs.mk.injEq] at h_input
  obtain ⟨ hx, hy ⟩ := h_input
  rw [ByteXorTable.equiv, hx, hy] at h_holds
  rw [hx, hy]
  clear hx hy
  obtain ⟨ _, hx_byte, hy_byte, h_xor ⟩ := h_holds
  set z := env.get i
  change z.val = x.val ^^^ y.val at h_xor
  set w := (2 : F p)⁻¹ * (x + y + -z)
  show w.val = x.val &&& y.val

  -- it's easier to prove something about 2 * w, since we can cancel the 2⁻¹
  have two_and_field : 2 * w = x + y - z := by
    rw [←mul_assoc, Field.mul_inv_cancel _ two_non_zero]; ring

  have x_y_val : (x + y).val = x.val + y.val := by field_to_nat
  have z_lt : z.val ≤ (x + y).val := by
    rw [h_xor, x_y_val]
    exact xor_le_add hx_byte hy_byte
  have x_y_z_val : (x + y - z).val = x.val + y.val - z.val := by
    rw [ZMod.val_sub z_lt, x_y_val]

  have two_and : (2 * w).val = 2 * (x.val &&& y.val) := by
    rw [two_and_field, x_y_z_val, h_xor, ←and_times_two_add_xor hx_byte hy_byte, Nat.add_sub_cancel]

  clear two_and_field x_y_val x_y_z_val h_xor z_lt

  -- rewrite the goal to the form `(2 * w).val = (2 * v).val`,
  -- where we can prove `(2 * v).val = 2 * v.val`
  have and_byte : x.val &&& y.val < 256 := Nat.and_lt_two_pow (n:=8) x.val hy_byte
  have p_large := p_large_enough.elim

  let v : F p := nat_to_field (x.val &&& y.val) (by linarith)
  have v_val_eq : v.val = x.val &&& y.val := nat_to_field_eq v rfl
  rw [←v_val_eq] at two_and ⊢
  apply congrArg ZMod.val
  apply mul_left_inj (F:=F p) two_non_zero
  apply ext
  rw [two_and]

  -- this is now easy
  have rhs_lt : (2 : F p).val * v.val < p := by rw [v_val_eq, val_two]; linarith
  rw [ZMod.val_mul_of_lt rhs_lt, val_two]

theorem completeness : Completeness (F p) field assumptions := by
  intro i env ⟨ x_var, y_var ⟩ h_env ⟨ x, y ⟩ h_input h_assumptions
  simp_all only [circuit_norm, main, assumptions, spec, ByteXorLookup]
  simp only [Inputs.mk.injEq] at h_input
  obtain ⟨ hx, hy ⟩ := h_input
  rw [ByteXorTable.equiv, hx, hy]
  set z := env.get i

  obtain ⟨ hx_byte, hy_byte ⟩ := h_assumptions
  suffices h_xor : z.val = x.val ^^^ y.val from ⟨ trivial, hx_byte, hy_byte, h_xor ⟩

  specialize h_env 0
  rw [h_env, hx, hy]
  apply ZMod.val_natCast_of_lt
  have z_lt : x.val.xor y.val < 256 := Nat.xor_lt_two_pow (n:=8) hx_byte hy_byte
  linarith [p_large_enough.elim]

def circuit : FormalCircuit (F p) Inputs field :=
  { assumptions, spec, soundness, completeness }

end Gadgets.And.And8
