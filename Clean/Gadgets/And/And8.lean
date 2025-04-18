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
  z.val = x.val &&& y.val

def main (input : Var Inputs (F p)) : Circuit (F p) (Expression (F p)) := do
  let ⟨x, y⟩ := input
  let and ← witness (fun eval => (eval x).val &&& (eval y).val)
  -- we prove AND correct using an XOR lookup and the following identity:
  let xor := x + y - 2 * and
  lookup (ByteXorLookup x y xor)
  return and

-- AND / XOR identity that justifies the circuit

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

-- corollaries that we also need

theorem xor_le_add {x y : ℕ} (hx : x < 256) (hy : y < 256) : x ^^^ y ≤ x + y := by
  rw [←and_times_two_add_xor hx hy]; linarith

theorem two_and_le_add {x y : ℕ} (hx : x < 256) (hy : y < 256) : 2 * (x &&& y) ≤ x + y := by
  rw [←and_times_two_add_xor hx hy]; linarith

-- some helper lemmas about 2
lemma val_two : (2 : F p).val = 2 := val_lt_p 2 (by linarith [p_large_enough.elim])

lemma two_non_zero : (2 : F p) ≠ 0 := by
  apply_fun ZMod.val
  rw [val_two, ZMod.val_zero]
  trivial

instance elaborated : ElaboratedCircuit (F p) Inputs (Var field (F p)) where
  main
  local_length _ := 1
  output _ i := var ⟨i⟩

theorem soundness : Soundness (F p) (circuit:=elaborated) assumptions spec := by
  intro i env ⟨ x_var, y_var ⟩ ⟨ x, y ⟩ h_input _ h_holds
  simp_all only [circuit_norm, main, assumptions, spec, ByteXorLookup]
  simp only [Inputs.mk.injEq] at h_input
  obtain ⟨ hx, hy ⟩ := h_input
  rw [ByteXorTable.equiv, hx, hy] at h_holds
  clear hx hy
  obtain ⟨ _, hx_byte, hy_byte, h_xor ⟩ := h_holds
  set w := env.get i
  set z := x + y + -(2 * w)
  show w.val = x.val &&& y.val

  -- it's easier to prove something about 2 * w since it features in the constraint
  have two_and_field : 2 * w = x + y - z := by ring

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
  rw [←mul_right_inj' two_non_zero]
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
  set w := env.get i
  let z := x + y + -(2 * w)

  obtain ⟨ hx_byte, hy_byte ⟩ := h_assumptions
  suffices h_xor : (x + y + -(2 * w)).val = x.val ^^^ y.val from ⟨ trivial, hx_byte, hy_byte, h_xor ⟩

  -- now it's pretty much the soundness proof in reverse
  simp only [forall_const, true_and] at h_env
  have and_byte : x.val &&& y.val < 256 := Nat.and_lt_two_pow (n:=8) x.val hy_byte
  have p_large := p_large_enough.elim
  have and_lt : x.val &&& y.val < p := by linarith
  rw [hx, hy, nat_to_field_eq_natcast and_lt] at h_env
  have h_and : w.val = x.val &&& y.val := nat_to_field_eq w h_env
  clear h_env

  have two_and_val : (2 * w).val = 2 * (x.val &&& y.val) := by
    rw [ZMod.val_mul_of_lt, val_two, h_and]
    rw [val_two]
    linarith

  have x_y_val : (x + y).val = x.val + y.val := by field_to_nat
  have two_and_lt : (2 * w).val ≤ (x + y).val := by
    rw [two_and_val, x_y_val]
    exact two_and_le_add hx_byte hy_byte

  rw [←sub_eq_add_neg, ZMod.val_sub two_and_lt, x_y_val, two_and_val,
    ←and_times_two_add_xor hx_byte hy_byte, add_comm, Nat.add_sub_cancel]

def circuit : FormalCircuit (F p) Inputs field :=
  { assumptions, spec, soundness, completeness }

end Gadgets.And.And8
