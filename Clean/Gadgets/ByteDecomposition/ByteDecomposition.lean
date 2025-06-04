import Clean.Utils.Primes
import Clean.Utils.Field
import Clean.Gadgets.TwoPowerLookup
import Clean.Gadgets.ByteDecomposition.Theorems
import Init.Data.Nat.Div.Basic

namespace Gadgets.ByteDecomposition
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

open Gadgets.ByteDecomposition.Theorems (byte_decomposition_lift)

-- TODO: is there a better way?
instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

structure Outputs (F : Type) where
  low : F
  high : F

instance instProvableTypeOutputs : ProvableType Outputs where
  size := 2
  to_elements x := #v[x.low, x.high]
  from_elements v :=
    let ⟨ .mk [low, high], _ ⟩ := v
    ⟨ low, high ⟩

/--
  Decompose a byte into a low and a high part.
  The low part is the least significant `offset` bits,
  and the high part is the most significant `8 - offset` bits.
-/
def byte_decomposition (offset : Fin 8) (x : Var field (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let x : Expression (F p) := x
  let two_power : ℕ := (2 : ℕ)^offset.val

  let low ← witness fun env =>
    FieldUtils.mod (env x) ⟨two_power, by dsimp only [two_power]; simp⟩ (by
      dsimp only [two_power, PNat.mk_coe, two_power];
      have h : 2^offset.val < 2^8 := by
        apply Nat.pow_lt_pow_of_lt
        simp only [Nat.one_lt_ofNat, two_power]
        simp only [Fin.is_lt, two_power]
      linarith [p_large_enough.elim]
    )

  let high ← witness fun env => FieldUtils.floordiv (env x) (2^offset.val)

  lookup (TwoPowerLookup.lookup (offset.castSucc) low)
  lookup (TwoPowerLookup.lookup (8 - offset.castSucc) high)

  assert_zero (low + high * ((2 : ℕ)^offset.val : F p) - x)

  return ⟨ low, high ⟩

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
  intro i0 env x_var x h_input x_byte h_holds
  simp only [id_eq, circuit_norm] at h_input
  simp [circuit_norm, elaborated, byte_decomposition, TwoPowerLookup.lookup, TwoPowerLookup.equiv, h_input] at h_holds
  simp [circuit_norm, spec, eval, Outputs, elaborated, var_from_offset, h_input]
  obtain ⟨⟨low_lt, high_lt⟩, c⟩ := h_holds
  simp_all [h_input]
  set low := env.get i0
  set high := env.get (i0 + 1)

  exact Theorems.soundness offset x low high x_byte low_lt high_lt c



theorem completeness (offset : Fin 8) : Completeness (F p) (elaborated offset) assumptions := by
  rintro i0 env x_var henv x h_eval as
  simp only [assumptions] at as
  simp [circuit_norm, byte_decomposition, elaborated] at henv
  simp only [field, id] at x

  let ⟨ h0, h1 ⟩ := henv

  simp only [id_eq, ↓eval_field] at h_eval
  simp [circuit_norm, byte_decomposition, elaborated, ByteLookup, TwoPowerLookup.lookup]
  rw [TwoPowerLookup.equiv, TwoPowerLookup.equiv, h_eval, h0, h1]
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

namespace Gadgets.U32ByteDecomposition
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

structure Outputs (F : Type) where
  low : U32 F
  high : U32 F

instance : ProvableStruct Outputs where
  components := [U32, U32]
  to_components := fun { low, high } => .cons low (.cons high .nil)
  from_components := fun (.cons low (.cons high .nil)) => { low, high }

/--
  Decompose every limb of a u32 into a low and a high part.
  The low part is the least significant `offset` bits, and the high part is the most significant `8 - offset` bits.
-/
def u32_byte_decomposition (offset : Fin 8) (x : Var U32 (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x0, x1, x2, x3⟩ := x

  let ⟨x0_l, x0_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit offset) x0
  let ⟨x1_l, x1_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit offset) x1
  let ⟨x2_l, x2_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit offset) x2
  let ⟨x3_l, x3_h⟩ ← subcircuit (Gadgets.ByteDecomposition.circuit offset) x3

  let low := U32.mk x0_l x1_l x2_l x3_l
  let high := U32.mk x0_h x1_h x2_h x3_h

  return ⟨ low, high ⟩

def assumptions (x : U32 (F p)) := x.is_normalized

def spec (offset : Fin 8) (input : U32 (F p)) (out: Outputs (F p)) :=
  let ⟨x0, x1, x2, x3⟩ := input
  let ⟨⟨x0_l, x1_l, x2_l, x3_l⟩,
        ⟨x0_h, x1_h, x2_h, x3_h⟩⟩ := out
  x0_l.val = x0.val % (2^offset.val) ∧ x0_h.val = x0.val / (2^offset.val) ∧
  x1_l.val = x1.val % (2^offset.val) ∧ x1_h.val = x1.val / (2^offset.val) ∧
  x2_l.val = x2.val % (2^offset.val) ∧ x2_h.val = x2.val / (2^offset.val) ∧
  x3_l.val = x3.val % (2^offset.val) ∧ x3_h.val = x3.val / (2^offset.val)

-- #eval! (u32_byte_decomposition (p:=p_babybear) 0) default |>.operations.local_length
-- #eval! (u32_byte_decomposition (p:=p_babybear) 0) default |>.output
def elaborated (offset : Fin 8) : ElaboratedCircuit (F p) U32 Outputs where
  main := u32_byte_decomposition offset
  local_length _ := 8
  output _ i0 := {
    low := ⟨var ⟨i0 + 0⟩, var ⟨i0 + 2⟩, var ⟨i0 + 4⟩, var ⟨i0 + 6⟩⟩,
    high := ⟨var ⟨i0 + 1⟩, var ⟨i0 + 3⟩, var ⟨i0 + 5⟩, var ⟨i0 + 7⟩⟩
  }

theorem soundness (offset : Fin 8) : Soundness (F p) (elaborated offset) assumptions (spec offset) := by
  intro i0 env x_var ⟨x0, x1, x2, x3⟩ h_input ⟨x_byte, offset_positive⟩ h_holds
  simp [circuit_norm, elaborated, u32_byte_decomposition, ByteLookup, ByteTable.equiv, h_input] at h_holds
  simp [subcircuit_norm, ByteDecomposition.circuit, ByteDecomposition.elaborated,
    ByteDecomposition.assumptions, ByteDecomposition.spec, eval, circuit_norm, var_from_offset, Vector.mapRange] at h_holds

  simp [assumptions, U32.is_normalized] at x_byte
  simp [eval, circuit_norm] at h_input

  simp only [spec, ↓ProvableStruct.eval_eq_eval_struct, ProvableStruct.eval, from_components,
    ProvableStruct.eval.go, eval, from_elements, size, to_vars, to_elements, elaborated, add_zero,
    ElaboratedCircuit.output, Vector.map_mk, List.map_toArray, List.map_cons, Expression.eval,
    List.map_nil, Vector.mapRange]
  obtain ⟨h0, h1, h2, h3⟩ := h_input
  simp [h0, h1, h2, h3, and_assoc, var_from_offset] at h_holds
  clear h0 h1 h2 h3

  obtain ⟨ h0, h1, h2, h3 ⟩ := h_holds
  simp_all only [gt_iff_lt, Fin.val_pos_iff, forall_const, and_self]

theorem completeness (offset : Fin 8) : Completeness (F p) (elaborated offset) assumptions := by
  rintro i0 env ⟨x0_var, x1_var, x2_var, x3_var⟩ henv ⟨x0, x1, x2, x3⟩ h_eval as
  simp only [assumptions] at as
  sorry

def circuit (offset : Fin 8) : FormalCircuit (F p) U32 Outputs := {
  elaborated offset with
  main := u32_byte_decomposition offset
  assumptions
  spec := spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.U32ByteDecomposition
