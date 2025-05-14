import Clean.Gadgets.Rotation64.Theorems
import Clean.Utils.Primes
import Clean.Utils.Field

namespace Gadgets.ByteDecomposition
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

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
  The low part is the least significant `offset` bits, and the high part is the most significant `8 - offset` bits.
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

  lookup (ByteLookup low)
  lookup (ByteLookup high)

  assert_zero (low + high * ((2 : ℕ)^offset.val : F p) - x)

  return ⟨ low, high ⟩

def assumptions (x : field (F p)) := x.val < 256

def spec (offset : Fin 8) (x : field (F p)) (out: Outputs (F p)) :=
  let ⟨low, high⟩ := out
  x.val = low.val + high.val * 2^offset.val ∧
  low.val < 2^offset.val ∧
  high.val < 2^(8 - offset.val)

def elaborated (offset : Fin 8) : ElaboratedCircuit (F p) field (Var Outputs (F p)) where
  main := byte_decomposition offset
  local_length _ := 2
  output _ i0 := var_from_offset Outputs i0

-- TODO: remove when updating to new mathlib
theorem Nat.mod_lt_of_lt {a b c : Nat} (h : a < c) : a % b < c :=
  Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

lemma val_two : (2 : F p).val = 2 := FieldUtils.val_lt_p 2 (by linarith [p_large_enough.elim])

theorem byte_decomposition_lift (offset : Fin 8) (x low high : F p)
    (h_low : low.val < 256) (h_high : high.val < 256)
    (h : low + high * (2^offset.val) + -x = 0) :
    x.val = low.val + high.val * (2^offset.val) := by
  have pow_val_field : ZMod.val (2 : F p) ^ offset.val < 256 := by
    rw [val_two]
    fin_cases offset
    repeat simp

  have pow_val_field : ZMod.val (2 : F p) ^ offset.val < p := by
    linarith [p_large_enough.elim]

  have pow_val : (2 ^ offset.val) < 2^16 := by
    apply Nat.pow_lt_pow_of_lt
    · simp only [Nat.one_lt_ofNat]
    · linarith [offset.is_lt]

  have pow_val' : (2 ^ offset.val) < p := by
    linarith [p_large_enough.elim]

  rw [add_neg_eq_iff_eq_add, zero_add] at h
  apply_fun ZMod.val at h
  rw [ZMod.val_add, ZMod.val_mul, ZMod.val_pow pow_val_field, Nat.mul_mod] at h
  rw [val_two, Nat.mod_eq_of_lt pow_val'] at h

  set low := low.val
  set high := high.val

  have high_val : high % p = high := by
    apply Nat.mod_eq_of_lt
    linarith [p_large_enough.elim]

  have mul_val : high * (2^offset.val) < 2^16 := by
    rw [show 2^16 = 256 * 2^8 by rfl]
    apply Nat.mul_lt_mul_of_lt_of_lt
    · linarith
    · apply Nat.pow_lt_pow_of_lt
      simp only [Nat.one_lt_ofNat]
      linarith [offset.is_lt]

  have mul_val' : high * (2^offset.val) < p := by
    linarith [p_large_enough.elim]

  rw [high_val, Nat.mod_eq_of_lt mul_val'] at h

  have sum_val : low + high * (2^offset.val) < 2^8 + 2^16 := by
    apply Nat.add_lt_add
    repeat linarith

  have sum_val' : low + high * (2^offset.val) < p := by
    linarith [p_large_enough.elim]

  rw [Nat.mod_eq_of_lt sum_val'] at h
  simp only [h]

theorem soundness (offset : Fin 8) : Soundness (F p) (circuit := elaborated offset) assumptions (spec offset) := by
  intro i0 env x_var x h_input x_byte h_holds
  simp only [id_eq, circuit_norm] at h_input
  simp [circuit_norm, elaborated, byte_decomposition, ByteLookup, ByteTable.equiv, h_input] at h_holds
  simp [circuit_norm, spec, eval, Outputs, elaborated, var_from_offset, h_input]
  obtain ⟨⟨low_byte, high_byte⟩, c⟩ := h_holds
  simp only [byte_decomposition_lift offset _ _ _ low_byte high_byte c, true_and]
  sorry



theorem completeness (offset : Fin 8) : Completeness (F p) (circuit := elaborated offset) Outputs assumptions := by
  rintro i0 env x_var henv x h_eval as
  simp only [assumptions] at as
  simp [circuit_norm, byte_decomposition, elaborated] at henv
  simp only [field, id] at x

  let ⟨ h0, h1 ⟩ := henv

  simp only [id_eq, ↓eval_field] at h_eval
  simp [circuit_norm, byte_decomposition, elaborated, ByteLookup]
  rw [ByteTable.equiv, ByteTable.equiv, h_eval, h0, h1]

  if zero_off : offset = 0 then
    simp [Fin.isValue, zero_off, lt_self_iff_false, ↓reduceIte, FieldUtils.floordiv,
      Fin.val_zero, pow_zero, PNat.val_ofNat, Nat.div_one, mul_one, zero_add, FieldUtils.mod]
    simp only [h_eval, Nat.mod_one, FieldUtils.nat_to_field_zero, ZMod.val_zero, Nat.ofNat_pos,
      FieldUtils.nat_to_field_of_val_eq_iff, as, and_self, zero_add, add_neg_cancel]
  else
    have off_ge_zero : offset > 0 := by
      simp only [Fin.isValue, gt_iff_lt, Fin.pos_iff_ne_zero', ne_eq, zero_off, not_false_eq_true]
    simp only [FieldUtils.mod, h_eval, PNat.mk_coe, FieldUtils.floordiv, PNat.pow_coe,
      PNat.val_ofNat]

    have x_lt : x.val < p := by linarith [as, p_large_enough.elim]

    have h : ZMod.val (2 : F p) ^ offset.val < 256 := by
      rw [val_two]
      fin_cases offset
      repeat simp

    have h' : ZMod.val (2 : F p) ^ offset.val < p := by
      linarith [p_large_enough.elim]

    constructor
    · repeat rw [FieldUtils.val_of_nat_to_field_eq]

      have h_mod : x.val % (2^offset.val) < 256 := by
        apply Nat.mod_lt_of_lt
        exact as

      have h_div : x.val / (2^offset.val) < 256 := by
        apply Nat.div_lt_of_lt_mul
        fin_cases offset
        repeat linarith

      simp only [h_mod, h_div, and_self]

    · apply_fun ZMod.val
      · repeat rw [ZMod.val_add]

        rw [ZMod.val_mul, ZMod.val_pow h', ZMod.neg_val]
        repeat rw [FieldUtils.val_of_nat_to_field_eq]

        simp only [Nat.add_mod_mod, Nat.mod_add_mod, ZMod.val_zero, val_two]
        set bin_pow := 2^offset.val
        if h: x = 0 then
          simp [h]
        else
          have x_ne_zero : NeZero x.val := by
            rw [neZero_iff]
            simp only [ne_eq, ZMod.val_eq_zero, h, not_false_eq_true]

          simp only [h, ↓reduceIte]
          rw [Nat.mod_add_div', Nat.add_mod]
          rw [Nat.self_sub_mod, Nat.mod_eq_of_lt x_lt, Nat.add_sub_of_le (by linarith)]
          simp only [Nat.mod_self]

      · apply ZMod.val_injective

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
  x0.val = x0_l.val + x0_h.val * 2^(offset.val) ∧
  x0_l.val < 2^offset.val ∧ x0_h.val < 2^(8 - offset.val) ∧
  x1.val = x1_l.val + x1_h.val * 2^(offset.val) ∧
  x1_l.val < 2^offset.val ∧ x1_h.val < 2^(8 - offset.val) ∧
  x2.val = x2_l.val + x2_h.val * 2^(offset.val) ∧
  x2_l.val < 2^offset.val ∧ x2_h.val < 2^(8 - offset.val) ∧
  x3.val = x3_l.val + x3_h.val * 2^(offset.val) ∧
  x3_l.val < 2^offset.val ∧ x3_h.val < 2^(8 - offset.val) ∧
  x4.val = x4_l.val + x4_h.val * 2^(offset.val) ∧
  x4_l.val < 2^offset.val ∧ x4_h.val < 2^(8 - offset.val) ∧
  x5.val = x5_l.val + x5_h.val * 2^(offset.val) ∧
  x5_l.val < 2^offset.val ∧ x5_h.val < 2^(8 - offset.val) ∧
  x6.val = x6_l.val + x6_h.val * 2^(offset.val) ∧
  x6_l.val < 2^offset.val ∧ x6_h.val < 2^(8 - offset.val) ∧
  x7.val = x7_l.val + x7_h.val * 2^(offset.val) ∧
  x7_l.val < 2^offset.val ∧ x7_h.val < 2^(8 - offset.val)

-- #eval! (u64_byte_decomposition (p:=p_babybear) 0) default |>.operations.local_length
-- #eval! (u64_byte_decomposition (p:=p_babybear) 0) default |>.output
def elaborated (offset : Fin 8) : ElaboratedCircuit (F p) U64 (Var Outputs (F p)) where
  main := u64_byte_decomposition offset
  local_length _ := 16
  output _ i0 := {
    low := ⟨var ⟨i0 + 0⟩, var ⟨i0 + 2⟩, var ⟨i0 + 4⟩, var ⟨i0 + 6⟩, var ⟨i0 + 8⟩, var ⟨i0 + 10⟩, var ⟨i0 + 12⟩, var ⟨i0 + 14⟩⟩,
    high := ⟨var ⟨i0 + 1⟩, var ⟨i0 + 3⟩, var ⟨i0 + 5⟩, var ⟨i0 + 7⟩, var ⟨i0 + 9⟩, var ⟨i0 + 11⟩, var ⟨i0 + 13⟩, var ⟨i0 + 15⟩⟩
  }

theorem soundness (offset : Fin 8) : Soundness (F p) (circuit := elaborated offset) assumptions (spec offset) := by
  intro i0 env x_var ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ h_input x_byte h_holds
  simp [circuit_norm, elaborated, u64_byte_decomposition, ByteLookup, ByteTable.equiv, h_input] at h_holds
  simp [subcircuit_norm, ByteDecomposition.circuit, ByteDecomposition.elaborated,
    ByteDecomposition.assumptions, ByteDecomposition.spec, eval, circuit_norm] at h_holds

  simp [assumptions, U64.is_normalized] at x_byte
  simp [eval, circuit_norm] at h_input

  simp only [spec, ↓ProvableStruct.eval_eq_eval_struct, ProvableStruct.eval, from_components,
    ProvableStruct.eval.go, eval, from_elements, size, to_vars, to_elements, elaborated, add_zero,
    ElaboratedCircuit.output, Vector.map_mk, List.map_toArray, List.map_cons, Expression.eval,
    List.map_nil]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h_input
  simp [h0, h1, h2, h3, h4, h5, h6, h7, and_assoc] at h_holds
  clear h0 h1 h2 h3 h4 h5 h6 h7

  obtain ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩ := h_holds
  simp_all only [Nat.reducePow, Nat.reduceAdd, gt_iff_lt, forall_const]
  sorry


theorem completeness (offset : Fin 8) : Completeness (F p) (circuit := elaborated offset) Outputs assumptions := by
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
