import Clean.Gadgets.Rotation64.Theorems
import Clean.Utils.Primes
import Clean.Utils.Field
import Clean.Gadgets.TwoPowerLookup

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

  lookup (TwoPowerLookup.lookup (offset) low)
  lookup (TwoPowerLookup.lookup (8 - offset) high)

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
  simp [circuit_norm, elaborated, byte_decomposition, TwoPowerLookup.lookup, TwoPowerLookup.equiv, h_input] at h_holds
  simp [circuit_norm, spec, eval, Outputs, elaborated, var_from_offset, h_input]
  obtain ⟨⟨low_lt, high_lt⟩, c⟩ := h_holds
  simp_all [h_input]
  simp only [assumptions] at x_byte
  set low := env.get i0
  set high := env.get (i0 + 1)
  have two_power_lt : 2^offset.val < 2^8 := Nat.pow_lt_pow_of_lt (by linarith) offset.is_lt
  have two_power_lt' : 2^(-offset).val < 2^8 := Nat.pow_lt_pow_of_lt (by linarith) (by simp only [Fin.is_lt])
  have low_byte : low.val < 256 := by linarith
  have high_byte : high.val < 256 := by linarith
  have h := byte_decomposition_lift offset _ _ _ low_byte high_byte c

  set low_b := UInt32.ofNat low.val
  set high_b := UInt32.ofNat high.val
  set x_b := UInt32.ofNat x.val

  -- The heavy lifting is done by using a SAT solver
  have h_decomposition_bv (base : UInt32) :
      base < 256 →
      low_b < base →
      high_b < 256 / base →
      x_b < 256 → x_b = low_b + high_b * base →
      low_b = x_b % base ∧ high_b = x_b / base := by
    bv_decide

  -- now it is left to prove that the bv variant is equivalent
  -- to the field variant of the theorem
  have two_power_lt_bv : UInt32.ofNat (2^offset.val) < 256 := by
    apply Nat.mod_lt_of_lt
    have : (UInt32.toBitVec 256).toNat = 256 := by simp only [UInt32.toBitVec_ofNat,
      BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    linarith

  have low_b_lt : low_b < UInt32.ofNat (2^offset.val) := by
    simp [low_b]
    simp [UInt32.ofNat]
    sorry

  have high_b_lt : high_b < 256 / UInt32.ofNat (2^offset.val) := by
    sorry

  have x_lt : x_b < 256 := by sorry

  have eq_holds_bv : x_b = low_b + high_b * UInt32.ofNat (2^offset.val) := by sorry

  specialize h_decomposition_bv (UInt32.ofNat (2^offset.val))
    two_power_lt_bv low_b_lt high_b_lt x_lt eq_holds_bv

  obtain ⟨h1, h2⟩ := h_decomposition_bv

  have two_power_mod : (2^offset.val % 2 ^ 32) = 2^offset.val := by
    rw [Nat.mod_eq_iff_lt]
    linarith
    simp only [Nat.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, low_b, x_b]

  have low_mod : low.val % 2^32 = low.val := by
    rw [Nat.mod_eq_iff_lt]
    linarith
    simp only [Nat.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, low_b, x_b]

  have high_mod : high.val % 2^32 = high.val := by
    rw [Nat.mod_eq_iff_lt]
    linarith
    simp only [Nat.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, low_b, x_b]

  have x_mod : x.val % 2^32 = x.val := by
    rw [Nat.mod_eq_iff_lt]
    linarith
    simp only [Nat.reducePow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, low_b, x_b]

  constructor
  · apply_fun UInt32.toNat at h1
    simp only [UInt32.toNat_ofNat, UInt32.toNat_mod, low_b, x_b] at h1
    rw [low_mod, x_mod, two_power_mod] at h1
    assumption
  · apply_fun UInt32.toNat at h2
    simp only [UInt32.toNat_ofNat, UInt32.toNat_div, high_b, x_b, low_b] at h2
    rw [high_mod, x_mod, two_power_mod] at h2
    assumption


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
