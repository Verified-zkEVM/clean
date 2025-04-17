import Clean.Gadgets.Rotation64.Theorems
import Clean.Utils.Primes
import Clean.Utils.Field

namespace Gadgets.ByteDecomposition
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

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
  x.val = low.val + high.val * 2^(offset.val)

def elaborated (offset : Fin 8) : ElaboratedCircuit (F p) field (Var Outputs (F p)) where
  main := byte_decomposition offset
  local_length _ := 2
  output _ i0 := var_from_offset Outputs i0

-- TODO: remove when updating to new mathlib
theorem Nat.mod_lt_of_lt {a b c : Nat} (h : a < c) : a % b < c :=
  Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

theorem soundness (offset : Fin 8) : Soundness (F p) (circuit := elaborated offset) assumptions (spec offset) := by
  intro i0 env x_var x h_input x_byte h_holds
  simp only [id_eq, circuit_norm] at h_input
  simp [circuit_norm, elaborated, byte_decomposition, ByteLookup, ByteTable.equiv, h_input] at h_holds
  simp [circuit_norm, spec, eval, Outputs, elaborated, var_from_offset, h_input]

  set low := env.get i0
  set high := env.get (i0 + 1)
  obtain ⟨⟨low_byte, high_byte⟩, c⟩ := h_holds


  have val_two : (2 : F p).val = 2 := FieldUtils.val_lt_p 2 (by linarith [p_large_enough.elim])

  have h : ZMod.val (2 : F p) ^ offset.val < 256 := by
    rw [val_two]
    fin_cases offset
    repeat simp

  have h' : ZMod.val (2 : F p) ^ offset.val < p := by
    linarith [p_large_enough.elim]


  rw [add_neg_eq_iff_eq_add, zero_add] at c
  apply_fun ZMod.val at c
  rw [ZMod.val_add, ZMod.val_mul, ZMod.val_pow h', Nat.mul_mod] at c


  sorry

theorem completeness (offset : Fin 8) : Completeness (F p) (circuit := elaborated offset) Outputs assumptions := by
  rintro i0 env x_var henv x h_eval as
  simp only [assumptions] at as
  simp [circuit_norm, byte_decomposition, elaborated] at henv
  simp only [field, id] at x

  let h0 := henv 0
  simp only [Fin.isValue, Fin.val_zero, add_zero, gt_iff_lt, List.getElem_cons_zero] at h0
  let h1 := henv 1
  simp only [Fin.isValue, Fin.val_one, gt_iff_lt, List.getElem_cons_succ,
    List.getElem_cons_zero] at h1

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
    have val_two : (2 : F p).val = 2 := FieldUtils.val_lt_p 2 (by linarith [p_large_enough.elim])

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
