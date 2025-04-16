import Clean.Gadgets.Rotation64.Theorems
import Clean.Utils.Primes
import Clean.Utils.Field

namespace Gadgets.ByteDecomposition
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

structure Inputs (F : Type) where
  x: F

instance instProvableTypeInputs : ProvableType Inputs where
  size := 1
  to_elements x := #v[x.x]
  from_elements v := ⟨ v.get 0 ⟩

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
def byte_decomposition (offset : Fin 8) (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x⟩ := input
  let two_power : ℕ := (2 : ℕ)^offset.val

  let low ← witness fun env =>
    if offset > 0 then
      FieldUtils.mod (env x) ⟨two_power, by dsimp only [two_power]; simp⟩ (by
        dsimp only [two_power, PNat.mk_coe, two_power];
        have h : 2^offset.val < 2^8 := by
          apply Nat.pow_lt_pow_of_lt
          simp only [Nat.one_lt_ofNat, two_power]
          simp only [Fin.is_lt, two_power]
        linarith [p_large_enough.elim]
      )
    else 0

  let high ← witness fun env => FieldUtils.floordiv (env x) (2^offset.val)

  assert_zero (low + high * ((2 : ℕ)^offset.val : F p) - x)

  return ⟨ low, high ⟩

def assumptions (input : Inputs (F p)) := input.x.val < 256

def spec (offset : Fin 8) (input : Inputs (F p)) (out: Outputs (F p)) :=
  let ⟨x⟩ := input
  let ⟨low, high⟩ := out
  x.val = low.val + high.val * 2^(offset.val)


def elaborated (offset : Fin 8) : ElaboratedCircuit (F p) Inputs (Var Outputs (F p)) where
  main := byte_decomposition offset
  local_length _ := 2
  output _ i0 := var_from_offset Outputs i0

theorem soundness (offset : Fin 8) : Soundness (F p) (circuit := elaborated offset) assumptions (spec offset) := by
  sorry

theorem completeness (offset : Fin 8) : Completeness (F p) (circuit := elaborated offset) Outputs assumptions := by
  rintro i0 env ⟨x_var⟩ henv ⟨ x ⟩ h_eval as
  simp only [assumptions] at as
  simp [circuit_norm, byte_decomposition, elaborated] at henv

  let h0 := henv 0
  simp at h0
  let h1 := henv 1
  simp at h1

  simp [eval, circuit_norm] at h_eval

  simp [circuit_norm, byte_decomposition, elaborated]
  rw [h_eval, h0, h1]

  if zero_off : offset = 0 then
    simp only [Fin.isValue, zero_off, lt_self_iff_false, ↓reduceIte, FieldUtils.floordiv,
      Fin.val_zero, pow_zero, PNat.val_ofNat, Nat.div_one, mul_one, zero_add]
    rw [FieldUtils.nat_to_field_of_val_eq_iff, h_eval]
    ring
  else
    have off_ge_zero : offset > 0 := by
      simp only [Fin.isValue, gt_iff_lt, Fin.pos_iff_ne_zero', ne_eq, zero_off, not_false_eq_true]
    simp [FieldUtils.mod, h_eval, FieldUtils.floordiv, off_ge_zero]
    apply_fun ZMod.val
    · repeat rw [ZMod.val_add]
      have val_two : (2 : F p).val = 2 := FieldUtils.val_lt_p 2 (by linarith [p_large_enough.elim])
      have h : ZMod.val (2 : F p) ^ offset.val < p := by
        sorry

      rw [ZMod.val_mul, ZMod.val_pow h, ZMod.neg_val]
      repeat rw [FieldUtils.val_of_nat_to_field_eq]

      simp only [Nat.add_mod_mod, Nat.mod_add_mod, ZMod.val_zero, val_two]
      set bin_pow := 2^offset.val
      if h: x = 0 then
        simp [h]
      else
        simp [h]
        set x := x.val

        sorry

    · apply ZMod.val_injective

def circuit (offset : Fin 8) : FormalCircuit (F p) Inputs Outputs := {
  elaborated offset with
  main := byte_decomposition offset
  assumptions
  spec := spec offset
  soundness := soundness offset
  completeness := completeness offset
}
end Gadgets.ByteDecomposition
