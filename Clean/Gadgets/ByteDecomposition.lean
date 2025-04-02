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

def circuit (off : Fin 8) : FormalCircuit (F p) Inputs Outputs where
  main := byte_decomposition off
  assumptions := assumptions
  spec := spec off
  local_length := 2
  output _ i0 := ⟨ var ⟨i0⟩, var ⟨i0 +1⟩ ⟩
  soundness := by sorry
  completeness := by
    rintro i0 env ⟨ x_var ⟩ henv ⟨ x ⟩ h_eval as
    simp only [assumptions] at as
    simp [circuit_norm, byte_decomposition] at henv

    let h0 := henv 0
    simp at h0
    let h1 := henv 1
    simp at h1

    simp [eval, circuit_norm] at h_eval

    simp [circuit_norm, byte_decomposition]
    rw [h_eval, h0, h1]

    fin_cases off
    · simp only [Fin.isValue, Fin.zero_eta, lt_self_iff_false, ↓reduceIte, FieldUtils.floordiv,
      pow_zero, PNat.val_ofNat, Nat.div_one, mul_one, zero_add]
      rw [FieldUtils.nat_to_field_of_val_eq_iff, h_eval]
      ring
    · simp [FieldUtils.mod, h_eval, FieldUtils.floordiv]
      apply_fun ZMod.val
      · repeat rw [ZMod.val_add]
        rw [ZMod.val_mul]
        repeat rw [FieldUtils.val_of_nat_to_field_eq]

        sorry

      · apply ZMod.val_injective
    repeat sorry
end Gadgets.ByteDecomposition
