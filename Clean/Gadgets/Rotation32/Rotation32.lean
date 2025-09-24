import Clean.Types.U32
import Clean.Circuit.Subcircuit
import Clean.Utils.Rotation
import Clean.Gadgets.Rotation32.Rotation32Bytes
import Clean.Gadgets.Rotation32.Rotation32Bits
import Clean.Circuit.Provable

namespace Gadgets.Rotation32
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Utils.Rotation (rotRight32_composition)

/--
  Rotate the 32-bit integer by `offset` bits
-/
def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (offset : Fin 32) (x : Var U32 (F p)) : Circuit sentences (Var U32 (F p)) := do
  let byte_offset : Fin 4 := ⟨ offset.val / 8, by omega ⟩
  let bit_offset : Fin 8 := ⟨ offset.val % 8, by omega ⟩

  -- rotation is performed by combining a bit and a byte rotation
  let byte_rotated ← Rotation32Bytes.circuit order byte_offset x
  Rotation32Bits.circuit order bit_offset byte_rotated

def Assumptions (input : U32 (F p)) := input.Normalized

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : U32 (F p)) := Assumptions input

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (offset : Fin 32) (x : U32 (F p)) (y : U32 (F p)) :=
  y.value = rotRight32 x.value offset.val
  ∧ y.Normalized

def output (offset : Fin 32) (i0 : ℕ) : U32 (Expression (F p)) :=
  Rotation32Bits.output ⟨ offset.val % 8, by omega ⟩ i0

-- #eval! (rot32 (p:=p_babybear) 0) default |>.localLength
-- #eval! (rot32 (p:=p_babybear) 0) default |>.output
def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (off : Fin 32) : ElaboratedCircuit (F p) sentences U32 U32 where
  main := main order off
  localLength _ := 8
  output _inputs i0 := output off i0
  yields _ _ _ := ∅
  yields_eq := by
    intros env input offset
    simp only [main, circuit_norm, ElaboratedCircuit.yields_eq]
    simp [Rotation32Bytes.circuit, Rotation32Bits.circuit, Rotation32Bytes.elaborated, Rotation32Bits.elaborated]

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (offset : Fin 32) : Soundness (F p) (elaborated order offset) order Assumptions (Spec (offset := offset)) := by
  intro i0 env yields checked x_var x h_input x_normalized h_holds

  simp [circuit_norm, main, elaborated,
    Rotation32Bits.circuit, Rotation32Bits.elaborated] at h_holds

  -- abstract away intermediate U32
  let byte_offset : Fin 4 := ⟨ offset.val / 8, by omega ⟩
  let bit_offset : Fin 8 := ⟨ offset.val % 8, by omega ⟩
  set byte_rotated := eval env (ElaboratedCircuit.output (self:=Rotation32Bytes.elaborated byte_offset) sentences x_var i0)

  simp only [Rotation32Bytes.circuit, Rotation32Bytes.elaborated, Rotation32Bytes.Assumptions,
    Rotation32Bytes.Spec, Rotation32Bits.Assumptions, Rotation32Bits.Spec, add_zero] at h_holds

  simp only [Spec, elaborated, output, ElaboratedCircuit.output]
  set y := eval env (Rotation32Bits.output ⟨ offset.val % 8, by omega ⟩ i0)

  simp [Assumptions] at x_normalized
  rw [←h_input] at x_normalized
  obtain ⟨h0, h1⟩ := h_holds
  specialize h0 x_normalized
  obtain ⟨hy_yield, hy_rot, hy_norm⟩ := h0
  specialize h1 hy_norm
  rw [hy_rot] at h1
  obtain ⟨hy, hy_norm⟩ := h1
  simp only [hy_norm, and_true]
  rw [h_input] at hy x_normalized

  -- reason about rotation
  rw [rotRight32_composition _ _ _ (U32.value_lt_of_normalized x_normalized)] at hy
  rw [hy, Nat.div_add_mod']
  simp

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (offset : Fin 32) : Completeness (F p) sentences (elaborated order offset) CompletenessAssumptions := by
  intro i0 env yields x_var h_env x h_eval x_normalized

  simp only [circuit_norm, main, elaborated,
    Rotation32Bits.circuit, Rotation32Bits.elaborated,
    Rotation32Bytes.circuit, Rotation32Bytes.Spec] at h_env ⊢

  obtain ⟨h0, _⟩ := h_env
  rw [h_eval] at h0
  specialize h0 x_normalized
  obtain ⟨h_rot, h_norm⟩ := h0

  constructor
  · simp only [Rotation32Bytes.CompletenessAssumptions, Rotation32Bytes.Assumptions]
    rw [h_eval]
    exact x_normalized
  · simp only [Rotation32Bits.CompletenessAssumptions, Rotation32Bits.Assumptions]
    exact h_norm.2

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (offset : Fin 32) : FormalCircuit order U32 U32 := {
  elaborated := elaborated order offset
  Assumptions
  CompletenessAssumptions
  Spec := Spec (offset := offset)
  soundness := soundness order offset
  completeness := completeness order offset
  completenessAssumptions_implies_assumptions := fun _ _ h => h
}

end Gadgets.Rotation32
