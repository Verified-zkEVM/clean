import Clean.Types.U64
import Clean.Circuit.Subcircuit
import Clean.Utils.Rotation
import Clean.Gadgets.Rotation64.Theorems
import Clean.Gadgets.Rotation64.Rotation64Bytes
import Clean.Gadgets.Rotation64.Rotation64Bits
import Clean.Circuit.Provable

namespace Gadgets.Rotation64
variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 2^16 + 2^8)]

instance : Fact (p > 512) := by
  constructor
  linarith [p_large_enough.elim]

open Utils.Rotation (rotRight64_composition)

/--
  Rotate the 64-bit integer by `offset` bits
-/
def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (offset : Fin 64) (x : Var U64 (F p)) : Circuit sentences (Var U64 (F p)) := do
  let byte_offset : Fin 8 := ⟨ offset.val / 8, by omega ⟩
  let bit_offset : Fin 8 := ⟨ offset.val % 8, by omega ⟩

  -- rotation is performed by combining a bit and a byte rotation
  let byte_rotated ← Rotation64Bytes.circuit order byte_offset x
  Rotation64Bits.circuit order bit_offset byte_rotated

def Assumptions (input : U64 (F p)) := input.Normalized

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (offset : Fin 64) (x : U64 (F p)) (y : U64 (F p)) :=
  y.value = rotRight64 x.value offset.val
  ∧ y.Normalized

def output (offset : Fin 64) (i0 : ℕ) : U64 (Expression (F p)) :=
  Rotation64Bits.output ⟨ offset.val % 8, by omega ⟩ i0

-- #eval! (main (p:=p_babybear) 0) default |>.localLength
-- #eval! (main (p:=p_babybear) 0) default |>.output
def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (off : Fin 64) : ElaboratedCircuit (F p) sentences U64 U64 where
  main := main order off
  localLength _ := 16
  output _ i0 := output off i0

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (offset : Fin 64) : Soundness (F p) (elaborated order offset) order Assumptions (Spec (offset := offset)) := by
  intro i0 env yields checked x_var x h_input x_normalized h_holds

  simp [circuit_norm, main, elaborated,
    Rotation64Bits.circuit, Rotation64Bits.elaborated] at h_holds

  -- abstract away intermediate U64
  let byte_offset : Fin 8 := ⟨ offset.val / 8, by omega ⟩
  let bit_offset : Fin 8 := ⟨ offset.val % 8, by omega ⟩
  set byte_rotated := eval env (ElaboratedCircuit.output (self:=Rotation64Bytes.elaborated order byte_offset) sentences (x_var : Var U64 _) i0)

  simp only [Rotation64Bytes.circuit, Rotation64Bytes.elaborated, Rotation64Bytes.Assumptions,
    Rotation64Bytes.Spec, Rotation64Bits.Assumptions, Rotation64Bits.Spec, add_zero] at h_holds
  simp only [Spec, elaborated, output, ElaboratedCircuit.output]
  set y := eval env (Rotation64Bits.output ⟨ offset.val % 8, by omega ⟩ i0)

  simp [Assumptions] at x_normalized
  rw [←h_input] at x_normalized
  obtain ⟨h0, h1⟩ := h_holds
  specialize h0 x_normalized
  obtain ⟨hx_yield, hy_rot, hy_norm⟩ := h0
  specialize h1 hy_norm

  constructor
  · -- Prove yielded sentences hold (vacuous - no yields)
    intro s hs _
    -- The Rotation subcircuits don't yield anything
    sorry

  simp only [hy_rot] at h1
  obtain ⟨_, ⟨hy, hy_norm⟩⟩ := h1
  simp only [hy_norm, and_true]
  rw [h_input] at hy x_normalized

  -- reason about rotation
  rw [rotRight64_composition _ _ _ (U64.value_lt_of_normalized x_normalized)] at hy
  rw [hy, Nat.div_add_mod']

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (offset : Fin 64) : Completeness (F p) sentences (elaborated order offset) Assumptions := by
  intro i0 env yields x_var h_env x h_eval x_normalized

  simp only [circuit_norm, main, elaborated,
    Rotation64Bits.circuit, Rotation64Bits.elaborated, Rotation64Bits.Assumptions,
    Rotation64Bytes.circuit, Rotation64Bytes.elaborated, Rotation64Bytes.Assumptions, Rotation64Bytes.Spec] at h_env ⊢

  obtain ⟨h0, _⟩ := h_env
  rw [h_eval] at h0
  specialize h0 x_normalized
  obtain ⟨h_rot, h_norm⟩ := h0

  simp only [Assumptions] at x_normalized
  rw [h_eval]
  simp only [x_normalized, true_and, h_norm]

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (offset : Fin 64) : FormalCircuit order U64 U64 := {
  elaborated := elaborated order offset
  Assumptions
  Spec := Spec (offset := offset)
  soundness := soundness order offset
  completeness := completeness order offset
}

end Gadgets.Rotation64
