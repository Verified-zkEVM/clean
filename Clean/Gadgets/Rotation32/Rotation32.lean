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
def main (offset : Fin 32) (x : Var U32 (F p)) : Circuit (F p) (Var U32 (F p)) := do
  let byte_offset : Fin 4 := ⟨ offset.val / 8, by omega ⟩
  let bit_offset : Fin 8 := ⟨ offset.val % 8, by omega ⟩

  -- rotation is performed by combining a bit and a byte rotation
  let byte_rotated ← Rotation32Bytes.circuit byte_offset x
  Rotation32Bits.circuit bit_offset byte_rotated

def Assumptions (input : U32 (F p)) := input.Normalized

def Spec (offset : Fin 32) (x : U32 (F p)) (y : U32 (F p)) :=
  y.value = rotRight32 x.value offset.val
  ∧ y.Normalized

def output (offset : Fin 32) (i0 : ℕ) : U32 (Expression (F p)) :=
  Rotation32Bits.output ⟨ offset.val % 8, by omega ⟩ i0

-- #eval! (rot32 (p:=p_babybear) 0) default |>.localLength
-- #eval! (rot32 (p:=p_babybear) 0) default |>.output
def elaborated (off : Fin 32) : ElaboratedCircuit (F p) U32 U32 where
  main := main off
  localLength _ := 8
  output _inputs i0 := output off i0

theorem soundness (offset : Fin 32) : Soundness (F p) (circuit := elaborated offset) Assumptions (Spec offset) := by
  circuit_proof_start [Rotation32Bits.circuit, Rotation32Bits.elaborated]

  -- abstract away intermediate U32
  let byte_offset : Fin 4 := ⟨ offset.val / 8, by omega ⟩
  let bit_offset : Fin 8 := ⟨ offset.val % 8, by omega ⟩
  set byte_rotated := eval env
    ((Rotation32Bytes.circuit byte_offset).output input_var i₀)

  simp only [Rotation32Bytes.circuit, Rotation32Bytes.elaborated,
    Rotation32Bytes.Assumptions, Rotation32Bytes.Spec, add_zero,
    Rotation32Bits.Assumptions, Rotation32Bits.Spec, output] at h_holds ⊢
  set y : U32 (F p) := eval env (Rotation32Bits.output (p:=p) ⟨ offset.val % 8, by omega ⟩ i₀)
  simp_all only [forall_const, and_true]

  -- reason about rotation
  rw [rotRight32_composition _ _ _ (U32.value_lt_of_normalized h_assumptions),
    Nat.div_add_mod']

theorem completeness (offset : Fin 32) : Completeness (F p) (elaborated offset) Assumptions := by
  circuit_proof_all [Rotation32Bits.circuit, Rotation32Bits.elaborated,
    Rotation32Bits.Assumptions, Rotation32Bytes.circuit,
    Rotation32Bytes.Assumptions, Rotation32Bytes.Spec]

def circuit (offset : Fin 32) : FormalCircuit (F p) U32 U32 := {
  elaborated offset with
  Assumptions
  Spec := Spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.Rotation32
