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
def main (offset : Fin 64) (x : Var U64 (F p)) : Circuit (F p) (Var U64 (F p)) := do
  let byte_offset : Fin 8 := ⟨ offset.val / 8, by omega ⟩
  let bit_offset : Fin 8 := ⟨ offset.val % 8, by omega ⟩

  -- rotation is performed by combining a bit and a byte rotation
  let byte_rotated ← Rotation64Bytes.circuit byte_offset x
  Rotation64Bits.circuit bit_offset byte_rotated

def Assumptions (input : U64 (F p)) := input.Normalized

def Spec (offset : Fin 64) (x : U64 (F p)) (y : U64 (F p)) :=
  y.value = rotRight64 x.value offset.val
  ∧ y.Normalized

def output (offset : Fin 64) (i0 : ℕ) : U64 (Expression (F p)) :=
  Rotation64Bits.output ⟨ offset.val % 8, by omega ⟩ i0

-- #eval! (main (p:=p_babybear) 0) default |>.localLength
-- #eval! (main (p:=p_babybear) 0) default |>.output
def elaborated (off : Fin 64) : ElaboratedCircuit (F p) U64 U64 where
  main := main off
  localLength _ := 16
  output _ i0 := output off i0

theorem soundness (offset : Fin 64) : Soundness (F p) (circuit := elaborated offset) Assumptions (Spec offset) := by
  circuit_proof_start [Rotation64Bits.circuit, Rotation64Bits.elaborated]

  -- abstract away intermediate U64
  let byte_offset : Fin 8 := ⟨ offset.val / 8, by omega ⟩
  let bit_offset : Fin 8 := ⟨ offset.val % 8, by omega ⟩
  set byte_rotated := ProvableType.eval' env
    ((Rotation64Bytes.circuit byte_offset).output input_var i₀)

  simp only [Rotation64Bytes.circuit, Rotation64Bytes.elaborated,
    Rotation64Bytes.Assumptions, Rotation64Bytes.Spec, add_zero,
    Rotation64Bits.Assumptions, Rotation64Bits.Spec, output] at h_holds ⊢
  set y := ProvableType.eval' env (Rotation64Bits.output ⟨ offset.val % 8, by omega ⟩ i₀)
  simp_all only [forall_const, and_true]

  -- reason about rotation
  rw [rotRight64_composition _ _ _ (U64.value_lt_of_normalized h_assumptions),
    Nat.div_add_mod']

theorem completeness (offset : Fin 64) : Completeness (F p) (elaborated offset) Assumptions := by
  circuit_proof_all [Rotation64Bits.circuit, Rotation64Bits.elaborated,
    Rotation64Bits.Assumptions, Rotation64Bytes.circuit,
    Rotation64Bytes.Assumptions, Rotation64Bytes.Spec]

def circuit (offset : Fin 64) : FormalCircuit (F p) U64 U64 := {
  elaborated offset with
  Assumptions
  Spec := Spec offset
  soundness := soundness offset
  completeness := completeness offset
}

end Gadgets.Rotation64
