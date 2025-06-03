import Clean.Types.U32
import Clean.Gadgets.Rotation32.Theorems
import Clean.Utils.Primes

namespace Gadgets.Rotation32Bytes
variable {p : ℕ} [Fact p.Prime]

open Bitwise (rot_right32)
-- TODO: Create necessary soundness theorems for Rotation32Bytes
-- open Rotation32.Theorems (soundnessCase1 soundnessCase2 soundnessCase3 soundnessCase4 soundnessCase5 soundnessCase6 soundnessCase7)

@[reducible]
def Inputs (F : Type) := U32 F

@[reducible]
def Outputs (F : Type) := U32 F

-- q Is this indeed a right rotation?
/--
  Rotate the 32-bit integer by increments of 8 positions
  This gadget does not introduce constraints
-/
def rot32_bytes (offset : Fin 4) (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x0, x1, x2, x3⟩ := input

  if offset = 0 then
    return ⟨ x0, x1, x2, x3 ⟩
  else if offset = 1 then
    return ⟨ x1, x2, x3, x0 ⟩
  else if offset = 2 then
    return ⟨ x2, x3, x0, x1 ⟩
  else
    return ⟨ x3, x0, x1, x2 ⟩

def assumptions (input : Inputs (F p)) := input.is_normalized

def spec (offset : Fin 4) (x : Inputs (F p)) (y: Outputs (F p)) :=
  y.value = rot_right32 x.value (offset.val * 8) ∧ y.is_normalized

instance elaborated (off : Fin 4): ElaboratedCircuit (F p) Inputs Outputs where
  main := rot32_bytes off
  local_length _ := 0
  output input i0 :=
    let ⟨x0, x1, x2, x3⟩ := input
    match off with
    | 0 => ⟨ x0, x1, x2, x3 ⟩
    | 1 => ⟨ x1, x2, x3, x0 ⟩
    | 2 => ⟨ x2, x3, x0, x1 ⟩
    | 3 => ⟨ x3, x0, x1, x2 ⟩
  initial_offset_eq := by
    intros
    fin_cases off
    repeat rfl
  output_eq := by
    intros
    fin_cases off
    repeat rfl
  local_length_eq := by
    intros
    fin_cases off
    repeat rfl

theorem soundness (off : Fin 4) : Soundness (F p) (elaborated off) assumptions (spec off) := by
  sorry

theorem completeness (off : Fin 4) : Completeness (F p) (elaborated off) assumptions := by
  sorry

def circuit (off : Fin 4) : FormalCircuit (F p) Inputs Outputs := {
  elaborated off with
  main := rot32_bytes off
  assumptions := assumptions
  spec := spec off
  soundness := soundness off
  completeness := completeness off
}

end Gadgets.Rotation32Bytes
