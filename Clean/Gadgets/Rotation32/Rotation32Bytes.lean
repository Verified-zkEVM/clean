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
  rintro i0 env ⟨ x0_var, x1_var, x2_var, x3_var ⟩ ⟨ x0, x1, x2, x3 ⟩ h_inputs as h

  have h_x0 : x0_var.eval env = x0 := by injections h_inputs
  have h_x1 : x1_var.eval env = x1 := by injections h_inputs
  have h_x2 : x2_var.eval env = x2 := by injections h_inputs
  have h_x3 : x3_var.eval env = x3 := by injections h_inputs
  clear h_inputs
  clear h

  dsimp only [assumptions, U32.is_normalized] at as
  fin_cases off
  · simp [circuit_norm, rot32_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, eval]
    rw [h_x0, h_x1, h_x2, h_x3]
    simp [U32.value, rot_right32, Nat.mod_one]
    simp [U32.is_normalized]
    tauto

  · simp [circuit_norm, rot32_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, eval]
    rw [h_x0, h_x1, h_x2, h_x3]
    sorry

  · simp [circuit_norm, rot32_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, eval]
    rw [h_x0, h_x1, h_x2, h_x3]
    sorry

  · simp [circuit_norm, rot32_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, eval]
    rw [h_x0, h_x1, h_x2, h_x3]
    sorry

theorem completeness (off : Fin 4) : Completeness (F p) (elaborated off) assumptions := by
  rintro i0 env ⟨ x0_var, x1_var, x2_var, x3_var ⟩ henv ⟨ x0, x1, x2, x3 ⟩ _
  fin_cases off
  repeat
    intro assumptions
    simp [elaborated, rot32_bytes, circuit_norm]

def circuit (off : Fin 4) : FormalCircuit (F p) Inputs Outputs := {
  elaborated off with
  main := rot32_bytes off
  assumptions := assumptions
  spec := spec off
  soundness := soundness off
  completeness := completeness off
}

end Gadgets.Rotation32Bytes
