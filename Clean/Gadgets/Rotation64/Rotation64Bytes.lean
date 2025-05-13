import Clean.Types.U64
import Clean.Gadgets.Rotation64.Theorems
import Clean.Utils.Primes

namespace Gadgets.Rotation64Bytes
variable {p : ℕ} [Fact p.Prime]

open Gadgets.Rotation64.Theorems (rot_right64)
open Gadgets.Rotation64.Theorems (soundnessCase1 soundnessCase2 soundnessCase3 soundnessCase4 soundnessCase5 soundnessCase6 soundnessCase7)

@[reducible]
def Inputs (F : Type) :=  U64 F

@[reducible]
def Outputs (F : Type) := U64 F


/--
  Rotate the 64-bit integer by increments of 8 positions
  This gadget does not introduce constraints
-/
def rot64_bytes (offset : Fin 8) (input : Var Inputs (F p)) : Circuit (F p) (Var Outputs (F p)) := do
  let ⟨x0, x1, x2, x3 , x4, x5, x6, x7⟩ := input

  if offset = 0 then
    return ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩
  else if offset = 1 then
    return ⟨ x1, x2, x3, x4, x5, x6, x7, x0 ⟩
  else if offset = 2 then
    return ⟨ x2, x3, x4, x5, x6, x7, x0, x1 ⟩
  else if offset = 3 then
    return ⟨ x3, x4, x5, x6, x7, x0, x1, x2 ⟩
  else if offset = 4 then
    return ⟨ x4, x5, x6, x7, x0, x1, x2, x3 ⟩
  else if offset = 5 then
    return ⟨ x5, x6, x7, x0, x1, x2, x3, x4 ⟩
  else if offset = 6 then
    return ⟨ x6, x7, x0, x1, x2, x3, x4, x5 ⟩
  else
    return ⟨ x7, x0, x1, x2, x3, x4, x5, x6 ⟩

def assumptions (input : Inputs (F p)) := input.is_normalized

def spec (offset : Fin 8) (x : Inputs (F p)) (y: Outputs (F p)) :=
  y.value = rot_right64 x.value (offset.val * 8) ∧ y.is_normalized

instance elaborated (off : Fin 8): ElaboratedCircuit (F p) Inputs (Var Outputs (F p)) where
  main := rot64_bytes off
  local_length _ := 0
  output input i0 :=
    let ⟨x0, x1, x2, x3, x4, x5, x6, x7⟩ := input
    match off with
    | 0 => ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩
    | 1 => ⟨ x1, x2, x3, x4, x5, x6, x7, x0 ⟩
    | 2 => ⟨ x2, x3, x4, x5, x6, x7, x0, x1 ⟩
    | 3 => ⟨ x3, x4, x5, x6, x7, x0, x1, x2 ⟩
    | 4 => ⟨ x4, x5, x6, x7, x0, x1, x2, x3 ⟩
    | 5 => ⟨ x5, x6, x7, x0, x1, x2, x3, x4 ⟩
    | 6 => ⟨ x6, x7, x0, x1, x2, x3, x4, x5 ⟩
    | 7 => ⟨ x7, x0, x1, x2, x3, x4, x5, x6 ⟩
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


theorem soundness (off : Fin 8) : Soundness (F p) assumptions (spec off) (circuit:=elaborated off) := by
  rintro i0 env ⟨ x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩ ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ h_inputs as h

  have h_x0 : x0_var.eval env = x0 := by injections h_inputs
  have h_x1 : x1_var.eval env = x1 := by injections h_inputs
  have h_x2 : x2_var.eval env = x2 := by injections h_inputs
  have h_x3 : x3_var.eval env = x3 := by injections h_inputs
  have h_x4 : x4_var.eval env = x4 := by injections h_inputs
  have h_x5 : x5_var.eval env = x5 := by injections h_inputs
  have h_x6 : x6_var.eval env = x6 := by injections h_inputs
  have h_x7 : x7_var.eval env = x7 := by injections h_inputs
  clear h_inputs
  clear h

  dsimp only [assumptions, U64.is_normalized] at as
  fin_cases off
  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, eval]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    simp [U64.value, rot_right64, Nat.mod_one]
    simp [U64.is_normalized]
    tauto

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, eval]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    constructor
    · exact soundnessCase1 x0 x1 x2 x3 x4 x5 x6 x7 as
    · simp [U64.is_normalized]
      tauto

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, eval]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    constructor
    · exact soundnessCase2 x0 x1 x2 x3 x4 x5 x6 x7 as
    · simp [U64.is_normalized]
      tauto

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, eval, show (3 : Fin 8).val = 3 by rfl]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    constructor
    · exact soundnessCase3 x0 x1 x2 x3 x4 x5 x6 x7 as
    · simp [U64.is_normalized]
      tauto

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, eval, show (4 : Fin 8).val = 4 by rfl]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    constructor
    · exact soundnessCase4 x0 x1 x2 x3 x4 x5 x6 x7 as
    · simp [U64.is_normalized]
      tauto

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, eval, show (5 : Fin 8).val = 5 by rfl]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    constructor
    · exact soundnessCase5 x0 x1 x2 x3 x4 x5 x6 x7 as
    · simp [U64.is_normalized]
      tauto

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, eval, show (6 : Fin 8).val = 6 by rfl]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    constructor
    · exact soundnessCase6 x0 x1 x2 x3 x4 x5 x6 x7 as
    · simp [U64.is_normalized]
      tauto

  · simp [circuit_norm, rot64_bytes, spec, circuit_norm, Circuit.output, monad_norm, StateT.pure, pure, eval, show (7 : Fin 8).val = 7 by rfl]
    rw [h_x0, h_x1, h_x2, h_x3, h_x4, h_x5, h_x6, h_x7]
    constructor
    · exact soundnessCase7 x0 x1 x2 x3 x4 x5 x6 x7 as
    · simp [U64.is_normalized]
      tauto

theorem completeness (off : Fin 8) : Completeness (F p) Outputs assumptions (circuit := elaborated off) := by
  rintro i0 env ⟨ x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩ henv ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ _
  fin_cases off
  repeat
    intro assumptions
    simp [elaborated, rot64_bytes, circuit_norm]



def circuit (off : Fin 8) : FormalCircuit (F p) Inputs Outputs := {
  elaborated off with
  main := rot64_bytes off
  assumptions := assumptions
  spec := spec off
  soundness := soundness off
  completeness := completeness off
}
end Gadgets.Rotation64Bytes
