import Clean.Types.U32
import Clean.Gadgets.Rotation32.Theorems
import Clean.Utils.Primes

namespace Gadgets.Rotation32Bytes
variable {p : ℕ} [Fact p.Prime]

open Bitwise (rot_right32)
/--
  Rotate the 32-bit integer by increments of 8 positions
  This gadget does not introduce constraints
-/
def rot32_bytes (offset : Fin 4) (input : Var U32 (F p)) : Circuit (F p) (Var U32 (F p)) := do
  let ⟨x0, x1, x2, x3⟩ := input

  if offset = 0 then
    return ⟨ x0, x1, x2, x3 ⟩
  else if offset = 1 then
    return ⟨ x1, x2, x3, x0 ⟩
  else if offset = 2 then
    return ⟨ x2, x3, x0, x1 ⟩
  else
    return ⟨ x3, x0, x1, x2 ⟩

def assumptions (input : U32 (F p)) := input.Normalized

def spec (offset : Fin 4) (x : U32 (F p)) (y: U32 (F p)) :=
  y.value = rot_right32 x.value (offset.val * 8) ∧ y.Normalized

instance elaborated (off : Fin 4): ElaboratedCircuit (F p) U32 U32 where
  main := rot32_bytes off
  localLength _ := 0
  output input i0 :=
    let ⟨x0, x1, x2, x3⟩ := input
    match off with
    | 0 => ⟨ x0, x1, x2, x3 ⟩
    | 1 => ⟨ x1, x2, x3, x0 ⟩
    | 2 => ⟨ x2, x3, x0, x1 ⟩
    | 3 => ⟨ x3, x0, x1, x2 ⟩

  subcircuitsConsistent x i0 := by
    simp only [rot32_bytes]
    fin_cases off <;> simp only [circuit_norm, reduceIte, Fin.reduceFinMk, Fin.reduceEq]

  output_eq := by
    intros
    fin_cases off
    repeat rfl
  localLength_eq := by
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

  dsimp only [assumptions, U32.Normalized] at as
  obtain ⟨ h0, h1, h2, h3 ⟩ := as

  simp [circuit_norm, spec, U32.value, -Nat.reducePow]
  constructor
  · fin_cases off <;> (simp_all [explicit_provable_type, rot_right32, circuit_norm, -Nat.reducePow]; omega)
  · fin_cases off <;> simp_all [circuit_norm, U32.Normalized, explicit_provable_type]

theorem completeness (off : Fin 4) : Completeness (F p) (elaborated off) assumptions := by
  rintro i0 env ⟨ x0_var, x1_var, x2_var, x3_var ⟩ henv ⟨ x0, x1, x2, x3 ⟩ _
  fin_cases off
  repeat
    intro assumptions
    simp [elaborated, rot32_bytes, circuit_norm]

def circuit (off : Fin 4) : FormalCircuit (F p) U32 U32 := {
  elaborated off with
  main := rot32_bytes off
  assumptions := assumptions
  spec := spec off
  soundness := soundness off
  completeness := completeness off
}

end Gadgets.Rotation32Bytes
