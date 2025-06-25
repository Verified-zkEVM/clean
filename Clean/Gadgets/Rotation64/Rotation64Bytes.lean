import Clean.Types.U64
import Clean.Gadgets.Rotation64.Theorems
import Clean.Utils.Primes

namespace Gadgets.Rotation64Bytes
variable {p : ℕ} [Fact p.Prime]

open Bitwise (rotRight64)

/--
  Rotate the 64-bit integer by increments of 8 positions
  This gadget does not introduce constraints
-/
def rot64_bytes (offset : Fin 8) (input : Var U64 (F p)) : Circuit (F p) (Var U64 (F p)) := do
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

def assumptions (input : U64 (F p)) := input.is_normalized

def spec (offset : Fin 8) (x : U64 (F p)) (y: U64 (F p)) :=
  y.value = rotRight64 x.value (offset.val * 8) ∧ y.is_normalized

instance elaborated (off : Fin 8): ElaboratedCircuit (F p) U64 U64 where
  main := rot64_bytes off
  localLength _ := 0
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
  subcircuitsConsistent x i0 := by
    simp only [rot64_bytes]
    fin_cases off <;> simp only [circuit_norm, reduceIte, Fin.reduceFinMk, Fin.reduceEq]

  output_eq := by
    intros
    fin_cases off
    repeat rfl
  localLength_eq := by
    intros
    fin_cases off
    repeat rfl

theorem soundness (off : Fin 8) : Soundness (F p) (elaborated off) assumptions (spec off) := by
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
  obtain ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩ := as

  simp [circuit_norm, spec, U64.value, -Nat.reducePow]
  constructor
  · fin_cases off <;> (simp_all [explicit_provable_type, rotRight64, circuit_norm, -Nat.reducePow]; omega)
  · fin_cases off <;> simp_all [circuit_norm, U64.is_normalized, explicit_provable_type]

theorem completeness (off : Fin 8) : Completeness (F p) (elaborated off) assumptions := by
  rintro i0 env ⟨ x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩ henv ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ _ assumptions
  fin_cases off <;> simp [elaborated, rot64_bytes, circuit_norm]

def circuit (off : Fin 8) : FormalCircuit (F p) U64 U64 := {
  elaborated off with
  main := rot64_bytes off
  assumptions := assumptions
  spec := spec off
  soundness := soundness off
  completeness := completeness off
}
end Gadgets.Rotation64Bytes
