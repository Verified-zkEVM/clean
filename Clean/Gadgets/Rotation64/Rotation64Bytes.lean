import Clean.Types.U64
import Clean.Gadgets.Rotation64.Theorems
import Clean.Utils.Primes

namespace Gadgets.Rotation64Bytes
variable {p : ℕ} [Fact p.Prime]

/--
  Rotate the 64-bit integer by increments of 8 positions
  This gadget does not introduce constraints
-/
def main {sentences : PropertySet (F p)} (_order : SentenceOrder sentences) (offset : Fin 8) (input : Var U64 (F p)) : Circuit sentences (Var U64 (F p)) := do
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

def Assumptions (input : U64 (F p)) := input.Normalized

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : U64 (F p)) :=
  Assumptions input

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (offset : Fin 8) (x : U64 (F p)) (y : U64 (F p)) :=
  y.value = rotRight64 x.value (offset.val * 8) ∧ y.Normalized

def elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (off : Fin 8): ElaboratedCircuit (F p) sentences U64 U64 where
  main := main order off
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
    simp only [main]
    fin_cases off <;> simp only [circuit_norm, reduceIte, Fin.reduceFinMk, Fin.reduceEq]

  output_eq := by
    intros
    fin_cases off
    repeat rfl
  localLength_eq := by
    intros
    fin_cases off
    repeat rfl

theorem soundness {sentences : PropertySet (F p)} {order : SentenceOrder sentences} (off : Fin 8) : Soundness (F p) (elaborated order off) order Assumptions (Spec (offset := off)) := by
  rintro i0 env state_var checked ⟨ x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩ ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ h_inputs as h

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

  dsimp only [Assumptions, U64.Normalized] at as
  obtain ⟨ h0, h1, h2, h3, h4, h5, h6, h7 ⟩ := as

  simp [circuit_norm, Spec, U64.value, -Nat.reducePow]
  and_intros
  · fin_cases off <;> (simp_all [explicit_provable_type, elaborated, main, circuit_norm, -Nat.reducePow])
  · fin_cases off <;> (simp_all [explicit_provable_type, elaborated, rotRight64, circuit_norm, -Nat.reducePow]; omega)
  · fin_cases off <;> (simp_all [explicit_provable_type, elaborated, circuit_norm, -Nat.reducePow])
  · fin_cases off <;> (simp_all [explicit_provable_type, elaborated, circuit_norm, -Nat.reducePow])
  · fin_cases off <;> (simp_all [explicit_provable_type, elaborated, circuit_norm, -Nat.reducePow])
  · fin_cases off <;> (simp_all [explicit_provable_type, elaborated, circuit_norm, -Nat.reducePow])
  · fin_cases off <;> (simp_all [explicit_provable_type, elaborated, circuit_norm, -Nat.reducePow])
  · fin_cases off <;> (simp_all [explicit_provable_type, elaborated, circuit_norm, -Nat.reducePow])
  · fin_cases off <;> (simp_all [explicit_provable_type, elaborated, circuit_norm, -Nat.reducePow])
  · fin_cases off <;> (simp_all [explicit_provable_type, elaborated, circuit_norm, -Nat.reducePow])

theorem completeness {sentences : PropertySet (F p)} {order : SentenceOrder sentences} (off : Fin 8) : Completeness (F p) sentences (elaborated order off) CompletenessAssumptions := by
  rintro i0 env yielded ⟨ x0_var, x1_var, x2_var, x3_var, x4_var, x5_var, x6_var, x7_var ⟩ henv ⟨ x0, x1, x2, x3, x4, x5, x6, x7 ⟩ _ Assumptions
  fin_cases off <;> simp [elaborated, main, circuit_norm]

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (off : Fin 8) : FormalCircuit order U64 U64 where
  elaborated := elaborated order off
  Assumptions := Assumptions
  CompletenessAssumptions
  Spec := Spec (offset := off)
  soundness := soundness off
  completeness := completeness off
  completenessAssumptions_implies_assumptions := fun _ _ h => h
end Gadgets.Rotation64Bytes
