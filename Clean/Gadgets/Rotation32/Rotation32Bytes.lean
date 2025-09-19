import Clean.Types.U32
import Clean.Gadgets.Rotation32.Theorems
import Clean.Utils.Primes

namespace Gadgets.Rotation32Bytes
variable {p : ℕ} [Fact p.Prime]

/--
  Rotate the 32-bit integer by increments of 8 positions
  This gadget does not introduce constraints
-/
def main {sentences : PropertySet (F p)} (offset : Fin 4) (input : Var U32 (F p)) : Circuit sentences (Var U32 (F p)) := do
  let ⟨x0, x1, x2, x3⟩ := input

  if offset = 0 then
    return ⟨ x0, x1, x2, x3 ⟩
  else if offset = 1 then
    return ⟨ x1, x2, x3, x0 ⟩
  else if offset = 2 then
    return ⟨ x2, x3, x0, x1 ⟩
  else
    return ⟨ x3, x0, x1, x2 ⟩

def Assumptions (input : U32 (F p)) := input.Normalized

def CompletenessAssumptions {sentences : PropertySet (F p)} (_ : YieldContext sentences) (input : U32 (F p)) :=
  Assumptions input

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (offset : Fin 4) (x : U32 (F p)) (y : U32 (F p)) :=
  y.value = rotRight32 x.value (offset.val * 8) ∧ y.Normalized

instance elaborated {sentences : PropertySet (F p)} (off : Fin 4): ElaboratedCircuit (F p) sentences U32 U32 where
  main := main off
  localLength _ := 0
  output input i0 :=
    let ⟨x0, x1, x2, x3⟩ := input
    match off with
    | 0 => ⟨ x0, x1, x2, x3 ⟩
    | 1 => ⟨ x1, x2, x3, x0 ⟩
    | 2 => ⟨ x2, x3, x0, x1 ⟩
    | 3 => ⟨ x3, x0, x1, x2 ⟩

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

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (off : Fin 4) : Soundness (F p) (elaborated (sentences := sentences) off) order Assumptions (Spec (offset := off)) := by
  rintro i0 env yields checked ⟨ x0_var, x1_var, x2_var, x3_var ⟩ ⟨ x0, x1, x2, x3 ⟩ h_inputs as h

  have h_x0 : x0_var.eval env = x0 := by injections h_inputs
  have h_x1 : x1_var.eval env = x1 := by injections h_inputs
  have h_x2 : x2_var.eval env = x2 := by injections h_inputs
  have h_x3 : x3_var.eval env = x3 := by injections h_inputs
  clear h_inputs
  clear h

  dsimp only [Assumptions, U32.Normalized] at as
  obtain ⟨ h0, h1, h2, h3 ⟩ := as

  simp [circuit_norm, Spec, U32.value, -Nat.reducePow]
  constructor
  · fin_cases off <;> (simp_all [explicit_provable_type, main, circuit_norm, -Nat.reducePow])
  · fin_cases off <;> (simp_all [explicit_provable_type, rotRight32, circuit_norm, -Nat.reducePow]; omega)

theorem completeness {sentences : PropertySet (F p)} (off : Fin 4) : Completeness (F p) sentences (elaborated (sentences := sentences) off) CompletenessAssumptions := by
  rintro i0 env yields ⟨ x0_var, x1_var, x2_var, x3_var ⟩ henv ⟨ x0, x1, x2, x3 ⟩ _
  fin_cases off
  repeat
    intro CompletenessAssumptions
    simp [main, circuit_norm]

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (off : Fin 4) : FormalCircuit order U32 U32 := {
  elaborated := elaborated off
  Assumptions
  CompletenessAssumptions
  Spec := Spec (offset := off)
  soundness := soundness order off
  completeness := completeness off
  completenessAssumptions_implies_assumptions := fun _ _ h => h
}

end Gadgets.Rotation32Bytes
