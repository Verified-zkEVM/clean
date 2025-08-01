import Clean.Gadgets.ElementwiseScalarMul
import Clean.Gadgets.ElementwiseAdd
import Clean.Gadgets.Boolean

namespace Conditional

section
variable {F : Type} [Field F]
variable {M : TypeMap} [ProvableType M]

open ProvableType

/--
Inputs for conditional selection between two ProvableTypes.
Contains a selector bit and two data values.
-/
structure Inputs (M : TypeMap) (F : Type) where
  selector : F
  ifTrue : M F
  ifFalse : M F

instance : ProvableStruct (Inputs M) where
  components := [field, M, M]
  toComponents := fun { selector, ifTrue, ifFalse } => .cons selector (.cons ifTrue (.cons ifFalse .nil))
  fromComponents := fun (.cons selector (.cons ifTrue (.cons ifFalse .nil))) => { selector, ifTrue, ifFalse }

def main [DecidableEq F] (input : Var (Inputs M) F) : Circuit F (Var M F) := do
  let { selector, ifTrue, ifFalse } := input

  let scaledTrue ← Gadgets.ElementwiseScalarMul.binaryCircuit { scalar := selector, data := ifTrue }
  let scaledFalse ← Gadgets.ElementwiseScalarMul.binaryCircuit { scalar := 1 - selector, data := ifFalse }

  -- Add them together (using circuitWithZeroSpec which handles zero plus something)
  ElementwiseAdd.circuitWithZeroSpec { a := scaledTrue, b := scaledFalse }

def Assumptions (input : Inputs M F) : Prop :=
  IsBool input.selector

/--
Specification: Output is selected based on selector value using if-then-else.
-/
def Spec [DecidableEq F] (input : Inputs M F) (output : M F) : Prop :=
  output = if input.selector = 1 then input.ifTrue else input.ifFalse

instance elaborated [DecidableEq F] : ElaboratedCircuit F (Inputs M) M where
  main
  localLength _ := 0

theorem soundness [DecidableEq F] : Soundness F (elaborated (F := F) (M := M)) Assumptions Spec := by
  circuit_proof_start
  rcases input
  simp only [Inputs.mk.injEq] at h_input
  simp only [h_input] at ⊢ h_holds
  simp only [Assumptions, Spec] at h_assumptions ⊢
  rcases h_holds with ⟨ h_scale1, h_holds ⟩
  rcases h_holds with ⟨ h_scale2, h_holds ⟩
  -- binaryCircuit now has boolean assumptions
  simp only [Gadgets.ElementwiseScalarMul.binaryCircuit, circuit_norm] at h_scale1 h_scale2
  specialize h_scale1 h_assumptions
  specialize h_scale2 (by
    simp only [Gadgets.ElementwiseScalarMul.BinaryAssumptions]
    cases h_assumptions <;> simp_all [circuit_norm])
  simp only [Gadgets.ElementwiseScalarMul.BinarySpec] at h_scale1 h_scale2
  specialize h_holds (by simp only [ElementwiseAdd.Assumptions])
  simp only [ElementwiseAdd.WeakerSpec] at h_holds
  cases h_assumptions with
  | inl h_zero =>
    simp only [h_zero] at h_scale1 h_scale2 h_holds ⊢
    simp only [h_scale1, h_scale2] at h_holds
    rw [if_neg (by simp [h_zero])]
    aesop
  | inr h_one =>
    simp only [h_one] at h_scale1 h_scale2 h_holds ⊢
    simp only [h_scale1, h_scale2] at h_holds
    aesop

theorem completeness [DecidableEq F] : Completeness F (elaborated (F := F) (M := M)) Assumptions := by
  circuit_proof_start
  constructor
  · aesop
  constructor
  · cases h_assumptions with
    | inl h =>
        simp only [h_input.symm] at h
        simp [h, Gadgets.ElementwiseScalarMul.binaryCircuit, circuit_norm, Gadgets.ElementwiseScalarMul.BinaryAssumptions]
    | inr h =>
        simp only [h_input.symm] at h
        simp [h, Gadgets.ElementwiseScalarMul.binaryCircuit, circuit_norm, Gadgets.ElementwiseScalarMul.BinaryAssumptions]
  simp only [ElementwiseAdd.Assumptions]

/--
Conditional selection. Computes: selector * ifTrue + (1 - selector) * ifFalse
-/
def circuit [DecidableEq F] : FormalCircuit F (Inputs M) M where
  elaborated := elaborated
  Assumptions
  Spec
  soundness
  completeness

end

end Conditional
