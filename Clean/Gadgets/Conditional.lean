import Clean.Gadgets.ElementwiseScalarMul
import Clean.Gadgets.ElementwiseAdd

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

def main (input : Var (Inputs M) F) : Circuit F (Var M F) := do
  let { selector, ifTrue, ifFalse } := input

  let scaledTrue ← Gadgets.ElementwiseScalarMul.binaryCircuit { scalar := selector, data := ifTrue }
  let scaledFalse ← Gadgets.ElementwiseScalarMul.binaryCircuit { scalar := 1 - selector, data := ifFalse }

  -- Add them together (using circuitWithZeroSpec which handles zero plus something)
  ElementwiseAdd.circuitWithZeroSpec { a := scaledTrue, b := scaledFalse }

def Assumptions (_ : Inputs M F) : Prop := True

/--
Specification: If selector is 1, output equals ifTrue; if selector is 0, output equals ifFalse.
-/
def Spec (input : Inputs M F) (output : M F) : Prop :=
  (input.selector = 1 → output = input.ifTrue) ∧
  (input.selector = 0 → output = input.ifFalse)

instance elaborated : ElaboratedCircuit F (Inputs M) M where
  main
  localLength _ := 0

theorem soundness : Soundness F (elaborated (F := F) (M := M)) Assumptions Spec := by
  circuit_proof_start
  rcases input
  simp only [Inputs.mk.injEq] at h_input
  simp only [h_input] at ⊢ h_holds
  constructor
  · intros h_one
    simp only [h_one] at h_holds
    rcases h_holds with ⟨ h_scale1, h_holds ⟩
    rcases h_holds with ⟨ h_scale2, h_holds ⟩
    specialize h_scale1 trivial
    specialize h_scale2 trivial
    simp only [Gadgets.ElementwiseScalarMul.binaryCircuit, circuit_norm, Gadgets.ElementwiseScalarMul.BinarySpec, FormalCircuit.weakenSpec] at h_scale1 h_scale2
    norm_num at h_scale1 h_scale2
    simp only [h_scale1, h_scale2] at h_holds
    specialize h_holds (by simp only [ElementwiseAdd.Assumptions])
    simp only [ElementwiseAdd.WeakerSpec] at h_holds
    simp_all
  · intros h_zero
    simp only [h_zero] at h_holds
    rcases h_holds with ⟨ h_scale1, h_holds ⟩
    rcases h_holds with ⟨ h_scale2, h_holds ⟩
    specialize h_scale1 trivial
    specialize h_scale2 trivial
    simp only [Gadgets.ElementwiseScalarMul.binaryCircuit, circuit_norm, Gadgets.ElementwiseScalarMul.BinarySpec, FormalCircuit.weakenSpec] at h_scale1 h_scale2
    norm_num at h_scale1 h_scale2
    simp only [h_scale1, h_scale2] at h_holds
    specialize h_holds (by simp only [ElementwiseAdd.Assumptions])
    simp only [ElementwiseAdd.WeakerSpec] at h_holds
    simp_all

theorem completeness : Completeness F (elaborated (F := F) (M := M)) Assumptions := by
  circuit_proof_start
  constructor
  · trivial
  constructor
  · trivial
  simp only [ElementwiseAdd.Assumptions]

/--
Conditional selection. Computes: selector * ifTrue + (1 - selector) * ifFalse
-/
def circuit : FormalCircuit F (Inputs M) M where
  Assumptions
  Spec
  soundness
  completeness

end

end Conditional
