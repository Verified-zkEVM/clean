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

/--
Main circuit that performs conditional selection.
Computes: selector * ifTrue + (1 - selector) * ifFalse
Using binaryCircuit for scalar multiplication (since selector and 1-selector are binary)
and circuitWithZeroSpec for addition (handles zero cases).
-/
def main (input : Var (Inputs M) F) : Circuit F (Var M F) := do
  let { selector, ifTrue, ifFalse } := input
  
  -- Compute selector * ifTrue (using binaryCircuit since selector is binary)
  let scaledTrue ← Gadgets.ElementwiseScalarMul.binaryCircuit { scalar := selector, data := ifTrue }
  
  -- Compute (1 - selector) * ifFalse (using binaryCircuit since 1-selector is binary when selector is binary)
  let scaledFalse ← Gadgets.ElementwiseScalarMul.binaryCircuit { scalar := 1 - selector, data := ifFalse }
  
  -- Add them together (using circuitWithZeroSpec which handles zero cases)
  ElementwiseAdd.circuitWithZeroSpec { a := scaledTrue, b := scaledFalse }

/--
Assumes the selector is binary (0 or 1).
-/
def Assumptions (input : Inputs M F) : Prop :=
  IsBool input.selector

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
  sorry -- Will need to compose the soundness proofs of ElementwiseScalarMul and ElementwiseAdd

theorem completeness : Completeness F (elaborated (F := F) (M := M)) Assumptions := by
  sorry -- Will need to compose the completeness proofs

def circuit : FormalCircuit F (Inputs M) M where
  Assumptions
  Spec
  soundness
  completeness

end

end Conditional