import Clean.Circuit.Provable
import Clean.Gadgets.Boolean
import Clean.Utils.Tactics

namespace Gadgets.Conditional

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

def main [DecidableEq F] {sentences : PropertySet F} (input : Var (Inputs M) F) : Circuit sentences (Var M F) := do
  let { selector, ifTrue, ifFalse } := input

  -- Inline element-wise scalar multiplication
  let trueVars := toVars ifTrue
  let falseVars := toVars ifFalse

  -- Inline element-wise addition
  let resultVars := Vector.ofFn fun i => selector * (trueVars[i] - falseVars[i]) + falseVars[i]

  return fromVars resultVars

def Assumptions (input : Inputs M F) : Prop :=
  IsBool input.selector

/--
Specification: Output is selected based on selector value using if-then-else.
-/
def Spec [DecidableEq F] {sentences : PropertySet F} (_ : CheckedYields sentences) (input : Inputs M F) (output : M F) : Prop :=
  output = if input.selector = 1 then input.ifTrue else input.ifFalse

instance elaborated [DecidableEq F] {sentences : PropertySet F} : ElaboratedCircuit F sentences (Inputs M) M where
  main
  yields _ _ _ := ∅
  yields_eq := by simp only [main, circuit_norm]
  localLength _ := 0

theorem soundness [DecidableEq F] {sentences : PropertySet F} (order : SentenceOrder sentences) : Soundness F (elaborated (F:=F) (M:=M) (sentences:=sentences)) order Assumptions Spec := by
  circuit_proof_start
  rcases input
  simp only [Inputs.mk.injEq] at h_input
  rcases h_input with ⟨h_selector, h_ifTrue, h_ifFalse⟩
  simp only at h_assumptions

  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.eval_fromElements]
  rw [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_ofFn]
  simp only [Expression.eval, ProvableType.getElem_eval_toElements, h_selector, h_ifTrue, h_ifFalse]

  -- Case split on the selector value
  cases h_assumptions with
  | inl h_zero =>
    simp only [h_zero]
    have : (0 : F) = 1 ↔ False := by simp
    simp only [this, if_false]
    ring_nf
  | inr h_one =>
    simp only [h_one]
    have : (1 : F) = 1 ↔ True := by simp
    simp only [if_true]
    ring_nf

def CompletenessAssumptions [DecidableEq F] {sentences : PropertySet F} (_ : YieldContext sentences) (input : Inputs M F) :=
  Assumptions input

theorem completeness [DecidableEq F] {sentences : PropertySet F} : Completeness F sentences (elaborated (F:=F) (M:=M) (sentences:=sentences)) CompletenessAssumptions := by
  circuit_proof_start

/--
Conditional selection. Computes: selector * ifTrue + (1 - selector) * ifFalse
-/
def circuit [DecidableEq F] {sentences : PropertySet F} (order : SentenceOrder sentences) : FormalCircuit order (Inputs M) M where
  elaborated := elaborated
  Assumptions
  CompletenessAssumptions
  Spec
  soundness := soundness order
  completeness
  completenessAssumptions_implies_assumptions := fun _ _ h => h

end

end Gadgets.Conditional
