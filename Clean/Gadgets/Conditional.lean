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

def main [DecidableEq F] (input : Var (Inputs M) F) : Circuit F (Var M F) := do
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
def Spec [DecidableEq F] (input : Inputs M F) (output : M F) : Prop :=
  output = if input.selector = 1 then input.ifTrue else input.ifFalse

instance elaborated [DecidableEq F] : ElaboratedCircuit F (Inputs M) M where
  main
  localLength _ := 0

theorem soundness [DecidableEq F] : Soundness F (elaborated (F := F) (M := M)) Assumptions Spec := by
  circuit_proof_start
  rcases input
  simp only [Inputs.mk.injEq] at h_input
  rcases h_input with ⟨h_selector, h_ifTrue, h_ifFalse⟩
  simp only [Assumptions, Spec] at h_assumptions ⊢

  -- Show that the result equals the conditional expression
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
    simp only [this, if_true]
    ring_nf

theorem completeness [DecidableEq F] : Completeness F (elaborated (F := F) (M := M)) Assumptions := by
  circuit_proof_start

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

end Gadgets.Conditional
