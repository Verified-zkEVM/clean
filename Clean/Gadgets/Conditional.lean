import Clean.Circuit.Provable
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Boolean
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

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
deriving ProvableStruct

def main [DecidableEq F] (input : Var (Inputs M) F) : Circuit F (Var M F) := do
  let { selector, ifTrue, ifFalse } := input

  -- Inline element-wise scalar multiplication / addition
  let trueVars := toVars ifTrue
  let falseVars := toVars ifFalse
  let resultVars := Vector.ofFn fun i => selector * (trueVars[i] - falseVars[i]) + falseVars[i]

  return fromVars resultVars

def output (selector: Expression F) (ifTrue ifFalse : Var M F) : Var M F :=
  -- Inline element-wise scalar multiplication / addition
  let trueVars := toVars ifTrue
  let falseVars := toVars ifFalse
  let resultVars := Vector.ofFn fun i => selector * (trueVars[i] - falseVars[i]) + falseVars[i]
  fromVars resultVars

def outputValue (selector: F) (ifTrue ifFalse : M F) : M F :=
  -- Inline element-wise scalar multiplication / addition
  let trueElems := toElements ifTrue
  let falseElems := toElements ifFalse
  let resultElems := Vector.ofFn fun i => selector * (trueElems[i] - falseElems[i]) + falseElems[i]
  fromElements resultElems

@[circuit_norm]
def Assumptions (input : Inputs M F) : Prop :=
  IsBool input.selector

/--
Specification: Output is selected based on selector value using if-then-else.
-/
@[circuit_norm]
def Spec [DecidableEq F] (input : Inputs M F) (output : M F) : Prop :=
  output = if input.selector = 1 then input.ifTrue else input.ifFalse

instance elaborated [DecidableEq F] : ElaboratedCircuit F (Inputs M) M where
  main
  localLength _ := 0
  output
  | { selector, ifTrue, ifFalse }, _ => output selector ifTrue ifFalse

theorem soundness [DecidableEq F] : Soundness F (elaborated (F:=F) (M:=M)) Assumptions Spec := by
  circuit_proof_start [output]
  rcases input
  simp only [Inputs.mk.injEq] at h_input
  rcases h_input with ⟨h_selector, h_ifTrue, h_ifFalse⟩
  simp only at h_assumptions

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
    simp only [if_true]
    ring_nf

theorem completeness [DecidableEq F] : Completeness F (elaborated (F:=F) (M:=M)) Assumptions := by
  circuit_proof_start

/--
Conditional selection. Computes: selector * ifTrue + (1 - selector) * ifFalse
-/
@[circuit_norm]
def circuit [DecidableEq F] : FormalCircuit F (Inputs M) M where
  elaborated := elaborated
  Assumptions
  Spec
  soundness
  completeness

/--
Conditional selection.
-/
@[circuit_norm]
def ifElse [Field F] [DecidableEq F] {M : TypeMap} [ProvableType M]
  (selector : Expression F) (ifTrue ifFalse : M (Expression F)) : Circuit F (M (Expression F)) :=
  circuit { selector, ifTrue, ifFalse }

omit [Field F] in
/--
  Lemma to simplify the evaluated output
-/
@[circuit_norm]
theorem eval_ifElse_output [Field F] [DecidableEq F] {M : TypeMap} [ProvableType M] {env}
  (selector : Expression F) (ifTrue ifFalse : M (Expression F)) :
  eval env (output selector ifTrue ifFalse) =
    outputValue (selector.eval env) (eval env ifTrue) (eval env ifFalse) := by
  simp only [output, outputValue]

  -- Show that the result equals the conditional expression
  rw [ProvableType.ext_iff, fromVars, toVars]
  intro i hi
  rw [ProvableType.eval_fromElements]
  simp only [circuit_norm, ProvableType.toElements_fromElements,
    Vector.getElem_map, Vector.getElem_ofFn, ProvableType.getElem_eval_toElements]
  ring
end

end Gadgets.Conditional

export Gadgets.Conditional (ifElse)
