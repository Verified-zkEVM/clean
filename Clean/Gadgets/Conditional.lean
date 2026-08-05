import Clean.Circuit.Provable
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Boolean
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

namespace Gadgets.Conditional

section
variable {F : Type} [FiniteField F]
variable {M : TypeMap} [ProvableType M]

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
  let trueVars := toElements ifTrue
  let falseVars := toElements ifFalse
  let resultVars := Vector.ofFn fun i => selector * (trueVars[i] - falseVars[i]) + falseVars[i]

  return fromElements (M:=M) resultVars

def output (selector: Expression F) (ifTrue ifFalse : Var M F) : Var M F :=
  -- Inline element-wise scalar multiplication / addition
  let trueVars := toElements (M:=M) ifTrue
  let falseVars := toElements (M:=M) ifFalse
  let resultVars := Vector.ofFn fun i => selector * (trueVars[i] - falseVars[i]) + falseVars[i]
  fromElements (M:=M) resultVars

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

instance elaborated [DecidableEq F] : ElaboratedCircuit F (Inputs M) M main := by
  elaborate_circuit

theorem soundness [DecidableEq F] : Soundness F (Input := Inputs M) main Assumptions Spec := by
  circuit_proof_start
  rcases h_input with ⟨h_selector, h_ifTrue, h_ifFalse⟩

  -- Show that the result equals the conditional expression
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.eval_fromElements]
  rw [ProvableType.toElements_fromElements, Vector.getElem_map, Vector.getElem_ofFn]
  simp only [circuit_norm, ProvableType.getElem_eval_toElements, h_selector, h_ifTrue, h_ifFalse]

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

theorem completeness [DecidableEq F] : Completeness F (Input := Inputs M) main Assumptions := by
  circuit_proof_start

/--
Conditional selection. Computes: selector * ifTrue + (1 - selector) * ifFalse
-/
@[circuit_norm]
def circuit [DecidableEq F] : FormalCircuit F (Inputs M) M where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness
  computableWitnesses := by
    intro n input env env'
    -- destructure up front: simp does not iota-reduce the `match` coming from `main`'s
    -- destructuring against an opaque variable
    obtain ⟨selector, ifTrue, ifFalse⟩ := input
    refine ⟨?_, ?_⟩
    · -- forAll part (witnesses/subcircuits are computable) — closes automatically
      simp only [circuit_norm]
      try (unfold_formal_circuit_consts; simp only [circuit_norm])
    · -- output part: the output agrees given the input agrees (+ AgreesBelow)
      intro h_input h_agrees
      simp_all only [circuit_norm, Inputs.mk.injEq] -- TODO our tactic could be able to break up h_input
      -- HARD TO AUTOMATE: goal is now
      --   eval env.toEnvironment (fromElements (Vector.ofFn fun i => selector*(…)+…))
      --     = eval env'.toEnvironment (…)
      simp_rw [ProvableType.eval_fromElements]
      congr 1
      rw [Vector.ext_iff]
      intro i hi
      simp only [circuit_norm]
      simp_rw [ProvableType.getElem_eval_toElements]
      simp_all

/--
Conditional selection.
-/
@[circuit_norm]
def ifElse [DecidableEq F] {M : TypeMap} [ProvableType M]
  (selector : Expression F) (ifTrue ifFalse : M (Expression F)) : Circuit F (M (Expression F)) :=
  circuit { selector, ifTrue, ifFalse }

/--
  Lemma to simplify the evaluated output
-/
@[circuit_norm]
theorem eval_ifElse_output {M : TypeMap} [ProvableType M] {env}
  (selector : Expression F) (ifTrue ifFalse : M (Expression F)) :
  eval env (output selector ifTrue ifFalse) =
    outputValue (selector.eval env) (eval env ifTrue) (eval env ifFalse) := by
  simp only [output, outputValue, circuit_norm]

  -- Show that the result equals the conditional expression
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.eval_fromElements]
  simp only [circuit_norm, Vector.getElem_map, Vector.getElem_ofFn, ProvableType.getElem_eval_toElements]
end

end Gadgets.Conditional

export Gadgets.Conditional (ifElse)
