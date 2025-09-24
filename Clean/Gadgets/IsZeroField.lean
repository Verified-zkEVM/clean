import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics

namespace Gadgets.IsZeroField

variable {F : Type} [Field F] [DecidableEq F]

/--
Main circuit that checks if a field element is zero.
Returns 1 if the input is 0, otherwise returns 0.
-/
def main {sentences : PropertySet F} (order : SentenceOrder sentences)
    (x : Var field F) : Circuit sentences (Var field F) := do
  -- When x ≠ 0, we need x_inv such that x * x_inv = 1
  -- When x = 0, x_inv can be anything (we use 0)
  let xInv ← witnessField (sentences:=sentences) (F:=F) (fun env =>
    if x.eval env = 0 then 0 else (x.eval env : F)⁻¹)

  -- If x is zero, isZero is one
  let isZero <==[order] 1 - x*xInv
  -- If x is not zero, isZero is zero
  (isZero * x) ===[order] (0 : Expression F)

  return isZero

instance elaborated {sentences : PropertySet F} (order : SentenceOrder sentences) :
    ElaboratedCircuit F sentences field field where
  main := fun x => main (sentences:=sentences) order x
  localLength _ := 2  -- 2 witnesses: isZero and x_inv
  yields _ _ _ := ∅
  yields_eq := by
    intro env input offset
    simp [main, circuit_norm, Equality.circuit, FormalAssertion.toSubcircuit, Equality.main]

def Assumptions (_ : F) : Prop := True

def CompletenessAssumptions {sentences : PropertySet F} (_ : YieldContext sentences) (_ : F) : Prop := True

def Spec {sentences : PropertySet F} (_checked : CheckedYields sentences) (x : F) (output : F) : Prop :=
  output = if x = 0 then 1 else 0

theorem soundness {sentences : PropertySet F} (order : SentenceOrder sentences) :
    Soundness F (elaborated (sentences:=sentences) order) order Assumptions (Spec (sentences:=sentences)) := by
  circuit_proof_start
  split
  · rename_i h_input
    simp only [h_input] at *
    norm_num at *
    exact h_holds
  · aesop

theorem completeness {sentences : PropertySet F} (order : SentenceOrder sentences) :
    Completeness F sentences (elaborated (sentences:=sentences) order) CompletenessAssumptions := by
  circuit_proof_start
  aesop

def circuit {sentences : PropertySet F} (order : SentenceOrder sentences) :
    FormalCircuit order field field :=
  { (elaborated (sentences:=sentences) order) with
    Assumptions
    CompletenessAssumptions := CompletenessAssumptions (sentences:=sentences)
    Spec := Spec (sentences:=sentences)
    soundness := soundness (sentences:=sentences) order
    completeness := completeness (sentences:=sentences) order
    completenessAssumptions_implies_assumptions := fun _ _ _ => trivial }

end Gadgets.IsZeroField
