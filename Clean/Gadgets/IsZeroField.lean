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
def main (x : Expression F) : Circuit F (Expression F) := do
  -- When x ≠ 0, we need x_inv such that x * x_inv = 1
  -- When x = 0, x_inv can be anything (we use 0)
  let xInv ← witness fun env =>
    if x.eval env = 0 then 0 else (x.eval env : F)⁻¹

  let isZero <== 1 - x*xInv -- If x is zero, isZero is one
  isZero * x === 0  -- If x is not zero, isZero is zero

  return isZero

@[reducible]
instance elaborated : ElaboratedCircuit F field field main := by
  elaborate_circuit

def Assumptions (_ : F) : Prop := True

def Spec (x : F) (output : F) : Prop :=
  output = if x = 0 then 1 else 0

theorem soundness : Soundness (Input:=field) (Output:=field) F main Assumptions (Spec (F:=F)) := by
  circuit_proof_all

theorem completeness : Completeness (Input:=field) (Output:=field) F main Assumptions := by
  circuit_proof_all

def circuit : FormalCircuit F field field := {
  main, Assumptions, Spec := Spec (F:=F), soundness, completeness
}

end Gadgets.IsZeroField
