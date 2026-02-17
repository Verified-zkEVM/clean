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
def main (x : Var field F) : Circuit F (Var field F) := do
  -- When x ≠ 0, we need x_inv such that x * x_inv = 1
  -- When x = 0, x_inv can be anything (we use 0)
  let xInv ← witness fun env =>
    if x.eval env = 0 then 0 else (x.eval env : F)⁻¹

  let isZero <== 1 - x*xInv -- If x is zero, isZero is one
  isZero * x === 0  -- If x is not zero, isZero is zero

  return isZero

instance elaborated : ElaboratedCircuit F field field where
  main
  localLength _ := 2  -- 2 witnesses: isZero and x_inv
  localAdds_eq _ _ _ := by
    simp only [main, circuit_norm, Operations.localAdds]

def Assumptions (_ : F) : Prop := True

def Spec (x : F) (output : F) : Prop :=
  output = if x = 0 then 1 else 0

theorem soundness : Soundness F elaborated Assumptions (Spec (F:=F)) := by
  circuit_proof_start
  split
  · rename_i h_input
    simp only [h_input] at *
    norm_num at *
    assumption
  · aesop

theorem completeness : Completeness F elaborated Assumptions := by
  circuit_proof_start
  aesop

def circuit : FormalCircuit F field field := {
  elaborated with Assumptions, Spec := Spec (F:=F), soundness, completeness
}

end Gadgets.IsZeroField
