import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics

namespace Gadgets.IsZeroField
open Witgen
variable {F : Type} [FiniteField F] [DecidableEq F]

/--
Returns 1 if the input is 0, otherwise returns 0.
-/
def circuit : FormalCircuit F field field where
  main (x : Expression F) := do
    let z ← witness (.ite (x =? 0) 0 x⁻¹)
     -- if x = 0 then b = 1
    let b <== 1 - x * z
      -- if x ≠ 0 then b = 0
    b * x === 0
    return b

  Spec (x : F) (b : F) :=
    b = (if x = 0 then 1 else 0)

  soundness := by circuit_proof_all
  completeness := by circuit_proof_all

end Gadgets.IsZeroField
