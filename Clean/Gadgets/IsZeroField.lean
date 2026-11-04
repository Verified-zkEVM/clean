import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics

open Clean

namespace Gadgets.IsZeroField
variable {F : Type} [FiniteField F] [DecidableEq F]

private theorem condition_eval (env : ProverEnvironment F) (x : Expression F) :
    Witgen.BExprOver.eval ({ env := env } : Ctx F)
      (x =? (0 : ℕ)) = decide (x.eval env.toEnvironment = 0) := by
  change (BExpr.feq (.expr x) (.const ((0 : ℕ) : F))).eval ({ env := env } : Ctx F) = _
  apply Bool.eq_iff_iff.mpr
  simp only [BExpr.eval_feq_iff, Witgen.FExprOver.eval,
    WitgenEnv.readVar_eq, Nat.cast_zero, decide_eq_true_eq]

attribute [local circuit_norm] condition_eval

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
