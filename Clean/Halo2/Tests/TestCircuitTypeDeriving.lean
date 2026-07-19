import Clean.Halo2.CircuitTypeDeriving
import Clean.Halo2.WitnessIR

/-!
Regression test for Halo2's `deriving CircuitType`: a mixed record of ordinary
provable data and prover-only hints derives per-field, with the companion views typed
at the `Placed` cell environments.
-/

namespace Halo2.Tests.TestCircuitTypeDeriving
variable {F : Type} [FiniteField F]

structure Inputs (F : Type) where
  x : F
  ys : Vector F 4
  hint : Unconstrained field F
  ir : UnconstrainedIR F
deriving CircuitType

-- the derived instance is the halo2 one, and `Var` is the companion structure
example : Halo2.Var Inputs F = Inputs.Var F := rfl

-- Var view: cells for provable fields, programs for hints
example (v : Inputs.Var F) : AssignedCell F := v.x
example (v : Inputs.Var F) : Vector (AssignedCell F) 4 := v.ys
example (v : Inputs.Var F) : FExpr F := v.hint
example (v : Inputs.Var F) : WitgenIR F 1 := v.ir

-- Value view: verifier values for provable fields, hints erased
example (v : Inputs.Value F) : F := v.x
example (v : Inputs.Value F) : Unit := v.hint
example (v : Inputs.Value F) : Unit := v.ir

-- ProverValue view: everything visible
example (v : Inputs.ProverValue F) : F := v.x
example (v : Inputs.ProverValue F) : F := v.hint
example (v : Inputs.ProverValue F) : F := v.ir

-- evaluation dispatches field-wise
example (env : Placed Environment F) (v : Inputs.Var F) :
    (@Eval.eval _ _ _ (CircuitType.verifierEval Inputs) env v).hint = () := rfl

example (env : Placed ProverEnvironment F) (v : Inputs.Var F) :
    (@Eval.eval _ _ _ (CircuitType.proverEval Inputs) env v).ir
      = (v.ir.eval env)[0] := by
  with_unfolding_all rfl

end Halo2.Tests.TestCircuitTypeDeriving
