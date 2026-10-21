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
  ir : Unconstrained field F
  n : UnconstrainedNat F
deriving CircuitType

-- the derived instance is the halo2 one, and `Var` is the companion structure
example : Halo2.Var Inputs F = Inputs.Var F := rfl

-- the generated view struct carries the `DecomposableStruct` marker (the post-revert addition
-- the struct-eval simprocs key on)
example : DecomposableStruct Inputs.Var := inferInstance

-- Var view: cells for provable fields, builder programs for hints
example (v : Inputs.Var F) : AssignedCell F := v.x
example (v : Inputs.Var F) : Vector (AssignedCell F) 4 := v.ys
example (v : Inputs.Var F) : Witgen.MOver F (AssignedCell F) (FExpr F) := v.ir
example (v : Inputs.Var F) : Witgen.MOver F (AssignedCell F) (NExpr F) := v.n

-- Value view: verifier values for provable fields, hints erased
example (v : Inputs.Value F) : F := v.x
example (v : Inputs.Value F) : Unit := v.ir
example (v : Inputs.Value F) : Unit := v.n

-- ProverValue view: everything visible (hints at their evaluated sort)
example (v : Inputs.ProverValue F) : F := v.x
example (v : Inputs.ProverValue F) : F := v.ir
example (v : Inputs.ProverValue F) : ℕ := v.n

-- evaluation dispatches field-wise
example (env : Placed Environment F) (v : Inputs.Var F) :
    (@Eval.eval _ _ _ (CircuitType.verifierEval Inputs) env v).ir = () := rfl

example (env : Placed ProverEnvironment F) (v : Inputs.Var F) :
    (@Eval.eval _ _ _ (CircuitType.proverEval Inputs) env v).ir
      = Witgen.MOver.eval env v.ir := by
  with_unfolding_all rfl

end Halo2.Tests.TestCircuitTypeDeriving
