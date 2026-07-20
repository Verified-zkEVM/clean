import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Halo2.Provable

/-!
# `deriving CircuitType` for Halo2 circuit inputs

Registers the shared record-`CircuitType` deriving generator
(`Clean/Utils/Tactics/ProvableStructDeriving.lean`) at Halo2's environment profile, so
structures mixing ordinary provable data with prover-only hints derive their halo2
`CircuitType` per-field, exactly like main Clean's:

```lean
structure Inputs (F : Type) where
  base : Point F
  alpha : Unconstrained field F
deriving CircuitType
```

Inside a `Halo2.*` namespace, `deriving CircuitType` resolves to `Halo2.CircuitType`
and dispatches here; the generated `Inputs.Var`/`Inputs.Value`/`Inputs.ProverValue`
companions are typed at the `Placed` cell environments.
-/

namespace Halo2

/-- Marker for derived halo2 `CircuitType`s, mirroring main Clean's
`DerivedCircuitType`: the eval bridges below hand `circuit_norm` the reduction from
the generic `Eval` calls to the derived instance's field-wise evaluators. -/
class DerivedCircuitType (M : TypeMap) extends CircuitType M

namespace DerivedCircuitType
variable {M : TypeMap} {F : Type} [FiniteField F] [DerivedCircuitType M]

@[circuit_norm]
theorem eval_verifier (env : Placed Environment F) :
    @Eval.eval (Placed Environment F) (Var M F) (Value M F)
      (CircuitType.verifierEval M) env
      = CircuitTypeOver.evalVerifier env := by rfl'

@[circuit_norm]
theorem eval_prover (env : Placed ProverEnvironment F) :
    @Eval.eval (Placed ProverEnvironment F) (Var M F) (ProverValue M F)
      (CircuitType.proverEval M) env
      = CircuitTypeOver.evalProver env := by rfl'

end DerivedCircuitType

end Halo2

namespace ProvableStructDeriving

open Lean Elab Command

/-- Halo2's profile (`Placed Environment`/`Placed ProverEnvironment`). -/
def halo2CircuitTypeProfile : CircuitTypeProfile where
  classConst := ``Halo2.CircuitType
  varConst := ``Halo2.Var
  valueConst := ``Halo2.Value
  proverValueConst := ``Halo2.ProverValue
  derivedConst := ``Halo2.DerivedCircuitType

/-- Halo2's `deriving CircuitType`. -/
def halo2CircuitTypeDerivingHandler (declNames : Array Name) : CommandElabM Bool :=
  circuitTypeDerivingHandlerWith halo2CircuitTypeProfile declNames

initialize registerDerivingHandler ``Halo2.CircuitType halo2CircuitTypeDerivingHandler

end ProvableStructDeriving
