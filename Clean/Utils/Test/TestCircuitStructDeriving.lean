import Clean.Circuit
import Clean.Types.U32

namespace TestCircuitStructDeriving

structure Inputs (F : Type) where
  someElement : U32 F
  someHint : UnconstrainedNative Bool F
deriving CircuitType

example : CircuitType Inputs := inferInstance

example {F : Type} [FiniteField F] (input : Var Inputs F) : Var U32 F :=
  input.someElement

example {F : Type} [FiniteField F] (input : Var Inputs F) : ProverEnvironment F → Bool :=
  input.someHint

example {F : Type} [FiniteField F] (input : Value Inputs F) : U32 F :=
  input.someElement

example {F : Type} [FiniteField F] (input : Value Inputs F) : Unit :=
  input.someHint

example {F : Type} [FiniteField F] (input : ProverValue Inputs F) : U32 F :=
  input.someElement

example {F : Type} [FiniteField F] (input : ProverValue Inputs F) : Bool :=
  input.someHint

example {F : Type} [FiniteField F] (env : Environment F) (input : Var Inputs F) :
    eval env input = Inputs.Value.mk (eval env input.someElement) () := by
  rw [CircuitType.eval_verifier]
  rfl

example {F : Type} [FiniteField F] (env : ProverEnvironment F) (input : Var Inputs F) :
    eval env input = Inputs.ProverValue.mk (eval env input.someElement) (eval env input.someHint) := by
  rw [CircuitType.eval_prover]
  rfl

end TestCircuitStructDeriving
