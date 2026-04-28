import Clean.Circuit
import Clean.Types.U32

namespace TestCircuitStructDeriving

structure Inputs (F : Type) where
  someElement : U32 F
  someHint : Unconstrained Bool F
deriving CircuitType

example : CircuitType Inputs := inferInstance

example {F : Type} [Field F] (input : Var Inputs F) : Var U32 F :=
  input.someElement

example {F : Type} [Field F] (input : Var Inputs F) : ProverEnvironment F → Bool :=
  input.someHint

example {F : Type} [Field F] (input : Value Inputs F) : U32 F :=
  input.someElement

example {F : Type} [Field F] (input : Value Inputs F) : Unit :=
  input.someHint

example {F : Type} [Field F] (input : ProverValue Inputs F) : U32 F :=
  input.someElement

example {F : Type} [Field F] (input : ProverValue Inputs F) : Bool :=
  input.someHint

example {F : Type} [Field F] (env : Environment F) (input : Var Inputs F) :
    eval env input = Inputs.Value.mk (eval env input.someElement) () := by
  rw [CircuitType.eval_verifier]
  rfl

example {F : Type} [Field F] (env : ProverEnvironment F) (input : Var Inputs F) :
    eval env input = Inputs.ProverValue.mk (eval env input.someElement) (eval env input.someHint) := by
  rw [CircuitType.eval_prover]
  rfl

structure InputWithProp (F : Type) where
  bool : F
  hint : Unconstrained Bool F
  same_content [Field F] : bool = if hint.value then 1 else 0
deriving CircuitType

example : CircuitType InputWithProp := by infer_instance

example {F : Type} [Field F] (input : InputWithProp.Var F) (env : ProverEnvironment F) :
    eval env input.bool = if eval env input.hint then 1 else 0 :=
  input.same_content env

example {F : Type} [Field F] (input : InputWithProp.ProverValue F) :
    input.bool = if input.hint then 1 else 0 :=
  input.same_content

structure InputWithPlainProp (F : Type) where
  bool : F
  always : True
deriving CircuitType

example : CircuitType InputWithPlainProp := by infer_instance

example {F : Type} [Field F] (input : InputWithPlainProp.ProverValue F) :
    True :=
  input.always

end TestCircuitStructDeriving
