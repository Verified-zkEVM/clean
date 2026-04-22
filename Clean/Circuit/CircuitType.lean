import Clean.Circuit.Provable

structure Unconstrained (Hint : Type) where
  value : Hint

/-
  Prover hints: additional data that can be passed to a circuit's witness generation
  but does not affect the circuit's constraints or spec.
-/
def ProverHint (Hint : Type) (F : Type) := ProverEnvironment F → Hint

/--
`CircuitType` is a joint generalization of `ProvableType` and `ProverHint`.
It allows us to pass both committed witnesses and unconstrained prover hints to a circuit.

The only thing we require of a `CircuitType` is that we can evaluate it given an `Environment`.
-/
class CircuitType (F : Type) (Var : Type) (Value : outParam Type) where
  evalVerifier [Field F] : Environment F → Var → Value

class ProverType (F : Type) (Var : Type) (Value : outParam Type) where
  evalProver [Field F] : ProverEnvironment F → Var → Value

class Eval (Env : Type) where
  Var : Type
  Value : Type
  eval : Env → Var → Value

export CircuitType (evalVerifier)
export ProverType (evalProver)
export Eval (eval)

variable {F : Type} [Field F] {M : TypeMap} [ProvableType M] {Hint : Type}
variable {Variable : Type} {Value : Type}

instance Eval.verifier [CircuitType F Variable Value] : Eval (Environment F) where
  Var := Variable
  Value := Value
  eval := evalVerifier

instance Eval.prover [ProverType F Variable Value] : Eval (ProverEnvironment F) where
  Var := Variable
  Value := Value
  eval := evalProver

@[circuit_norm] lemma eval_eq_evalVerifier [CircuitType F Variable Value]
 {env : Environment F} (var : Variable) :
  eval env var = evalVerifier env var := rfl

@[circuit_norm] lemma eval_eq_evalProver [ProverType F Variable Value]
 {env : ProverEnvironment F} (var : Variable) :
  eval env var = evalProver env var := rfl

instance {F : Type} : CircuitType F (ProverHint Hint F) Unit where
  evalVerifier _ _ := ()

instance {F : Type} : ProverType F (ProverHint Hint F) Hint where
  evalProver env h := h env

instance {F : Type} : CircuitType F (Var M F) (M F) where
  evalVerifier env v := ProvableType.eval env v

instance {F : Type} : ProverType F (Var M F) (M F) where
  evalProver env v := ProvableType.eval env v

instance {F : Type} : CircuitType F (M (Expression F)) (M F) where
  evalVerifier env v := ProvableType.eval env v

instance {F : Type} : ProverType F (M (Expression F)) (M F) where
  evalProver env v := ProvableType.eval env v

instance {F : Type} : CircuitType F (Expression F) F where
  evalVerifier env v := Expression.eval env v

instance {F : Type} : ProverType F (Expression F) F where
  evalProver env v := Expression.eval env v

-- TODO need simp lemmas!!
