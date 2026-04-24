import Clean.Circuit.Expression

/--
'Provable types' are structured collections of field elements.

 We represent them as types generic over a single type argument (the field element),
 i.e. `Type → Type`.
-/
@[reducible]
def TypeMap := Type → Type

variable {F : Type} [Field F] {M N : TypeMap} {Hint : Type}

structure Unconstrained (Hint : Type) (F : Type) where
  value : Hint

/-
  Prover hints: additional data that can be passed to a circuit's witness generation
  but does not affect the circuit's constraints or spec.
-/
def ProverHint (Hint : Type) (F : Type) := ProverEnvironment F → Hint

/--
`Eval Env Var Value` says: in environment `Env`, a term `v : Var` evaluates to `Value`.

Generalizes verifier evaluation (`Env = Environment F`) and prover evaluation (`Env = ProverEnvironment F`),
for both `ProvableType` variables and `ProverHint` hints.

The `Var → Value` mapping is per-instance, so verifier- and prover-side can
disagree: e.g. a `ProverHint Hint F` evaluates to `Unit` under `Environment F` but to
`Hint` under `ProverEnvironment F`.
-/
class Eval (Env : Type) (Var : Type) (Value : outParam Type) where
  eval' : Env → Var → Value

export Eval (eval')

/-- Verifier evaluation is `Eval` specialized to `Environment F`. -/
@[circuit_norm]
abbrev VerifierEval (F : Type) Var (Value : outParam Type) := Eval (Environment F) Var Value

/-- Prover evaluation is `Eval` specialized to `ProverEnvironment F`. -/
@[circuit_norm]
abbrev ProverEval (F : Type) Var (Value : outParam Type) := Eval (ProverEnvironment F) Var Value

/--
Explicit "verifier view" — even on a `ProverEnvironment`, this forces the verifier
instance via the `ProverEnvironment → Environment` projection.
-/
abbrev evalVerifier {F Var Value} [VerifierEval F Var Value]
  (env : Environment F) (v : Var) : Value := eval' env v

/-- Explicit "prover view" — only applies where a `ProverEnvironment` is available. -/
abbrev evalProver {F Var Value} [ProverEval F Var Value]
  (env : ProverEnvironment F) (v : Var) : Value := eval' env v

/-!
## `CircuitType`: the schema-level class for circuit I/O

`CircuitType Input` bundles the three derived types (`Var`, `ProverValue`, `Value`)
and the two eval functions that map the variable form to the two value forms
(verifier-view, prover-view).

Parallel to `ProvableType α`: one class parameterized by a schema `Input : TypeMap`,
with the derived types as fields. A `GeneralFormalCircuit` can then be parameterized
as `(Input Output : TypeMap) [CircuitType Input] [CircuitType Output]`.

For pure-provable schemas (no hint fields) the verifier- and prover-value forms
coincide — see the default instance in `Provable.lean`.
-/

class CircuitType (Input : TypeMap) where
  /--
  `Var M F` is the type of variables that appear in the monadic notation of
  `Circuit F _`s. Most elements of `Var M F`, especially interesting ones, are not
  constant values of `M F` because variables in a circuit can depend on contents of
  the environment.

  An element of `Var M F` represents a `M F` that's polynomially dependent
  on the environment. More concretely, an element of `Var M F` is a value of `M F`
  with missing holes, and each hole contains a polynomial that can refer to fixed
  positions of the environment. Given an environment, `Var M F` can be evaluated
  to a `M F` (see `eval` below).
  -/
  Var : TypeMap
  /-- Prover value — hint fields carry their underlying type. -/
  ProverValue : TypeMap
  /-- Verifier value — hint fields are erased to `Unit`. -/
  Value : TypeMap
  evalVerifier : ∀ {F : Type} [Field F], Environment F → Var F → Value F
  evalProver   : ∀ {F : Type} [Field F], ProverEnvironment F → Var F → ProverValue F

export CircuitType (Var)

variable {Input : TypeMap} [CircuitType Input]

instance Unconstrained.toCircuitType {Hint : Type} : CircuitType (Unconstrained Hint) where
  Var := ProverHint Hint
  ProverValue _ := Hint
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env v := v env

namespace CircuitType
@[circuit_norm] lemma var_of_unconstrained (Hint F) :
  Var (Unconstrained Hint) F = ProverHint Hint F := rfl
@[circuit_norm] lemma proverValue_of_unconstrained (Hint F) :
  ProverValue (Unconstrained Hint) F = Hint := rfl
@[circuit_norm] lemma value_of_unconstrained (Hint F) :
  Value (Unconstrained Hint) F = Unit := rfl

/--
A `CircuitType Input` instance induces a verifier-side `Eval` on `Var Input F`.
This lets `eval env var` work uniformly whether the Var came from a `ProvableType`-derived
instance or a hand-written one.
-/
@[circuit_norm]
instance verifierEval (M : TypeMap) [CircuitType M] :
  VerifierEval F (Var M F) (Value M F) := ⟨ evalVerifier ⟩

/- `CircuitType` induces a prover-side `Eval` on `Var Input F`. -/
@[circuit_norm]
instance proverEval (M : TypeMap) [CircuitType M] :
  ProverEval F (Var M F) (ProverValue M F) := ⟨ evalProver ⟩

@[circuit_norm] lemma eval_verifier [CircuitType M] (env : Environment F) (v : Var M F) :
  eval' env v = evalVerifier env v := rfl
@[circuit_norm] lemma eval_prover [CircuitType M] (env : ProverEnvironment F) (v : Var M F) :
  eval' env v = evalProver env v := rfl

/- forwarding instances to help instance search get through defeq -/

@[circuit_norm] instance : VerifierEval F (ProverHint Hint F) Unit := verifierEval (Unconstrained Hint)
@[circuit_norm] instance : ProverEval F (ProverHint Hint F) Hint := proverEval (Unconstrained Hint)

/-!
## Simp bridges

`circuit_norm` should normalize a dispatched evaluation `eval` to a concrete one
(`Expression.eval` / `ProvableType.eval` / the underlying hint computation), so that
the existing `circuit_norm` lemma library — which speaks `ProvableType.eval` and
`Expression.eval` — continues to fire.

Lemmas are stated on `eval` (the primary API); goals or hypotheses written with
`evalVerifier` / `evalProver` (which are `abbrev`s over `eval`) match by reducibility.

All are `rfl` thanks to the corresponding `Eval` instance.

ProvableType-specific bridges live in `Provable.lean`.
-/

attribute [circuit_norm] eval' evalVerifier evalProver

-- TODO we also need to simp toElements and fromElements to their ProvableType versions
-- all the lemmas that prove using `simp only [circuit_norm]` might actually not be needed

@[circuit_norm] lemma eval_hint (env : Environment F) (v : ProverHint Hint F) :
  eval' env v = () := by simp only [circuit_norm]

@[circuit_norm] lemma eval_hint_prover (env : ProverEnvironment F) (v : ProverHint Hint F) :
  eval' env v = v env := by simp only [circuit_norm]

end CircuitType
