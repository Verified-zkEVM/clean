import Clean.Circuit.Expression

/--
_Circuit types_ are usually just structured collections of field elements.

 We represent them as types generic over a single type argument (the field element),
 i.e. `Type → Type`.
-/
abbrev TypeMap := Type → Type

variable {F : Type} [Field F] {M : TypeMap}

/--
Generic typeclass for evaluation of a `Var` (symbolic circuit variable)
to a `Value` (concrete value in the field), in a given environment.

Generalizes verifier evaluation and prover evaluation for both provable types and prover hints.
-/
class Eval (Env : Type) (Var : Type) (Value : outParam Type) where
  eval : Env → Var → Value

/-
`eval` is designed to be the normal form of evaluation statements across instances.
It is marked irreducible so it stays intact instead of being replaced by particular
`Eval` instance implementations on specialization/unfolding/whnf.
Normalization should go through explicit simp lemmas (`circuit_norm`, `explicit_provable_type`) instead.
-/
attribute [irreducible] Eval.eval

export Eval (eval)

/-- Verifier evaluation is `Eval` specialized to `Environment F`. -/
@[circuit_norm]
abbrev VerifierEval (F : Type) Var (Value : outParam Type) := Eval (Environment F) Var Value

/-- Prover evaluation is `Eval` specialized to `ProverEnvironment F`. -/
@[circuit_norm]
abbrev ProverEval (F : Type) Var (Value : outParam Type) := Eval (ProverEnvironment F) Var Value

/--
Explicit verifier view: even on a `ProverEnvironment`, this forces the verifier
instance via the `ProverEnvironment → Environment` projection.
-/
abbrev evalVerifier {F Var Value} [VerifierEval F Var Value]
  (env : Environment F) (v : Var) : Value := eval env v

/-- Explicit prover view. -/
abbrev evalProver {F Var Value} [ProverEval F Var Value]
  (env : ProverEnvironment F) (v : Var) : Value := eval env v

/--
`CircuitType M` bundles three derived types (`Var`, `Value`, `ProverValue`)
and two eval functions that map the variable form to the two value forms
(verifier-view, prover-view).

For fully provable schemas (no hint fields), the verifier- and prover-value forms
coincide; see the default instance in `Provable.lean`.
-/
class CircuitType (M : TypeMap) where
  /--
  An element of `Var M F` represents a `M F` that's polynomially dependent
  on the environment. More concretely, an element of `Var M F` is a value of `M F`
  with missing holes, and each hole contains a polynomial that can refer to fixed
  positions of the environment.
  -/
  Var : TypeMap
  /-- Verifier value: hint fields are erased to `Unit`. -/
  Value : TypeMap
  /-- Prover value: hint fields carry their underlying type. -/
  ProverValue : TypeMap
  evalVerifier : ∀ {F : Type} [Field F], Environment F → Var F → Value F
  evalProver   : ∀ {F : Type} [Field F], ProverEnvironment F → Var F → ProverValue F

export CircuitType (Var Value ProverValue)

namespace CircuitType
variable [CircuitType M]

attribute [circuit_norm] evalVerifier evalProver

/--
A `CircuitType M` instance induces a verifier-side `Eval` on `Var M F`.
This lets `eval env var` work uniformly whether the Var came from a `ProvableType`-derived
instance or a hand-written one.
-/
instance verifierEval M [CircuitType M] :
  VerifierEval F (Var M F) (Value M F) := ⟨ evalVerifier ⟩

/- `CircuitType` induces a prover-side `Eval` on `Var M F`. -/
instance proverEval M [CircuitType M] :
  ProverEval F (Var M F) (ProverValue M F) := ⟨ evalProver ⟩

lemma eval_verifier (env : Environment F) (v : Var M F) :
  eval env v = evalVerifier env v := by
  unfold eval
  rfl

lemma eval_prover (env : ProverEnvironment F) (v : Var M F) :
  eval env v = evalProver env v := by
  unfold eval
  rfl
end CircuitType

/--
`Unconstrained` acts as a type marker for circuit inputs that should only be hints to the prover.
-/
structure Unconstrained (Hint : Type) (F : Type) where
  value : Hint

variable {Hint : Type}

instance Unconstrained.toCircuitType : CircuitType (Unconstrained Hint) where
  Var F := ProverEnvironment F → Hint
  ProverValue _ := Hint
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env v := v env

namespace CircuitType
@[circuit_norm] lemma var_of_unconstrained (Hint F) :
  Var (Unconstrained Hint) F = (ProverEnvironment F → Hint) := rfl
@[circuit_norm] lemma proverValue_of_unconstrained (Hint F) :
  ProverValue (Unconstrained Hint) F = Hint := rfl
@[circuit_norm] lemma value_of_unconstrained (Hint F) :
  Value (Unconstrained Hint) F = Unit := rfl

/- forwarding instances to help instance search get through defeq -/
instance : VerifierEval F (ProverEnvironment F → Hint) Unit := verifierEval (Unconstrained Hint)
instance : ProverEval F (ProverEnvironment F → Hint) Hint := proverEval (Unconstrained Hint)

@[circuit_norm] lemma eval_unconstrained (env : Environment F) (v : ProverEnvironment F → Hint) :
  eval env v = () := by rfl

@[circuit_norm] lemma eval_unconstrained_prover (env : ProverEnvironment F)
    (v : ProverEnvironment F → Hint) :
    eval env v = v env := by
  rw [eval_prover (M := Unconstrained Hint)]
  rfl
end CircuitType

/--
`UnconstrainedDep` is the field-dependent version of `Unconstrained`.
Use it when the prover-only hint itself mentions the circuit field type.
-/
structure UnconstrainedDep (Hint : TypeMap) (F : Type) where
  value : Hint F

variable {HintMap : TypeMap}

instance UnconstrainedDep.toCircuitType : CircuitType (UnconstrainedDep HintMap) where
  Var F := ProverEnvironment F → HintMap F
  ProverValue F := HintMap F
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env v := v env

namespace CircuitType
@[circuit_norm] lemma var_of_unconstrainedDep (Hint F) :
  Var (UnconstrainedDep Hint) F = (ProverEnvironment F → Hint F) := rfl
@[circuit_norm] lemma proverValue_of_unconstrainedDep (Hint F) :
  ProverValue (UnconstrainedDep Hint) F = Hint F := rfl
@[circuit_norm] lemma value_of_unconstrainedDep (Hint F) :
  Value (UnconstrainedDep Hint) F = Unit := rfl

/- forwarding instances to help instance search get through defeq -/
instance : VerifierEval F (ProverEnvironment F → HintMap F) Unit :=
  verifierEval (UnconstrainedDep HintMap)
instance : ProverEval F (ProverEnvironment F → HintMap F) (HintMap F) :=
  proverEval (UnconstrainedDep HintMap)

@[circuit_norm] lemma eval_unconstrainedDep (env : Environment F)
    (v : ProverEnvironment F → HintMap F) :
  eval env v = () := by rfl

@[circuit_norm] lemma eval_unconstrainedDep_prover (env : ProverEnvironment F)
    (v : ProverEnvironment F → HintMap F) :
    eval env v = v env := by
  rw [eval_prover (M := UnconstrainedDep HintMap)]
  rfl
end CircuitType
