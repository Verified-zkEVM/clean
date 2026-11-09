import Clean.Circuit.Expression
import Clean.Utils.FiniteField

/--
_Circuit types_ are usually just structured collections of field elements.

 We represent them as types generic over a single type argument (the field element),
 i.e. `Type → Type`.
-/
abbrev TypeMap := Type → Type

variable {F : Type} [FiniteField F] {M : TypeMap}

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

namespace Clean

/-- Verifier evaluation is `Eval` specialized to `Environment F`. -/
@[circuit_norm]
abbrev VerifierEval (F : Type) Var (Value : outParam Type) := Eval (Environment F) Var Value

/-- Prover evaluation is `Eval` specialized to `ProverEnvironment F`. -/
@[circuit_norm]
abbrev ProverEval (F : Type) Var (Value : outParam Type) := Eval (ProverEnvironment F) Var Value

/--
Evaluation into `Unit` is trivial (e.g. the verifier view of prover-only hints).
Stated for an arbitrary instance so it fires regardless of how the instance
argument was normalized; holds by `Unit` eta.
-/
@[circuit_norm]
lemma eval_unit {Env X : Type} [Eval Env X Unit] (env : Env) (v : X) :
    eval env v = () := rfl

/--
Explicit verifier view: even on a `ProverEnvironment`, this forces the verifier
instance via the `ProverEnvironment → Environment` projection.
-/
abbrev evalVerifier {F Var Value} [VerifierEval F Var Value]
  (env : Environment F) (v : Var) : Value := eval env v

/-- Explicit prover view. -/
abbrev evalProver {F Var Value} [ProverEval F Var Value]
  (env : ProverEnvironment F) (v : Var) : Value := eval env v

end Clean

/--
`CircuitTypeOver Env PEnv M` bundles three derived types (`Var`, `Value`, `ProverValue`)
and two eval functions that map the variable form to the two value forms
(verifier-view, prover-view), for a given pair of environment types.

Main Clean instantiates the environments with `Environment`/`ProverEnvironment` (see the
`CircuitType` abbreviation); Halo2-Clean instantiates them with its placed cell
environments.

For fully provable schemas (no hint fields), the verifier- and prover-value forms
coincide; see the default instance in `Provable.lean`.
-/
class CircuitTypeOver (Env PEnv : Type → Type) (M : TypeMap) where
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
  evalVerifier : ∀ {F : Type} [FiniteField F], Env F → Var F → Value F
  evalProver   : ∀ {F : Type} [FiniteField F], PEnv F → Var F → ProverValue F

namespace Clean

/-- Main Clean's `CircuitType`: `CircuitTypeOver` at the tape-indexed
`Environment`/`ProverEnvironment`. -/
abbrev CircuitType (M : TypeMap) := CircuitTypeOver Environment ProverEnvironment M

/- Main-specialized views of the bundled types. These keep the established names
`Var M F`/`Value M F`/`ProverValue M F` deterministic: the raw generic projections would
leave `Env`/`PEnv` to instance search, which becomes ambiguous once several environment
instantiations are in scope. Frameworks over other environments define their own views
(e.g. `Halo2.Var`). -/
@[reducible] def CircuitType.Var (M : TypeMap) [CircuitType M] : TypeMap :=
  CircuitTypeOver.Var (Env := Environment) (PEnv := ProverEnvironment) (M := M)
@[reducible] def CircuitType.Value (M : TypeMap) [CircuitType M] : TypeMap :=
  CircuitTypeOver.Value (Env := Environment) (PEnv := ProverEnvironment) (M := M)
@[reducible] def CircuitType.ProverValue (M : TypeMap) [CircuitType M] : TypeMap :=
  CircuitTypeOver.ProverValue (Env := Environment) (PEnv := ProverEnvironment) (M := M)

namespace CircuitType
export CircuitTypeOver (evalVerifier evalProver)
end CircuitType

export CircuitType (Var Value ProverValue)

namespace CircuitType
variable [CircuitType M]

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
  eval env v = evalVerifier env v := by with_unfolding_all rfl

lemma eval_prover (env : ProverEnvironment F) (v : Var M F) :
  eval env v = evalProver env v := by with_unfolding_all rfl

-- the normal form of evaluation is `eval`; but once we specialize it to a particular `CircuitType`,
-- by applying `eval_verifier` or `eval_prover`, we want to immediately simplify the resulting
-- `evalVerifier` or `evalProver` to their definitions.
attribute [circuit_norm] evalVerifier evalProver
end CircuitType

/--
Marker class for `CircuitType`s generated by the deriving handler.

Tactics/simp lemmas use this opt-in to expose and split generated record types while leaving
hand-written `CircuitType`s opaque by default.
-/
class DerivedCircuitType (M : TypeMap) extends CircuitType M

namespace DerivedCircuitType
variable [DerivedCircuitType M]

@[circuit_norm]
theorem eval_verifier (env : Environment F) :
  @eval (Environment F) (Var M F) (Value M F) (CircuitType.verifierEval M) env
    = CircuitType.evalVerifier env := by rfl'

@[circuit_norm]
theorem eval_prover (env : ProverEnvironment F) :
  @eval (ProverEnvironment F) (Var M F) (ProverValue M F) (CircuitType.proverEval M) env
    = CircuitType.evalProver env := by rfl'
end DerivedCircuitType
end Clean

/-- Marker for record types the struct-decomposition tactics may destructure
componentwise beyond `ProvableStruct`: generated for `deriving CircuitType`'s
`Var`/`Value`/`ProverValue` view companions (mixed provable/hint records have no
`ProvableStruct` instance, but their views are plain structures `cases` can split). -/
class DecomposableStruct (M : Type → Type) : Prop where

/--
`UnconstrainedNative` acts as a type marker for circuit inputs that should only be hints to the prover.
-/
structure UnconstrainedNative (Hint : Type) (F : Type) where
  value : Hint

variable {Hint : Type}

@[reducible] instance UnconstrainedNative.toCircuitType {Env PEnv : Type → Type} :
    CircuitTypeOver Env PEnv (UnconstrainedNative Hint) where
  Var F := PEnv F → Hint
  ProverValue _ := Hint
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env v := v env

namespace Clean.CircuitType
@[circuit_norm] lemma var_of_unconstrainedNative (Hint F) :
  Var (UnconstrainedNative Hint) F = (ProverEnvironment F → Hint) := rfl
@[circuit_norm] lemma proverValue_of_unconstrainedNative (Hint F) :
  ProverValue (UnconstrainedNative Hint) F = Hint := rfl
@[circuit_norm] lemma value_of_unconstrainedNative (Hint F) :
  Value (UnconstrainedNative Hint) F = Unit := rfl

/- forwarding instances to help instance search get through defeq -/
instance : VerifierEval F (ProverEnvironment F → Hint) Unit := verifierEval (UnconstrainedNative Hint)
instance : ProverEval F (ProverEnvironment F → Hint) Hint := proverEval (UnconstrainedNative Hint)

instance [Inhabited Hint] : Inhabited (Var (UnconstrainedNative Hint) F) where
  default := fun _ => default

@[circuit_norm] lemma eval_unconstrainedNative (env : Environment F) (v : ProverEnvironment F → Hint) :
  eval env v = () := by rfl

@[circuit_norm] lemma eval_unconstrainedNative_prover (env : ProverEnvironment F)
    (v : ProverEnvironment F → Hint) :
    eval env v = v env := by
  rw [eval_prover (M := UnconstrainedNative Hint)]
  rfl
end Clean.CircuitType

/--
`UnconstrainedDepNative` is the field-dependent version of `UnconstrainedNative`.
Use it when the prover-only hint itself mentions the circuit field type.
-/
structure UnconstrainedDepNative (Hint : TypeMap) (F : Type) where
  value : Hint F

variable {HintMap : TypeMap}

@[reducible] instance UnconstrainedDepNative.toCircuitType {Env PEnv : Type → Type} :
    CircuitTypeOver Env PEnv (UnconstrainedDepNative HintMap) where
  Var F := PEnv F → HintMap F
  ProverValue F := HintMap F
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env v := v env

namespace Clean.CircuitType
@[circuit_norm] lemma var_of_unconstrainedDepNative (Hint F) :
  Var (UnconstrainedDepNative Hint) F = (ProverEnvironment F → Hint F) := rfl
@[circuit_norm] lemma proverValue_of_unconstrainedDepNative (Hint F) :
  ProverValue (UnconstrainedDepNative Hint) F = Hint F := rfl
@[circuit_norm] lemma value_of_unconstrainedDepNative (Hint F) :
  Value (UnconstrainedDepNative Hint) F = Unit := rfl

/- forwarding instances to help instance search get through defeq -/
instance : VerifierEval F (ProverEnvironment F → HintMap F) Unit :=
  verifierEval (UnconstrainedDepNative HintMap)
instance : ProverEval F (ProverEnvironment F → HintMap F) (HintMap F) :=
  proverEval (UnconstrainedDepNative HintMap)

instance [Inhabited (HintMap F)] : Inhabited (Var (UnconstrainedDepNative HintMap) F) where
  default := fun _ => default

@[circuit_norm] lemma eval_unconstrainedDepNative (env : Environment F)
    (v : ProverEnvironment F → HintMap F) :
  eval env v = () := by rfl

@[circuit_norm] lemma eval_unconstrainedDepNative_prover (env : ProverEnvironment F)
    (v : ProverEnvironment F → HintMap F) :
    eval env v = v env := by
  rw [eval_prover (M := UnconstrainedDepNative HintMap)]
  rfl
end Clean.CircuitType
