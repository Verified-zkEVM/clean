import Clean.Circuit.Provable

variable {F : Type} [Field F] {M N : TypeMap} [ProvableType M] [ProvableType N] {Hint : Type}

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

`CircuitType Input` bundles the three derived types (`Var`, `ProverValue`, `VerifierValue`)
and the two eval functions that map the variable form to the two value forms
(verifier-view, prover-view).

Parallel to `ProvableType α`: one class parameterized by a schema `Input : TypeMap`,
with the derived types as fields. A `GeneralFormalCircuit` can then be parameterized
as `(Input Output : TypeMap) [CircuitType Input] [CircuitType Output]`.

For pure-provable schemas (no hint fields) the verifier- and prover-value forms
coincide — see the default instance below.
-/

class CircuitType (Input : TypeMap) where
  /-- Variable form used in `main` (what circuits operate on). -/
  Var : TypeMap
  /-- Prover value — hint fields carry their underlying type. -/
  ProverValue : TypeMap
  /-- Verifier value — hint fields are erased to `Unit`. -/
  VerifierValue : TypeMap
  evalVerifier : ∀ {F : Type} [Field F], Environment F → Var F → VerifierValue F
  evalProver   : ∀ {F : Type} [Field F], ProverEnvironment F → Var F → ProverValue F

variable {Input : TypeMap} [CircuitType Input]

/--
Default `CircuitType` for any `ProvableType`: verifier- and prover-value coincide
with the input type, and `Var` is the usual `α ∘ Expression`.
-/
instance ProvableType.toCircuitType {α : TypeMap} [ProvableType α] : CircuitType α where
  Var := Var α
  ProverValue := α
  VerifierValue := α
  evalVerifier env v := ProvableType.eval env v
  evalProver env v := ProvableType.eval env v

instance Unconstrained.toCircuitType {Hint : Type} : CircuitType (Unconstrained Hint) where
  Var := ProverHint Hint
  ProverValue _ := Hint
  VerifierValue _ := Unit
  evalVerifier _ _ := ()
  evalProver env v := v env

namespace CircuitType
@[circuit_norm] lemma var_of_provableType (F) :
  Var M F = _root_.Var M F := rfl
@[circuit_norm] lemma proverValue_of_provableType (F) :
  ProverValue M F = M F := rfl
@[circuit_norm] lemma verifierValue_of_provableType (F) :
  VerifierValue M F = M F := rfl

@[circuit_norm] lemma var_of_unconstrained (Hint F) :
  Var (Unconstrained Hint) F = ProverHint Hint F := rfl
@[circuit_norm] lemma proverValue_of_unconstrained (Hint F) :
  ProverValue (Unconstrained Hint) F = Hint := rfl
@[circuit_norm] lemma verifierValue_of_unconstrained (Hint F) :
  VerifierValue (Unconstrained Hint) F = Unit := rfl

/--
A `CircuitType Input` instance induces a verifier-side `Eval` on `CircuitType.Var Input F`.
This lets `eval env var` work uniformly whether the Var came from a `ProvableType`-derived
instance or a hand-written one.
-/
@[circuit_norm]
instance verifierEval (M : TypeMap) [CircuitType M] :
  VerifierEval F (Var M F) (VerifierValue M F) := ⟨ evalVerifier ⟩

/- `CircuitType` induces a prover-side `Eval` on `CircuitType.Var Input F`. -/
@[circuit_norm]
instance proverEval (M : TypeMap) [CircuitType M] :
  ProverEval F (Var M F) (ProverValue M F) := ⟨ evalProver ⟩

@[circuit_norm] lemma eval_verifier (env : Environment F) (v : Var M F) :
  eval' env v = evalVerifier env v := rfl
@[circuit_norm] lemma eval_prover (env : ProverEnvironment F) (v : Var M F) :
  eval' env v = evalProver env v := rfl

/- forwarding instances to help instance search get through defeq -/

@[circuit_norm] instance : VerifierEval F (ProverHint Hint F) Unit := verifierEval (Unconstrained Hint)
@[circuit_norm] instance : ProverEval F (ProverHint Hint F) Hint := proverEval (Unconstrained Hint)
@[circuit_norm] instance : VerifierEval F (_root_.Var M F) (M F) := verifierEval M
@[circuit_norm] instance : ProverEval F (_root_.Var M F) (M F) := proverEval M
@[circuit_norm] instance : VerifierEval F (Expression F) F := verifierEval field
@[circuit_norm] instance : ProverEval F (Expression F) F := proverEval field
@[circuit_norm] instance : VerifierEval F (_root_.Var M F × _root_.Var N F) (M F × N F) := verifierEval (ProvablePair M N)
@[circuit_norm] instance : ProverEval F (_root_.Var M F × _root_.Var N F) (M F × N F) := proverEval (ProvablePair M N)
@[circuit_norm] instance : VerifierEval F (_root_.Var field F × _root_.Var field F) (F × F) := verifierEval (ProvablePair field field)
@[circuit_norm] instance : ProverEval F (_root_.Var field F × _root_.Var field F) (F × F) := proverEval (ProvablePair field field)
@[circuit_norm] instance {n : ℕ} : VerifierEval F (_root_.Var (fields n) F) (fields n F) := verifierEval (fields n)
@[circuit_norm] instance {n : ℕ} : ProverEval F (_root_.Var (fields n) F) (fields n F) := proverEval (fields n)

/-!
## Simp bridges

`circuit_norm` should normalize a dispatched evaluation `eval` to a concrete one
(`Expression.eval` / `ProvableType.eval` / the underlying hint computation), so that
the existing `circuit_norm` lemma library — which speaks `ProvableType.eval` and
`Expression.eval` — continues to fire.

Lemmas are stated on `eval` (the primary API); goals or hypotheses written with
`evalVerifier` / `evalProver` (which are `abbrev`s over `eval`) match by reducibility.

All are `rfl` thanks to the corresponding `Eval` instance.
-/

attribute [circuit_norm] eval' evalVerifier evalProver

-- TODO we also need to simp toElements and fromElements to their ProvableType versions
-- all the lemmas that prove using `simp only [circuit_norm]` might actually not be needed

@[circuit_norm] lemma eval_expr (env : Environment F) (v : Expression F) :
  eval' env v = Expression.eval env v := by simp only [circuit_norm]

@[circuit_norm] lemma eval_expr_prover (env : ProverEnvironment F) (v : Expression F) :
  eval' env v = Expression.eval env v := by simp only [circuit_norm]

@[circuit_norm] lemma eval_var (env : Environment F) (v : _root_.Var M F) :
  eval' env v = ProvableType.eval env v := by simp only [circuit_norm]

@[circuit_norm] lemma eval_var_prover (env : ProverEnvironment F) (v : _root_.Var M F) :
  eval' env v = ProvableType.eval env v := by simp only [circuit_norm]

@[circuit_norm] lemma eval_hint (env : Environment F) (v : ProverHint Hint F) :
  eval' env v = () := by simp only [circuit_norm]

@[circuit_norm] lemma eval_hint_prover (env : ProverEnvironment F) (v : ProverHint Hint F) :
  eval' env v = v env := by simp only [circuit_norm]

@[circuit_norm] lemma eval_var_field (env : Environment F) (v : _root_.Var field F) :
  eval' env v = Expression.eval env v := by simp only [circuit_norm]

@[circuit_norm] lemma eval_var_field_prover (env : ProverEnvironment F) (v : _root_.Var field F) :
  eval' env v = Expression.eval env v := by simp only [circuit_norm]

@[circuit_norm] lemma eval_var_pair (env : Environment F) (p1 : _root_.Var M F) (p2 : _root_.Var N F) :
    eval' (Var := _root_.Var (ProvablePair M N) F) env (p1, p2) = (eval' env p1, eval' env p2) := by
  simp only [circuit_norm]

@[circuit_norm] lemma eval_var_pair_prover (env : ProverEnvironment F) (p1 : _root_.Var M F) (p2 : _root_.Var N F) :
    eval' (Var := _root_.Var (ProvablePair M N) F) env (p1, p2) = (eval' env p1, eval' env p2) := by
  simp only [circuit_norm]

@[circuit_norm] lemma eval_field_pair (F : Type) [Field F]
  (env : Environment F) (p1 : _root_.Var field F) (p2 : _root_.Var field F) :
    eval' (Var := _root_.Var (ProvablePair field field) F) env (p1, p2) = (eval' env p1, eval' env p2) := by
  simp only [circuit_norm]

@[circuit_norm] lemma eval_field_pair_prover (F : Type) [Field F]
  (env : ProverEnvironment F) (p1 : _root_.Var field F) (p2 : _root_.Var field F) :
    eval' (Var := _root_.Var (ProvablePair field field) F) env (p1, p2) = (eval' env p1, eval' env p2) := by
  simp only [circuit_norm]

@[circuit_norm] lemma eval_fields (F : Type) [Field F] {n : ℕ}
  (env : Environment F) (xs : _root_.Var (fields n) F) :
    eval' (Var := _root_.Var (fields n) F) env xs = ProvableType.eval env xs := by
  simp only [circuit_norm]

@[circuit_norm] lemma eval_fields_prover (F : Type) [Field F] {n : ℕ}
  (env : ProverEnvironment F) (xs : _root_.Var (fields n) F) :
    eval' (Var := _root_.Var (fields n) F) env xs = ProvableType.eval env xs := by
  simp only [circuit_norm]

end CircuitType
