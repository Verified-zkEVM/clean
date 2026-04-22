import Clean.Circuit.Provable

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
  eval : Env → Var → Value

export Eval (eval)

/-- Verifier evaluation is `Eval` specialized to `Environment F`. -/
@[circuit_norm]
abbrev VerifierEval (F : Type) (Var : Type) (Value : outParam Type) :=
  Eval (Environment F) Var Value

/-- Prover evaluation is `Eval` specialized to `ProverEnvironment F`. -/
@[circuit_norm]
abbrev ProverEval (F : Type) (Var : Type) (Value : outParam Type) :=
  Eval (ProverEnvironment F) Var Value

/--
Explicit "verifier view" — even on a `ProverEnvironment`, this forces the verifier
instance via the `ProverEnvironment → Environment` projection.
-/
abbrev evalVerifier {F Var Value} [VerifierEval F Var Value]
  (env : Environment F) (v : Var) : Value := eval env v

/-- Explicit "prover view" — only applies where a `ProverEnvironment` is available. -/
abbrev evalProver {F Var Value} [ProverEval F Var Value]
  (env : ProverEnvironment F) (v : Var) : Value := eval env v

variable {F : Type} [Field F] {M N : TypeMap} [ProvableType M] [ProvableType N] {Hint : Type}

instance : VerifierEval F (ProverHint Hint F) Unit where
  eval _ _ := ()

instance : ProverEval F (ProverHint Hint F) Hint where
  eval env h := h env

instance : VerifierEval F (Var M F) (M F) where
  eval env v := ProvableType.eval env v

instance : ProverEval F (Var M F) (M F) where
  eval env v := ProvableType.eval env v

instance : VerifierEval F (M (Expression F)) (M F) where
  eval env v := ProvableType.eval env v

instance : ProverEval F (M (Expression F)) (M F) where
  eval env v := ProvableType.eval env v

instance : VerifierEval F (Expression F) F where
  eval env v := Expression.eval env v

instance : ProverEval F (Expression F) F where
  eval env v := Expression.eval env v

/--
Generic product instance: given component-wise evaluators, evaluate a pair pointwise.
-/
instance {Env A B A' B'} [Eval Env A A'] [Eval Env B B'] : Eval Env (A × B) (A' × B') where
  eval env p := (eval env p.1, eval env p.2)

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

@[circuit_norm] theorem eval_expr (env : Environment F) (v : Expression F) :
    eval env v = Expression.eval env v := rfl

@[circuit_norm] theorem eval_expr_prover (env : ProverEnvironment F) (v : Expression F) :
    eval env v = Expression.eval env v := rfl

@[circuit_norm] theorem eval_var (env : Environment F) (v : Var M F) :
    eval env v = ProvableType.eval env v := rfl

@[circuit_norm] theorem eval_var_prover (env : ProverEnvironment F) (v : Var M F) :
    eval env v = ProvableType.eval env v := rfl

omit [Field F] in
@[circuit_norm] theorem eval_hint (env : Environment F) (v : ProverHint Hint F) :
    eval env v = () := rfl

omit [Field F] in
@[circuit_norm] theorem eval_hint_prover (env : ProverEnvironment F) (v : ProverHint Hint F) :
    eval env v = v env := rfl

@[circuit_norm] theorem eval_var_field (env : Environment F) (v : Var field F) :
  eval env v = Expression.eval env v := by simp only [circuit_norm]

@[circuit_norm] theorem eval_var_field_prover (env : ProverEnvironment F) (v : Var field F) :
  eval env v = Expression.eval env v := by simp only [circuit_norm]

/-- Product unfolds pointwise via the generic `Eval _ (A × B) _` instance. -/
@[circuit_norm] theorem eval_prod {Env A B A' B'} [Eval Env A A'] [Eval Env B B']
    (env : Env) (p : A × B) :
    eval env p = (eval env p.1, eval env p.2) := rfl

@[circuit_norm] theorem eval_var_pair (env : Environment F) (p1 : Var M F) (p2 : Var N F) :
    eval (Var := Var (ProvablePair M N) F) env (p1, p2) = (eval env p1, eval env p2) := by
  rw [eval_var (M := (ProvablePair M N))]
  simp only [circuit_norm]

@[circuit_norm] theorem eval_var_pair_prover (env : ProverEnvironment F) (p1 : Var M F) (p2 : Var N F) :
    eval (Var := Var (ProvablePair M N) F) env (p1, p2) = (eval env p1, eval env p2) := by
  rw [eval_var_prover (M := (ProvablePair M N))]
  simp only [circuit_norm]

@[circuit_norm] theorem eval_field_pair (F : Type) [Field F]
  (env : Environment F) (p1 : Var field F) (p2 : Var field F) :
    eval (Var := Var (ProvablePair field field) F) env (p1, p2) = (eval env p1, eval env p2) := by
  rw [eval_var (M := (ProvablePair field field))]
  simp only [circuit_norm]

@[circuit_norm] theorem eval_field_pair_prover (F : Type) [Field F]
  (env : ProverEnvironment F) (p1 : Var field F) (p2 : Var field F) :
    eval (Var := Var (ProvablePair field field) F) env (p1, p2) = (eval env p1, eval env p2) := by
  rw [eval_var_prover (M := (ProvablePair field field))]
  simp only [circuit_norm]

@[circuit_norm] theorem eval_fields (F : Type) [Field F] {n : ℕ}
  (env : Environment F) (xs : Var (fields n) F) :
    eval (Var := Var (fields n) F) env xs = ProvableType.eval env xs := by
  rw [eval_var (M := (fields n))]

@[circuit_norm] theorem eval_fields_prover (F : Type) [Field F] {n : ℕ}
  (env : ProverEnvironment F) (xs : Var (fields n) F) :
    eval (Var := Var (fields n) F) env xs = ProvableType.eval env xs := by
  rw [eval_var_prover (M := (fields n))]

/-!
## `CircuitType`: the schema-level class for circuit I/O

`CircuitType Input` bundles the three derived types (`Var`, `Value`, `VerifierValue`)
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
  Value : TypeMap
  /-- Verifier value — hint fields are erased to `Unit`. -/
  VerifierValue : TypeMap
  evalVerifier : ∀ {F : Type} [Field F], Environment F → Var F → VerifierValue F
  evalProver   : ∀ {F : Type} [Field F], ProverEnvironment F → Var F → Value F

/--
Default `CircuitType` for any `ProvableType`: verifier- and prover-value coincide
with the input type, and `Var` is the usual `α ∘ Expression`.
-/
instance ProvableType.toCircuitType {α : TypeMap} [ProvableType α] : CircuitType α where
  Var := Var α
  Value := α
  VerifierValue := α
  evalVerifier env v := ProvableType.eval env v
  evalProver env v := ProvableType.eval env v

instance Unconstrained.toCircuitType {Hint : Type} : CircuitType (Unconstrained Hint) where
  Var := ProverHint Hint
  Value _ := Hint
  VerifierValue _ := Unit
  evalVerifier _ _ := ()
  evalProver env v := v env

/--
A `CircuitType Input` instance induces a verifier-side `Eval` on `CircuitType.Var Input F`.
This lets `eval env var` work uniformly whether the Var came from a `ProvableType`-derived
instance or a hand-written one.
-/
instance CircuitType.evalVerifierInstance {Input : TypeMap} [c : CircuitType Input]
    {F : Type} [Field F] :
    Eval (Environment F) (CircuitType.Var Input F) (CircuitType.VerifierValue Input F) where
  eval := c.evalVerifier

/-- `CircuitType` induces a prover-side `Eval` on `CircuitType.Var Input F`. -/
instance CircuitType.evalProverInstance {Input : TypeMap} [c : CircuitType Input]
    {F : Type} [Field F] :
    Eval (ProverEnvironment F) (CircuitType.Var Input F) (CircuitType.Value Input F) where
  eval := c.evalProver
