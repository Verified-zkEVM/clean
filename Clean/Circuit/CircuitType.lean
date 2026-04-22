import Clean.Circuit.Provable

structure Unconstrained (Hint : Type) where
  value : Hint

/-
  Prover hints: additional data that can be passed to a circuit's witness generation
  but does not affect the circuit's constraints or spec.
-/
def ProverHint (Hint : Type) (F : Type) := ProverEnvironment F → Hint

/--
`Eval Env Var Value` says: in environment `Env`, a term `v : Var` evaluates to `Value`.

This is the single joint generalization of verifier evaluation (`Env = Environment F`),
prover evaluation (`Env = ProverEnvironment F`), `ProvableType`, and prover hints.

The `Var → Value` mapping is per-instance, so verifier- and prover-side can legitimately
disagree: e.g. a `ProverHint Hint F` evaluates to `Unit` under `Environment F` but to
`Hint` under `ProverEnvironment F`.
-/
class Eval (Env : Type) (Var : Type) (Value : outParam Type) where
  eval : Env → Var → Value

export Eval (eval)

/-- Verifier evaluation is `Eval` specialized to `Environment F`. -/
@[circuit_norm]
abbrev CircuitType (F : Type) (Var : Type) (Value : outParam Type) :=
  Eval (Environment F) Var Value

/-- Prover evaluation is `Eval` specialized to `ProverEnvironment F`. -/
@[circuit_norm]
abbrev ProverType (F : Type) (Var : Type) (Value : outParam Type) :=
  Eval (ProverEnvironment F) Var Value

/--
Explicit "verifier view" — even on a `ProverEnvironment`, this forces the verifier
instance via the `ProverEnvironment → Environment` projection.
-/
abbrev evalVerifier {F Var Value} [CircuitType F Var Value]
  (env : Environment F) (v : Var) : Value := eval env v

/-- Explicit "prover view" — only applies where a `ProverEnvironment` is available. -/
abbrev evalProver {F Var Value} [ProverType F Var Value]
  (env : ProverEnvironment F) (v : Var) : Value := eval env v

variable {F : Type} [Field F] {M N : TypeMap} [ProvableType M] [ProvableType N] {Hint : Type}

instance : CircuitType F (ProverHint Hint F) Unit where
  eval _ _ := ()

instance : ProverType F (ProverHint Hint F) Hint where
  eval env h := h env

instance : CircuitType F (Var M F) (M F) where
  eval env v := ProvableType.eval env v

instance : ProverType F (Var M F) (M F) where
  eval env v := ProvableType.eval env v

instance : CircuitType F (M (Expression F)) (M F) where
  eval env v := ProvableType.eval env v

instance : ProverType F (M (Expression F)) (M F) where
  eval env v := ProvableType.eval env v

instance : CircuitType F (Expression F) F where
  eval env v := Expression.eval env v

instance : ProverType F (Expression F) F where
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
