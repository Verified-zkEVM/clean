import Lean
import Clean.Circuit.Basic
open Lean Elab Tactic Meta

/-!
# SubcircuitNorm: Forward Reasoning for Circuit Proofs

This file implements the `subcircuit_norm` tactic, which performs automatic forward
reasoning on hypotheses in circuit proofs.

## Background

In circuit proofs, we often encounter hypotheses about subcircuit constraints:

```lean
h : ConstraintsHoldFlat env (someCircuit.toSubcircuit n x).ops.toFlat
```

We want to replace such hypotheses with their high-level specifications
(e.g., `someCircuit.Spec (eval env x) output`), even though this is a
one-way implication (making the proof "logically weaker" but "practically easier").

`simp` cannot handle one-way implications; it requires equalities or iff lemmas.
This tactic provides a custom forward-reasoning mechanism: it automatically applies
any lemma tagged with `@[subcircuit_norm]` to hypotheses in the proof context.

## Usage

Tag forward-reasoning lemmas with `@[subcircuit_norm]`:
```lean
@[subcircuit_norm]
theorem myGadget_forward {n : ℕ} {x : Var Input F} {env : Environment F}
    (h : ConstraintsHoldFlat env (myGadget.toSubcircuit n x).ops.toFlat) :
    myGadget.Spec (eval env x) (eval env (myGadget.output x n)) :=
  (myGadget.toSubcircuit n x).soundness env h
```

Then in a proof, call `subcircuit_norm` to automatically replace the raw constraint
hypothesis with the spec.

## Design

This implements the approach described in the issue "Experiment with metaprogramming
to get rid of Subcircuit properties": instead of storing `Spec`/`ProverAssumptions`/
`ProverSpec` on the `Subcircuit` type (the current approach), forward-reasoning
lemmas are tagged and applied automatically by a custom tactic.

This enables a potential future refactoring where `Subcircuit` is simplified by
removing these properties, relying instead on `subcircuit_norm` for hypothesis
transformation.
-/

/--
`@[subcircuit_norm]` marks a theorem for use in forward reasoning by the
`subcircuit_norm` tactic.

A lemma tagged with `@[subcircuit_norm]` should have the form:
```lean
theorem myLemma {implicit args} (h : SomeConstraint) : SomeDerivedFact
```

When `subcircuit_norm` is applied in a proof context, it scans all hypotheses
and, for each hypothesis `h : P`, tries to apply any tagged lemma `l : P → Q`,
replacing `h` with the derived `h : Q`.

**Convention**: The hypothesis to be forwarded should be the **only explicit argument**;
other arguments (e.g., `n : ℕ`, `env : Environment F`) should be implicit so that
Lean can infer them automatically from the hypothesis type.

**Example**:
```lean
@[subcircuit_norm]
theorem assertBool_spec_forward {p : ℕ} [Fact p.Prime]
    {n : ℕ} {x : Expression (F p)} {env : Environment (F p)}
    (h : ConstraintsHoldFlat env (assertBool.toSubcircuit n x).ops.toFlat) :
    IsBool (eval env x) :=
  (assertBool.toSubcircuit n x).soundness env h trivial
```
-/
initialize subcircuitNormAttr : TagAttribute ←
  registerTagAttribute `subcircuit_norm
    "Forward reasoning lemma for the `subcircuit_norm` tactic. \
     Tag lemmas of the form `(h : P) → Q` to enable automatic replacement of \
     hypothesis `h : P` with `h : Q` in circuit proofs."

/--
Try to apply a single `@[subcircuit_norm]` lemma to a hypothesis in forward direction.

Attempts `replace h := lemma h` and returns `true` if successful (i.e., the
hypothesis type was changed).
-/
private def trySubcircuitNormLemma (lemmaName : Name) (hypName : Name) : TacticM Bool := do
  try
    let l := mkIdent lemmaName
    let h := mkIdent hypName
    evalTactic (← `(tactic| replace $h := $l $h))
    return true
  catch _ =>
    return false

/--
Core implementation of the `subcircuit_norm` tactic.

Scans all hypotheses in the current context and tries to apply each
`@[subcircuit_norm]`-tagged lemma to each hypothesis. Restarts scanning
whenever a hypothesis is successfully replaced. Terminates when no more
progress can be made.
-/
def subcircuitNormCore : TacticM Unit := do
  withMainContext do
    let env ← getEnv
    -- Collect all names tagged with @[subcircuit_norm] into an array
    -- Using fold instead of direct iteration for compatibility
    let lemmaNames : Array Name :=
      (subcircuitNormAttr.ext.getState env).fold (fun acc n => acc.push n) #[]
    if lemmaNames.isEmpty then return

    let rec go : TacticM Unit := do
      withMainContext do
        let ctx ← getLCtx
        for hypDecl in ctx do
          if hypDecl.isImplementationDetail then continue
          for lemmaName in lemmaNames do
            if ← trySubcircuitNormLemma lemmaName hypDecl.userName then
              go
              return
    go

/--
`subcircuit_norm` applies all `@[subcircuit_norm]` lemmas to hypotheses in forward direction.

This tactic:
1. Collects all lemmas tagged with `@[subcircuit_norm]`
2. For each hypothesis `h : P` and each tagged lemma `l : P → Q`, performs `replace h := l h`
3. Repeats until no more progress

**Primary use case**: In circuit soundness/completeness proofs, automatically replace
"raw constraint" hypotheses with their high-level specifications.

**Example**: Given a tagged lemma
```lean
@[subcircuit_norm]
theorem assertBool_forward {n} {x} {env} (h : ConstraintsHoldFlat env ...) : IsBool (eval env x)
```
and hypothesis `h : ConstraintsHoldFlat env (assertBool.toSubcircuit n x).ops.toFlat`,
`subcircuit_norm` replaces `h` with `h : IsBool (eval env x)`.

**Relationship to `circuit_norm`**: `circuit_norm` handles equality/iff lemmas via `simp`.
`subcircuit_norm` extends this with one-way implications, enabling replacement of hypotheses
with strictly weaker (but more readable) statements — something `simp` fundamentally cannot do.

**Design note**: This tactic demonstrates that the `Spec`/`ProverAssumptions`/`ProverSpec`
fields on `Subcircuit` could in principle be removed, with tagged forward-reasoning lemmas
playing their role instead. See the issue "Experiment with metaprogramming to get rid of
Subcircuit properties" for the motivation.
-/
elab "subcircuit_norm" : tactic => subcircuitNormCore
