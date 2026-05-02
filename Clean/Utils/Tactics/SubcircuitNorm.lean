import Lean
import Lean.PrettyPrinter.Delaborator.Basic
import Batteries.Lean.TagAttribute
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
any lemma tagged with `@[subcircuit_norm]` to hypotheses in the proof context, and
it can recurse into larger propositions (such as conjunctions and implication bodies)
to rewrite matching subexpressions in place.

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
and tries to apply tagged lemmas deeply inside each hypothesis type. If it finds
`l : P → Q` and a matching subexpression `P` in positive position, it replaces that
subexpression with `Q`, producing a logically weaker but more useful hypothesis.

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

/-- Build a proof transformer from a tagged forward lemma when its premise matches `type`. -/
private def mkForwardTransformer? (lemmaName : Name) (type : Expr) : MetaM (Option (Expr × Expr)) := do
  withLocalDeclD `h type fun h => do
    try
      let proof ← mkAppM lemmaName #[h]
      let newType ← instantiateMVars (← inferType proof)
      if ← isDefEq newType type then
        return none
      let transformer ← mkLambdaFVars #[h] proof
      return some (newType, transformer)
    catch _ =>
      return none

/--
Try to rewrite `type` once using the tagged forward lemmas, descending recursively into
positive logical structure when the whole expression does not match directly.

Returns `(newType, proof)` where `proof : type → newType`.
-/
private partial def rewritePropOnce (lemmaNames : Array Name) (type : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let type ← instantiateMVars type

  for lemmaName in lemmaNames do
    if let some result ← mkForwardTransformer? lemmaName type then
      return some result

  match type with
  | .app (.app andFn left) right =>
      if andFn.constName? == some ``And then
        match (← rewritePropOnce lemmaNames left) with
        | some (newLeft, leftTransformer) =>
            withLocalDeclD `h type fun h => do
              let leftProof ← mkAppM ``And.left #[h]
              let rightProof ← mkAppM ``And.right #[h]
              let newLeftProof := mkApp leftTransformer leftProof
              let proof ← mkAppM ``And.intro #[newLeftProof, rightProof]
              let newType := mkApp2 andFn newLeft right
              let transformer ← mkLambdaFVars #[h] proof
              return some (newType, transformer)
        | none =>
            match (← rewritePropOnce lemmaNames right) with
            | some (newRight, rightTransformer) =>
                withLocalDeclD `h type fun h => do
                  let leftProof ← mkAppM ``And.left #[h]
                  let rightProof ← mkAppM ``And.right #[h]
                  let newRightProof := mkApp rightTransformer rightProof
                  let proof ← mkAppM ``And.intro #[leftProof, newRightProof]
                  let newType := mkApp2 andFn left newRight
                  let transformer ← mkLambdaFVars #[h] proof
                  return some (newType, transformer)
            | none =>
                return none
      else
        return none
  | .forallE binderName domain body binderInfo =>
      withLocalDecl binderName binderInfo domain fun x => do
        let body := body.instantiate1 x
        match (← rewritePropOnce lemmaNames body) with
        | some (newBody, bodyTransformer) =>
            withLocalDeclD `h type fun h => do
              let proofAtX := mkApp bodyTransformer (mkApp h x)
              let proof ← mkLambdaFVars #[x] proofAtX
              let newType ← mkForallFVars #[x] newBody
              let transformer ← mkLambdaFVars #[h] proof
              return some (newType, transformer)
        | none =>
            return none
  | _ => return none

/-- Replace `hypName` with a new type and proof term produced by `rewritePropOnce`. -/
private def replaceHypothesis (hypName : Name) (newType proof : Expr) : TacticM Unit := do
  let hypIdent := mkIdent hypName
  let typeSyntax ← PrettyPrinter.delab (← instantiateMVars newType)
  let proofSyntax ← PrettyPrinter.delab (← instantiateMVars proof)
  evalTactic (← `(tactic| replace $hypIdent:ident : $typeSyntax := by exact $proofSyntax))

/--
Core implementation of the `subcircuit_norm` tactic.

Scans all hypotheses in the current context and tries to apply the tagged forward
lemmas deeply inside each hypothesis type. Restarts scanning whenever a hypothesis
is successfully replaced. Terminates when no more progress can be made.
-/
partial def subcircuitNormCore : TacticM Unit := do
  withMainContext do
    let env ← getEnv
    let lemmaNames : Array Name := subcircuitNormAttr.getDecls env
    if lemmaNames.isEmpty then return
    let ctx ← getLCtx
    for hypDecl in ctx do
      if hypDecl.isImplementationDetail then continue
      if let some (newType, transformer) ← rewritePropOnce lemmaNames hypDecl.type then
        let proof := mkApp transformer hypDecl.toExpr
        replaceHypothesis hypDecl.userName newType proof
        subcircuitNormCore
        return

/--
`subcircuit_norm` applies all `@[subcircuit_norm]` lemmas to hypotheses in forward direction.

This tactic:
1. Collects all lemmas tagged with `@[subcircuit_norm]`
2. Deeply walks each hypothesis type in positive position, looking for subexpressions
   matching the premise of a tagged lemma `l : P → Q`
3. Replaces the hypothesis with the transformed result, proving the new hypothesis from
   the old one automatically
4. Repeats until no more progress

**Primary use case**: In circuit soundness/completeness proofs, automatically replace
"raw constraint" hypotheses with their high-level specifications.

**Example**: Given a tagged lemma
```lean
@[subcircuit_norm]
theorem assertBool_forward {n} {x} {env} (h : ConstraintsHoldFlat env ...) : IsBool (eval env x)
```
and hypothesis `h : ConstraintsHoldFlat env (assertBool.toSubcircuit n x).ops.toFlat`,
`subcircuit_norm` replaces `h` with `h : IsBool (eval env x)`.

It also works under larger propositions such as
`h : A ∧ ConstraintsHoldFlat env (...) ∧ B`, rewriting just the matching middle part.

**Relationship to `circuit_norm`**: `circuit_norm` handles equality/iff lemmas via `simp`.
`subcircuit_norm` extends this with one-way implications, enabling replacement of hypotheses
with strictly weaker (but more readable) statements — something `simp` fundamentally cannot do.

**Design note**: This tactic demonstrates that the `Spec`/`ProverAssumptions`/`ProverSpec`
fields on `Subcircuit` could in principle be removed, with tagged forward-reasoning lemmas
playing their role instead. See the issue "Experiment with metaprogramming to get rid of
Subcircuit properties" for the motivation.
-/
elab "subcircuit_norm" : tactic => subcircuitNormCore
