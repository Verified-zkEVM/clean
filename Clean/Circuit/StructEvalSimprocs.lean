import Clean.Circuit.Provable

/-!
# Simprocs for `ProvableStruct` evaluation

Companion to the witgen simprocs in `Clean.Circuit.WitnessIR` (`evalProjection`,
`evalStructLiteral`), for the circuit-level evaluators.

The `circuit_norm` normal form for struct evaluation is component-preserving:

* `ProvableStruct.eval env ⟨a, b, …⟩` on a *literal* decomposes into `⟨eval env a, …⟩`,
* evaluation of a *projection* lifts to a projection of the row-level evaluation,
  `Expression.eval env s.pc ~~> (ProvableStruct.eval env s).pc`,
* evaluation of an *opaque* struct stays a folded row-level atom, to be consumed by
  row-level facts such as `h_input : eval env input_var = input`.

Previously the first two came from unfolding the `ProvableStruct.eval`/`toComponents`
definitions and relying on the matcher eta-expanding opaque structure variables during
`simp`'s definitional reduction. Matchers do not eta-expand variables anymore, which left
un-keyable stuck terms `fromComponents (eval.go … (match x with …))`. These simprocs
produce the same normal form by meta-level rewriting: they recognize constructor literals
and structure projections syntactically — something rewrite lemmas cannot do generically —
and validate the rewrite by definitional equality (structure eta *is* still part of
definitional equality, only matcher reduction lost it).
-/

open Lean Meta Simp

namespace ProvableStruct

/-- View an expression as a structure projection `base.field`, returning the base and a
function that rebuilds the same projection on a new base. Handles both `.proj` nodes and
projection-function applications (same logic as the witgen `evalProjection` simproc). -/
private def projectionView? (e : Expr) : MetaM (Option (Expr × (Expr → MetaM Expr))) := do
  match e with
  | .proj structName idx base =>
    return some (base, fun newBase => pure <| mkProj structName idx newBase)
  | _ =>
    let .const projName _ := e.getAppFn | return none
    let some pinfo ← getProjectionFnInfo? projName | return none
    let projArgs := e.getAppArgs
    if h : pinfo.numParams < projArgs.size then
      return some (projArgs[pinfo.numParams],
        fun newBase => mkProjection newBase (Name.mkSimple projName.getString!))
    else
      return none

/--
Lift evaluation of a structure projection to a projection of the struct evaluation:

```
Expression.eval env s.pc        ~~>  (ProvableStruct.eval env s).pc
ProvableStruct.eval env d.mode1 ~~>  (ProvableStruct.eval env d).mode1
```

This restores the row-level shape so that row-level hypotheses (`h_input` equations) and
per-struct lemmas can fire. A simproc rather than a lemma because lemmas cannot quantify
over an arbitrary structure projection. The rewrite is validated by definitional equality
at default transparency (structure eta), so it cannot produce wrong results.
-/
private def evalProjectionLiftCore (evalHead : Name) (e : Expr) : SimpM Simp.Step := do
  let args := e.getAppArgs
  unless e.getAppFn.isConstOf evalHead && args.size ≥ 2 do
    return .continue
  let env := args[args.size - 2]!
  let projected := args[args.size - 1]!
  -- indexing into a *projected* vector field lifts to the row level in one step:
  -- `Expression.eval env (s.c[i]) ~~> (ProvableStruct.eval env s).c[i]` (and likewise
  -- `Eval.eval env (s.c[i]) ~~> (ProvableStruct.eval env s).c[i]` for element types that
  -- are themselves provable). The proof is `getElem_eval_fields` / `getElem_eval_vector`,
  -- whose right-hand side `(eval env s.c)[i]` is definitionally the row-level form.
  -- Restricted to projections: literal vectors reduce element-wise instead, and this
  -- avoids introducing a bare `Eval.eval` of a vector, which other lemmas rewrite to the
  -- element-map spelling.
  if (evalHead == ``Expression.eval || evalHead == ``Eval.eval) &&
      projected.isAppOfArity ``GetElem.getElem 8 then
    let gArgs := projected.getAppArgs
    let xs := gArgs[5]!
    let i := gArgs[6]!
    let hval := gArgs[7]!
    let some (base, mkRhs) ← projectionView? xs | return .continue
    try
      let xsType ← withDefault <| whnf (← inferType xs)
      unless xsType.isAppOf ``Vector do return .continue
      let lemmaName := if evalHead == ``Expression.eval then
        ``ProvableType.getElem_eval_fields else ``getElem_eval_vector
      let proof ← withDefault <| mkAppM lemmaName #[env, xs, i, hval]
      let some (_, lhs0, rhs0) := (← inferType proof).eq? | return .continue
      -- validate that the proof's left-hand side really is the term being rewritten
      -- (`mkAppM` can pick a different `GetElem`/`Eval` instance than the term's)
      unless ← withDefault <| isDefEq lhs0 e do return .continue
      -- the lemma's right-hand side is `(eval env xs)[i]`; swap in the row-level
      -- spelling of the same (definitionally equal) vector
      unless rhs0.isAppOfArity ``GetElem.getElem 8 do return .continue
      let evalBase ← withDefault <| mkAppM ``ProvableStruct.eval #[env, base]
      let projEval ← mkRhs evalBase
      -- the swap is a pure spelling change: validate that the row-level projection is
      -- definitionally the evaluation of the projected field (the lemma's own equality
      -- is propositional and needs no validation)
      unless ← withTransparency .all <| isDefEq projEval rhs0.getAppArgs[5]! do
        trace[Meta.Tactic.simp.rewrite] "getElem lift: defeq failed {projEval} vs {rhs0.getAppArgs[5]!}"
        return .continue
      let rhs := mkAppN rhs0.getAppFn (rhs0.getAppArgs.set! 5 projEval)
      return .visit { expr := rhs, proof? := some proof }
    catch _ => return .continue
  let some (base, mkRhs) ← projectionView? projected | return .continue
  -- only lift projections out of `ProvableStruct` bases (`mkAppM` synthesizes the
  -- instance). Notably *not* out of pairs: their `circuit_norm` normal form is
  -- element-wise (`eval_var_pair` and friends), so lifting `.1`/`.2` would loop.
  let evalBase ← try
      withDefault <| mkAppM ``ProvableStruct.eval #[env, base]
    catch _ =>
      return .continue
  let rhs ← mkRhs evalBase
  -- definitional-equality validation at `.all` (see the literal simproc)
  unless ← withTransparency .all <| isDefEq rhs e do
    return .continue
  return .done { expr := rhs, proof? := none }

/-- `evalProjectionLiftCore` registered on scalar evaluation. -/
def structEvalProjectionExprProc : Simproc :=
  evalProjectionLiftCore ``Expression.eval

/-- `evalProjectionLiftCore` registered on struct evaluation. -/
def structEvalProjectionProc : Simproc :=
  evalProjectionLiftCore ``ProvableStruct.eval

/-- `evalProjectionLiftCore` registered on the `Eval` class projection. This covers
projected fields whose own type is not a `ProvableStruct` (e.g. vector fields), where the
`eval_eq_eval` bridge to `ProvableStruct.eval` cannot fire:
`Eval.eval env s.c ~~> (ProvableStruct.eval env s).c`. -/
def structEvalProjectionEvalProc : Simproc :=
  evalProjectionLiftCore ``Eval.eval

simproc structEvalProjectionExpr (Expression.eval _ _) := structEvalProjectionExprProc
attribute [circuit_norm] structEvalProjectionExpr

/--
Evaluate struct *literals* component-wise:

```
ProvableStruct.eval env ⟨a, b, …⟩  ~~>  ⟨Eval.eval env a, Eval.eval env b, …⟩
```

Only fires on literal constructor applications; opaque values deliberately stay folded
row-level atoms (decomposing them via eta would produce projections that the lift simproc
immediately rewrites back, looping — restricting to literals makes the pair confluent).
-/
def structEvalLiteralProc : Simproc := fun e => do
  let args := e.getAppArgs
  unless e.getAppFn.isConstOf ``ProvableStruct.eval && args.size ≥ 2 do
    return .continue
  let env := args[args.size - 2]!
  let x := args[args.size - 1]!
  let .const fn _ := x.getAppFn | return .continue
  let some (.ctorInfo info) := (← getEnv).find? fn | return .continue
  try
    let ctorArgs := x.getAppArgs
    if ctorArgs.size != info.numParams + info.numFields then return .continue
    let mut newArgs : Array (Option Expr) := #[]
    for _ in [0:info.numParams] do
      newArgs := newArgs.push none
    for a in ctorArgs[info.numParams:] do
      -- scalar fields use the `Expression.eval` spelling (the circuit_norm normal form);
      -- struct/vector fields go through the `Eval.eval` class projection
      let aType ← withDefault <| whnf (← inferType a)
      let evalA ←
        if aType.isAppOf ``Expression then
          withDefault <| mkAppM ``Expression.eval #[env, a]
        else
          withDefault <| mkAppM ``Eval.eval #[env, a]
      newArgs := newArgs.push (some evalA)
    let rhs ← mkAppOptM fn newArgs
    -- validate at `.all` (like the witgen struct-literal simproc): the reduction goes
    -- through instance and class-projection unfoldings that default transparency no
    -- longer performs; the kernel re-checks the resulting rfl-step unrestricted
    unless ← withTransparency .all <| isDefEq e rhs do
      trace[Meta.Tactic.simp.rewrite] "structEvalLiteral: defeq validation failed {e} vs {rhs}"
      return .continue
    return .visit { expr := rhs, proof? := none }
  catch _ => return .continue

/-- Gate for `structEqSplit`: the equality's type is a provable struct (its `TypeMap` has
a `ProvableStruct` instance) or the value view of a `DerivedCircuitType`. -/
private def isProvableStructLike (type : Expr) : MetaM Bool := do
  -- `Value M F` / `ProverValue M F` wrappers of derived circuit types
  if type.getAppFn.isConstOf ``CircuitType.Value ||
      type.getAppFn.isConstOf ``CircuitType.ProverValue then
    if let some m := type.getAppArgs[0]? then
      let instType ← mkAppM ``DerivedCircuitType #[m]
      if (← trySynthInstance instType) matches .some _ then
        return true
  -- `S ps F`: check `ProvableStruct (S ps)`; reducible whnf sees through type synonyms
  let type' ← withTransparency .reducible <| whnf type
  let .app typeCtor _ := type' | return false
  try
    let instType ← mkAppM ``ProvableStruct #[typeCtor]
    return (← trySynthInstance instType) matches .some _
  catch _ => return false

/--
Split a constructor equality of provable structs into field-wise equalities:

```
(⟨a, b, …⟩ : S _) = ⟨a', b', …⟩  ~~>  a = a' ∧ b = b' ∧ …
```

The proof is the structure's generated `mk.injEq` lemma. A simproc rather than per-type
simp lemmas so the split applies uniformly to every provable struct — without collecting
`mk.injEq` instances up front, and regardless of when the constructor shape materializes
during a simp pass (e.g. only after the literal-decomposition simproc has fired on an
`eval` equation). Restricted to `ProvableStruct`/`DerivedCircuitType` structures so that
`circuit_norm` does not change how simp treats arbitrary record equalities.
-/
def structEqSplitProc : Simproc := fun e => do
  unless e.isAppOfArity ``Eq 3 do return .continue
  let args := e.getAppArgs
  let lhs := args[1]!.consumeMData
  let rhs := args[2]!.consumeMData
  let .const ctorName _ := lhs.getAppFn | return .continue
  unless rhs.getAppFn.isConstOf ctorName do return .continue
  let some (.ctorInfo info) := (← getEnv).find? ctorName | return .continue
  unless info.numFields > 0 do return .continue
  unless lhs.getAppNumArgs == info.numParams + info.numFields &&
      rhs.getAppNumArgs == info.numParams + info.numFields do return .continue
  let injEqName := ctorName ++ `injEq
  unless (← getEnv).contains injEqName do return .continue
  unless ← isProvableStructLike args[0]! do return .continue
  try
    -- `mk.injEq` binders are the structure params followed by the fields of both sides
    let params := lhs.getAppArgs[:info.numParams].toArray.map some
    let lhsFields := lhs.getAppArgs[info.numParams:].toArray.map some
    let rhsFields := rhs.getAppArgs[info.numParams:].toArray.map some
    let proof ← mkAppOptM injEqName (params ++ lhsFields ++ rhsFields)
    let some (_, _, conj) := (← inferType proof).eq? | return .continue
    return .visit { expr := conj, proof? := some proof }
  catch _ => return .continue

simproc structEqSplit (_ = _) := structEqSplitProc
attribute [circuit_norm] structEqSplit

/-!
The surface `simproc … (ProvableStruct.eval _ _)` syntax cannot express these patterns:
pattern elaboration insists on synthesizing the `ProvableStruct ?α` instance. Compute the
discrimination keys with plain metavariables and register directly.
-/
open Elab in
run_cmd Command.liftTermElabM do
  let mkKeys := fun (head : Name) => do
    let f ← mkConstWithFreshMVarLevels head
    let (mvars, _, _) ← forallMetaTelescope (← inferType f)
    withSimpGlobalConfig <| DiscrTree.mkPath (mkAppN f mvars)
  let structEvalKeys ← mkKeys ``ProvableStruct.eval
  registerSimproc ``ProvableStruct.structEvalProjectionProc structEvalKeys
  registerSimproc ``ProvableStruct.structEvalLiteralProc structEvalKeys
  registerSimproc ``ProvableStruct.structEvalProjectionEvalProc (← mkKeys ``Eval.eval)

attribute [circuit_norm] ProvableStruct.structEvalProjectionProc
  ProvableStruct.structEvalLiteralProc ProvableStruct.structEvalProjectionEvalProc

end ProvableStruct
