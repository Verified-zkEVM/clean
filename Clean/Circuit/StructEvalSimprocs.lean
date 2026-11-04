module

public meta import Clean.Circuit.Provable

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
and construct equality proofs using exported component-evaluation lemmas. This avoids
requiring consumers to import the private implementations of core array operations.
-/

public meta section

open Lean Meta Simp

namespace ProvableStruct

/-- Prove a component-preserving evaluation rewrite using the exported evaluation
lemmas. Keep this simp set independent of `circuit_norm`: row-level user lemmas must
only run after the simproc has returned its result. -/
private def proveEvalEq (lhs rhs : Expr) : MetaM (Option Expr) := do
  let mut thms : SimpTheorems := {}
  thms ← thms.addConst ``ProvableStruct.eval_eq_eval
  thms ← thms.addConst ``ProvableType.eval_field
  for name in [``ProvableStruct.eval, ``ProvableStruct.eval.go,
      ``ProvableStruct.components, ``ProvableStruct.toComponents,
      ``ProvableStruct.fromComponents] do
    thms ← thms.addDeclToUnfold name
  let ctx ← Simp.mkContext (simpTheorems := #[thms])
  let (lhsResult, _) ← Meta.simp lhs ctx #[]
  let (rhsResult, _) ← Meta.simp rhs ctx #[]
  unless ← withDefault <| isDefEq lhsResult.expr rhsResult.expr do
    return none
  return some (← mkEqTrans (← lhsResult.getProof) (← mkEqSymm (← rhsResult.getProof)))

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
over an arbitrary structure projection. The proof uses the same component-evaluation
lemmas as literal decomposition, keeping the public row-level expression folded.
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
      -- Compose the indexing lemma with a proof that evaluating the field is the
      -- corresponding projection of the evaluated row.
      let rhs := mkAppN rhs0.getAppFn (rhs0.getAppArgs.set! 5 projEval)
      let some projectionProof ← proveEvalEq rhs0 rhs | return .continue
      return .visit { expr := rhs, proof? := some (← mkEqTrans proof projectionProof) }
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
  let some proof ← proveEvalEq e rhs | return .continue
  return .done { expr := rhs, proof? := some proof }

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

/-- Root of a projection/getElem chain: walk through `GetElem.getElem` and `Prod`
projections to the underlying subject. -/
private partial def chainRoot (e : Expr) : Expr :=
  if e.isAppOfArity ``GetElem.getElem 8 then chainRoot e.getAppArgs[5]!
  else if e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3 then
    chainRoot e.appArg!
  else if e.isProj then chainRoot e.projExpr!
  else if e.getAppFn.isConstOf ``ProvableType.toElements && e.getAppNumArgs ≥ 1 then
    -- `toElements` is a projection-like wrapper: chains through it stay opaque
    chainRoot e.appArg!
  else e

/-- Rewrite `e` at the root with the first of `lemmas` whose left-hand side (right-hand side,
when `symm`) matches it up to reducible and instance unfolding, the transparency simp matches
its lemmas at. Metavariables of `e` (circuits under elaboration) are never assigned. The proof
is annotated with the exact equation `e = rhs`, so the rewritten term stays type-correct at
reducible transparency even where the lemma spells an instance or type alias differently. -/
private def rewriteRoot? (lemmas : List Name) (symm : Bool) (e : Expr) :
    MetaM (Option Simp.Result) := do
  for name in lemmas do
    let match? ← withNewMCtxDepth <| withReducibleAndInstances do
      let thm ← mkConstWithFreshMVarLevels name
      let (args, _, type) ← forallMetaTelescopeReducing (← inferType thm)
      let some (_, lhs, rhs) := type.eq? | return none
      let (source, target) := if symm then (rhs, lhs) else (lhs, rhs)
      unless ← isDefEq source e do return none
      unless ← args.allM (·.mvarId!.isAssigned) do return none
      let proof ← instantiateMVars (mkAppN thm args)
      if proof.hasLevelMVar then return none
      return some (← instantiateMVars target, ← if symm then mkEqSymm proof else pure proof)
    if let some (rhs, proof) := match? then
      return some { expr := rhs, proof? := some (← mkExpectedTypeHint proof (← mkEq e rhs)) }
  return none

/-- Vector constructors that evaluation is pushed into, each with the lemma that moves a
`Vector.map` inside it. Evaluating a vector built by one of these decomposes inward, into
evaluations of its elements or sub-vectors. Every other vector is opaque: its evaluation stays
a folded whole-vector atom, the spelling input premises (`h_input`) are stated at. -/
private def vectorMapPushLemmas : List (Name × Name) :=
  [(``Vector.mk, ``Vector.map_mk), (``Vector.ofFn, ``Vector.map_ofFn_fun),
   (``Vector.mapFinRange, ``Vector.map_mapFinRange), (``Vector.mapRange, ``Vector.map_mapRange),
   (``Vector.mapIdx, ``Vector.map_mapIdx_fun), (``Vector.map, ``Vector.map_map_fun),
   (``HAppend.hAppend, ``Vector.map_append), (``Vector.cast, ``Vector.map_cast),
   (``Vector.replicate, ``Vector.map_replicate), (``Vector.set, ``Vector.map_set),
   (``Vector.push, ``Vector.map_push), (``Vector.take, ``Vector.map_take_comm),
   (``Vector.extract, ``Vector.map_extract), (``Vector.takeShort, ``Vector.map_takeShort),
   -- the elements of a provable value: evaluated as the elements of its evaluation
   (``ProvableType.toElements, ``ProvableType.map_eval_toElements)]

/-- The push lemma of a constructed vector, `none` for an opaque one. -/
private def pushLemma? (v : Expr) : Option Name :=
  match v.getAppFn with
  | .const name _ => (vectorMapPushLemmas.find? (·.1 == name)).map (·.2)
  | _ => none

/-- `eval env v = v.map (eval env)`, at `Expression` elements (`fields`), provable elements, and
`fieldPair` elements. -/
private def evalVectorLemmas : List Name :=
  [``ProvableType.eval_fields, ``eval_vector, ``eval_pairVector]

/-- Inward side of the vector normal form: evaluating a constructed vector pushes the
evaluation into the constructor, `eval env (Vector.ofFn f) ~~> Vector.ofFn fun i => eval env
(f i)`. Opaque vectors stay folded atoms. -/
private def vectorEvalLiteralCore (e : Expr) : SimpM Simp.Step := do
  unless e.isAppOfArity ``Eval.eval 6 do return .continue
  let some push := pushLemma? e.appArg! | return .continue
  let some mapped ← rewriteRoot? evalVectorLemmas false e | return .continue
  let some pushed ← rewriteRoot? [push] false mapped.expr | return .continue
  return .visit (← mapped.mkEqTrans pushed)

simproc vectorEvalLiteral (Eval.eval _ _) := vectorEvalLiteralCore
attribute [circuit_norm] vectorEvalLiteral

/-- `Vector.map` of an evaluator (`Expression.eval env` or `Eval.eval env`): pushed into a
constructed vector, folded into the whole-vector atom `eval env v` for an opaque one. This makes
the atom the single spelling of an evaluated opaque vector, also for `fields` vectors. -/
private def vectorMapEvalCore (e : Expr) : SimpM Simp.Step := do
  unless e.isAppOfArity ``Vector.map 5 do return .continue
  let evaluator := e.getAppArgs[3]!.eta.getAppFn
  unless evaluator.isConstOf ``Expression.eval || evaluator.isConstOf ``Eval.eval do
    return .continue
  let result? ← match pushLemma? e.appArg! with
    | some push => rewriteRoot? [push] false e
    | none => rewriteRoot? evalVectorLemmas true e
  let some result := result? | return .continue
  return .visit result

simproc vectorMapEval (Vector.map _ _) := vectorMapEvalCore
attribute [circuit_norm] vectorMapEval

/-- Lemmas lifting an element access to an access into the evaluated vector, by the evaluator
heading the access: `Expression.eval env x[i] ~~> (eval env x)[i]`,
`Expression.eval env (c[i]).1 ~~> ((eval env c)[i]).1`, `eval env x[i] ~~> (eval env x)[i]`.
Pair components fold to the whole-vector atom in one step: the intermediate `(eval env c[i]).1`
would loop against the component-wise `eval_fieldPair` lemmas. -/
private def liftLemmas (evalHead : Name) : List Name :=
  if evalHead == ``Expression.eval then
    [``ProvableType.getElem_eval_fields, ``eval_fst_getElem_pairVector,
      ``eval_snd_getElem_pairVector]
  else if evalHead == ``Eval.eval then [``getElem_eval_vector, ``getElem_eval_pairVector]
  else [``ProvableStruct.eval_getElem_vector]

/-- Outward side of the vector normal form: evaluations of an element access whose chain is
rooted in a free variable fold toward the whole-atom eval. Chains rooted in an application stay
element-wise, so per-element lemmas about that function keep applying. -/
private def vectorAtomLiftCore (evalHead : Name) (e : Expr) : SimpM Simp.Step := do
  unless e.getAppFn.isConstOf evalHead && e.getAppNumArgs ≥ 2 do return .continue
  unless (chainRoot e.appArg!).isFVar do return .continue
  let some result ← rewriteRoot? (liftLemmas evalHead) false e | return .continue
  return .visit result

simproc vectorAtomLift (Expression.eval _ _) := vectorAtomLiftCore ``Expression.eval
attribute [circuit_norm] vectorAtomLift

simproc vectorAtomLiftEval (Eval.eval _ _) := vectorAtomLiftCore ``Eval.eval
attribute [circuit_norm] vectorAtomLiftEval

/-- `vectorAtomLiftCore` on struct elements, registered below. -/
def vectorAtomLiftStructEvalProc : Simproc :=
  vectorAtomLiftCore ``ProvableStruct.eval

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
    -- `.default` transparency: a component's evaluated type is often spelled through the
    -- `CircuitType.Value` synonym (e.g. `Value KeccakState F` for a vector field), which
    -- unifies with the constructor's expected field type only through the reducible
    -- `ProvableType`-derived `CircuitType` instance; `mkAppOptM`'s default elaboration
    -- transparency does not resolve that, silently discarding the rewrite
    let rhs ← withTransparency .default <| mkAppOptM fn newArgs
    let some proof ← proveEvalEq e rhs | return .continue
    return .visit { expr := rhs, proof? := some proof }
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
  -- `S ps F`: check `ProvableStruct (S ps)`. `.instances` whnf, not `.reducible`: class
  -- projections through the `ProvableType`-derived instance (`Var M F` /
  -- `Value M F` spellings) do not reduce at reducible transparency, and a failure here
  -- is silent — equalities just stop splitting.
  let type' ← withTransparency .instances <| whnf type
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
    -- `mk.injEq` binders are the structure params followed by the fields of both sides.
    -- `.default` transparency: for a `CircuitType.Value`/`ProverValue` struct (the mixed,
    -- hint-carrying case), a field's argument type is stated as `Value <component> F`, which
    -- unfolds to the field's own evaluated type only through the (reducible)
    -- `ProvableType`-derived `CircuitType` instance — `mkAppOptM`'s default elaboration
    -- transparency does not see through that far, so the implicit unification silently fails
    -- and the whole `try` falls through to `.continue` without this.
    let params := lhs.getAppArgs[:info.numParams].toArray.map some
    let lhsFields := lhs.getAppArgs[info.numParams:].toArray.map some
    let rhsFields := rhs.getAppArgs[info.numParams:].toArray.map some
    let proof ← withTransparency .default <| mkAppOptM injEqName (params ++ lhsFields ++ rhsFields)
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
  registerSimproc ``ProvableStruct.vectorAtomLiftStructEvalProc structEvalKeys

attribute [circuit_norm] ProvableStruct.structEvalProjectionProc
  ProvableStruct.structEvalLiteralProc ProvableStruct.structEvalProjectionEvalProc
  ProvableStruct.vectorAtomLiftStructEvalProc

end ProvableStruct
