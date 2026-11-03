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

private def isConstructedVector (e : Expr) : Bool :=
  match e.getAppFn with
  | .const name _ => vectorMapPushLemmas.any (·.1 == name)
  | _ => false

/-- The rewrite `e ~~> rhs` proved by `proof`, whose stated left-hand side may differ from `e`
up to defeq (instance paths). The proof is annotated with the exact equation, so that the
rewritten term stays type-correct at reducible transparency. -/
private def rewriteTo (e rhs proof : Expr) : MetaM Simp.Result := do
  return { expr := rhs, proof? := some (← mkExpectedTypeHint proof (← mkEq e rhs)) }

/-- Rewrite `e` at the root with an equation lemma whose arguments its left-hand side
determines. Metavariables of `e` (circuits under elaboration) are never assigned. -/
private def rewriteRoot? (lemmaName : Name) (e : Expr) : MetaM (Option Simp.Result) := do
  try
    withNewMCtxDepth do
      let thm ← mkConstWithFreshMVarLevels lemmaName
      let (args, _, type) ← forallMetaTelescopeReducing (← inferType thm)
      let some (_, lhs, rhs) := type.eq? | return none
      unless ← isDefEq lhs e do return none
      unless ← args.allM (·.mvarId!.isAssigned) do return none
      let proof ← instantiateMVars (mkAppN thm args)
      if proof.hasLevelMVar then return none
      return some (← rewriteTo e (← instantiateMVars rhs) proof)
  catch _ => return none

/-- Rewrite `Vector.map f v` at the root with the push lemma of `v`'s constructor. -/
private def pushVectorMap? (e : Expr) : MetaM (Option Simp.Result) := do
  unless e.isAppOfArity ``Vector.map 5 do return none
  let .const head _ := e.appArg!.getAppFn | return none
  let some (_, lemmaName) := vectorMapPushLemmas.find? (·.1 == head) | return none
  rewriteRoot? lemmaName e

/-- The evaluator of a `Vector.map` whose function evaluates expressions (`Expression.eval env`)
or provable values (`Eval.eval env`), together with that environment. -/
private def vectorMapEvalEnv? (e : Expr) : Option (Name × Expr) :=
  if e.isAppOfArity ``Vector.map 5 then
    let f := e.getAppArgs[3]!.eta
    if f.getAppFn.isConstOf ``Expression.eval then some (``Expression.eval, f.appArg!)
    else if f.getAppFn.isConstOf ``Eval.eval then some (``Eval.eval, f.appArg!)
    else none
  else none

/-- `eval env v = v.map (eval env)` for a vector-typed subject, dispatched on the element type:
`Expression` elements use the `fields` lemma, provable elements the `ProvableVector` one. -/
private def evalVectorEq? (env v : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  try
    let vType ← withDefault <| whnf (← inferType v)
    unless vType.isAppOf ``Vector do return none
    let elemType ← withDefault <| whnf vType.getAppArgs[0]!
    let proof ← withDefault <| do
      if elemType.isAppOf ``Expression then mkAppM ``ProvableType.eval_fields #[env, v]
      -- `mkAppM` cannot assign the element `TypeMap` of `Expression`-component pairs
      else if elemType.isAppOf ``Prod then
        mkAppOptM ``eval_vector
          #[none, none, none, some (mkConst ``fieldPair), none, some env, some v]
      else mkAppM ``eval_vector #[env, v]
    let some (_, lhs, rhs) := (← inferType proof).eq? | return none
    return some (lhs, rhs, proof)
  catch _ => return none

/-- Inward side of the vector normal form: evaluating a constructed vector pushes the
evaluation into the constructor, `eval env (Vector.ofFn f) ~~> Vector.ofFn fun i => eval env
(f i)`. Opaque vectors stay folded atoms. -/
private def vectorEvalLiteralCore (e : Expr) : SimpM Simp.Step := do
  let args := e.getAppArgs
  unless e.getAppFn.isConstOf ``Eval.eval && args.size ≥ 2 do
    return .continue
  let subject := args[args.size - 1]!
  unless isConstructedVector subject do return .continue
  let some (lhs, mapped, proof) ← evalVectorEq? args[args.size - 2]! subject | return .continue
  -- alias-typed subjects (`U32`, `SHA256State`, …) carry their own `Eval` instances and hide
  -- behind regular defs; validate at full transparency
  unless lhs == e || (← withNewMCtxDepth <| withTransparency .all <| isDefEq lhs e) do
    return .continue
  let some pushed ← pushVectorMap? mapped | return .continue
  return .visit (← rewriteTo e pushed.expr (← mkEqTrans proof (← pushed.getProof)))

simproc vectorEvalLiteral (Eval.eval _ _) := vectorEvalLiteralCore
attribute [circuit_norm] vectorEvalLiteral

/-- `Vector.map` of an evaluator: pushed into a constructed vector, folded into the
whole-vector atom `eval env v` for an opaque one. This makes the atom the single spelling of
an evaluated opaque vector, also for `fields` vectors. -/
private def vectorMapEvalCore (e : Expr) : SimpM Simp.Step := do
  let some (_, env) := vectorMapEvalEnv? e | return .continue
  let subject := e.appArg!
  if isConstructedVector subject then
    let some pushed ← pushVectorMap? e | return .continue
    return .visit pushed
  let some (lhs, mapped, proof) ← evalVectorEq? env subject | return .continue
  unless ← withNewMCtxDepth <| withDefault <| isDefEq mapped e do return .continue
  return .visit (← rewriteTo e lhs (← mkEqSymm proof))

simproc vectorMapEval (Vector.map _ _) := vectorMapEvalCore
attribute [circuit_norm] vectorMapEval

/-- Outward side of the vector normal form: scalar evals whose subject chains down to an
input variable fold toward the whole-atom eval (`Expression.eval env x[i] ~~> (eval env x)[i]`,
`Expression.eval env (c[i]).1 ~~> ((eval env c)[i]).1`). -/
private def vectorAtomLiftCore (e : Expr) : SimpM Simp.Step := do
  let args := e.getAppArgs
  unless e.getAppFn.isConstOf ``Expression.eval && args.size ≥ 2 do
    return .continue
  let env := args[args.size - 2]!
  let subject := args[args.size - 1]!
  unless (chainRoot subject).isFVar do return .continue
  if subject.isAppOfArity ``GetElem.getElem 8 then
    let gArgs := subject.getAppArgs
    let xs := gArgs[5]!
    let i := gArgs[6]!
    let hval := gArgs[7]!
    try
      let xsType ← withDefault <| whnf (← inferType xs)
      unless xsType.isAppOf ``Vector do return .continue
      -- a bare `v[i]` access into a pair-element vector cannot be `Expression.eval`-headed;
      -- pair components are handled by the projection branch below
      let elemTy ← withDefault <| whnf (xsType.getAppArgs[0]!)
      if elemTy.isAppOf ``Prod then return .continue
      let lemmaName := if elemTy.isAppOf ``Expression then
        ``ProvableType.getElem_eval_fields else ``getElem_eval_vector
      let proof ← withDefault <| mkAppM lemmaName #[env, xs, i, hval]
      let some (_, lhs0, rhs0) := (← inferType proof).eq? | return .continue
      unless ← withNewMCtxDepth <| withDefault <| isDefEq lhs0 e do return .continue
      return .visit (← rewriteTo e rhs0 proof)
    catch _ => return .continue
  -- Projection chain through a pair-element vector access, folded to the whole-vector atom in
  -- one step: `Expression.eval env (c[i]).1 ~~> ((eval env c)[i]).1`. The intermediate
  -- spelling `(eval env c[i]).1` must never be produced: the pair `Eval` instance
  -- defeq-collapses, so it would loop against the component-wise `eval_fieldPair` lemmas.
  let isFst := subject.isAppOfArity ``Prod.fst 3
  unless isFst || subject.isAppOfArity ``Prod.snd 3 do return .continue
  let t := subject.appArg!
  unless t.isAppOfArity ``GetElem.getElem 8 do return .continue
  let gArgs := t.getAppArgs
  let xs := gArgs[5]!
  let i := gArgs[6]!
  let hval := gArgs[7]!
  try
    let xsType ← withDefault <| whnf (← inferType xs)
    unless xsType.isAppOf ``Vector do return .continue
    let elemTy ← withDefault <| whnf (xsType.getAppArgs[0]!)
    unless elemTy.isAppOf ``Prod do return .continue
    let chainLemma := if isFst then ``eval_fst_getElem_pairVector
      else ``eval_snd_getElem_pairVector
    let proof ← withDefault <| mkAppM chainLemma #[env, xs, i, hval]
    let some (_, lhs0, rhs0) := (← inferType proof).eq? | return .continue
    unless ← withNewMCtxDepth <| withDefault <| isDefEq lhs0 e do return .continue
    return .visit (← rewriteTo e rhs0 proof)
  catch _ => return .continue

simproc vectorAtomLift (Expression.eval _ _) := vectorAtomLiftCore
attribute [circuit_norm] vectorAtomLift

/-- The provable-element link of the same chains, `eval env x[i] ~~> (eval env x)[i]`, for
`Eval.eval` and, on struct elements, `ProvableStruct.eval`. -/
private def vectorAtomLiftEvalCore (evalHead : Name) (e : Expr) : SimpM Simp.Step := do
  let args := e.getAppArgs
  unless e.getAppFn.isConstOf evalHead && args.size ≥ 2 do
    return .continue
  let env := args[args.size - 2]!
  let subject := args[args.size - 1]!
  unless subject.isAppOfArity ``GetElem.getElem 8 do return .continue
  unless (chainRoot subject).isFVar do return .continue
  let gArgs := subject.getAppArgs
  let xs := gArgs[5]!
  let i := gArgs[6]!
  let hval := gArgs[7]!
  try
    let xsType ← withDefault <| whnf (← inferType xs)
    unless xsType.isAppOf ``Vector do return .continue
    let elemTy ← withDefault <| whnf (xsType.getAppArgs[0]!)
    let proof ← withDefault <| do
      if evalHead == ``ProvableStruct.eval then
        mkAppM ``ProvableStruct.eval_getElem_vector #[env, xs, i, hval]
      else if elemTy.isAppOf ``Expression then
        mkAppM ``ProvableType.getElem_eval_fields #[env, xs, i, hval]
      -- `mkAppM` cannot assign the element `TypeMap` of `Expression`-component pairs
      else if elemTy.isAppOf ``Prod then
        mkAppOptM ``getElem_eval_vector
          #[none, none, none, some (mkConst ``fieldPair), none, some env, some xs, some i, some hval]
      else mkAppM ``getElem_eval_vector #[env, xs, i, hval]
    let some (_, lhs0, rhs0) := (← inferType proof).eq? | return .continue
    unless ← withNewMCtxDepth <| withDefault <| isDefEq lhs0 e do return .continue
    return .visit (← rewriteTo e rhs0 proof)
  catch _ => return .continue

simproc vectorAtomLiftEval (Eval.eval _ _) := vectorAtomLiftEvalCore ``Eval.eval
attribute [circuit_norm] vectorAtomLiftEval

/-- `vectorAtomLiftEvalCore` on struct elements, registered below. -/
def vectorAtomLiftStructEvalProc : Simproc :=
  vectorAtomLiftEvalCore ``ProvableStruct.eval

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
