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

/-- The vector-atom side of the struct decomposition's balancing act: scalar evals
whose subject chains down to an OPAQUE root (a free variable — an input) fold OUTWARD
toward the whole-atom eval the input premise is stated at (`Expression.eval env x[i] ~~> (eval env x)[i]`,
`Expression.eval env t.1 ~~> (eval env t).1`). Constructed subjects (map/literal-built)
are left for the inward element lemmas — the same literal/opaque discrimination that
keeps the struct pair confluent. -/
private def vectorAtomLiftCore (e : Expr) : SimpM Simp.Step := do
  let args := e.getAppArgs
  unless e.getAppFn.isConstOf ``Expression.eval && args.size ≥ 2 do
    return .continue
  let env := args[args.size - 2]!
  let subject := args[args.size - 1]!
  unless (chainRoot subject).isFVar do return .continue
  -- getElem of an opaque-rooted vector: lift to getElem-of-eval. The folded whole-atom
  -- eval is the canonical form for opaque subjects of every element type; stability
  -- requires that no shared-set lemma unconditionally decomposes those atoms
  -- (`eval_var_fields` and the fieldPair eval lemmas are deliberately NOT in
  -- `circuit_norm` — the literal simproc handles constructed subjects).
  if subject.isAppOfArity ``GetElem.getElem 8 then
    let gArgs := subject.getAppArgs
    let xs := gArgs[5]!
    let i := gArgs[6]!
    let hval := gArgs[7]!
    try
      let xsType ← withDefault <| whnf (← inferType xs)
      unless xsType.isAppOf ``Vector do return .continue
      -- pair-element vectors are handled by the projection-chain branch below (their
      -- element type is not `Expression`, so a bare `v[i]` access cannot be
      -- `Expression.eval`-headed in the first place)
      let elemTy ← withDefault <| whnf (xsType.getAppArgs[0]!)
      if elemTy.isAppOf ``Prod then return .continue
      -- expression-element vectors (`fields` spelling) fold via the fields lemma,
      -- provable-element vectors via the ProvableVector one
      let lemmaName := if elemTy.isAppOf ``Expression then
        ``ProvableType.getElem_eval_fields else ``getElem_eval_vector
      let proof ← withDefault <| mkAppM lemmaName #[env, xs, i, hval]
      let some (lhs0, rhs0) := (← inferType proof).eq?.map (fun (_, l, r) => (l, r))
        | return .continue
      unless ← withDefault <| isDefEq lhs0 e do return .continue
      return .visit { expr := rhs0, proof? := some proof }
    catch _ => return .continue
  -- Projection chain through a pair-element vector access:
  -- `Expression.eval env (c[i]).1  ~~>  ((eval env c)[i]).1`.
  -- The fold goes all the way to the whole-vector atom in ONE step: the intermediate
  -- spelling `(eval env c[i]).1` (eval of the pair ELEMENT) must never be produced —
  -- the pair Eval instance defeq-collapses, so that spelling self-loops against the
  -- scalar-canonical `eval_fieldPair` projection lemmas. The final spelling has no
  -- pair-typed eval node at all (getElem and `.1/.2` sit outside at value level).
  let (isFst, t) :=
    if subject.isAppOfArity ``Prod.fst 3 then (true, subject.appArg!)
    else if subject.isAppOfArity ``Prod.snd 3 then (false, subject.appArg!)
    else (false, subject)
  if (subject.isAppOfArity ``Prod.fst 3 || subject.isAppOfArity ``Prod.snd 3) &&
      t.isAppOfArity ``GetElem.getElem 8 then
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
      let some (lhs0, rhs0) := (← inferType proof).eq?.map (fun (_, l, r) => (l, r))
        | return .continue
      unless ← withDefault <| isDefEq lhs0 e do return .continue
      return .visit { expr := rhs0, proof? := some proof }
    catch _ => return .continue
  return .continue

simproc vectorAtomLift (Expression.eval _ _) := vectorAtomLiftCore
attribute [circuit_norm] vectorAtomLift

/-- The `Eval.eval`-headed link of the same chains (`eval env x[i] ~~> (eval env x)[i]`
for opaque-rooted provable-vector subjects). -/
private def vectorAtomLiftEvalCore (e : Expr) : SimpM Simp.Step := do
  let args := e.getAppArgs
  unless e.getAppFn.isConstOf ``Eval.eval && args.size ≥ 2 do
    return .continue
  let env := args[args.size - 2]!
  let subject := args[args.size - 1]!
  unless (chainRoot subject).isFVar do return .continue
  unless subject.isAppOfArity ``GetElem.getElem 8 do return .continue
  let gArgs := subject.getAppArgs
  let xs := gArgs[5]!
  let i := gArgs[6]!
  let hval := gArgs[7]!
  try
    let xsType ← withDefault <| whnf (← inferType xs)
    unless xsType.isAppOf ``Vector do return .continue
    let elemTy ← withDefault <| whnf (xsType.getAppArgs[0]!)
    let lemmaName := if elemTy.isAppOf ``Expression then
      ``ProvableType.getElem_eval_fields else ``getElem_eval_vector
    -- pair elements: `mkAppM` cannot solve the higher-order unification assigning the
    -- element `TypeMap`; pin `fieldPair` explicitly for Expression-component pairs
    let proof ← withDefault <| do
      if elemTy.isAppOf ``Prod then
        Meta.mkAppOptM ``getElem_eval_vector
          #[none, none, some (Lean.mkConst ``fieldPair), none, some env, some xs, some i, some hval]
      else
        mkAppM lemmaName #[env, xs, i, hval]
    let some (lhs0, rhs0) := (← inferType proof).eq?.map (fun (_, l, r) => (l, r))
      | return .continue
    unless ← withDefault <| isDefEq lhs0 e do return .continue
    return .visit { expr := rhs0, proof? := some proof }
  catch _ => return .continue

simproc vectorAtomLiftEval (Eval.eval _ _) := vectorAtomLiftEvalCore
attribute [circuit_norm] vectorAtomLiftEval

/-- Constructor heads that classify a vector subject as CONSTRUCTED: these decompose
inward. The complement — chains rooted in a free variable — folds outward via the
atom lifts. The two classes are disjoint and each rewrite's output stays in reach of
its own class only, which is what makes the bidirectional pair terminate (see the
struct literal/projection pair above for the same argument). -/
private def constructedVectorHeads : List Name :=
  [``Vector.map, ``Vector.mapRange, ``Vector.mapFinRange, ``Vector.mapIdx,
   ``Vector.ofFn, ``Vector.mk, ``Vector.append, ``Vector.cast,
   ``Vector.replicate, ``Vector.listCons,
   -- concrete witness-window literals
   ``ProvableType.varFromOffset]
   -- NOT `Vector.set`/`Vector.push`: set-chains have their own compact normal form
   -- (`eval_vector_set` — eval commutes with set, no whole-vector decomposition)

/-- The inward side of the vector balancing act: `eval` of a CONSTRUCTED vector
decomposes to the element map (`eval env (Vector.map f v) ~~> (Vector.map f v).map
(eval env)`, and then the element lemmas continue). Opaque subjects deliberately stay
folded whole-vector atoms — the spelling input premises are stated at. Replaces the
unconditional `eval_fields ↓` / `eval_vector` membership in the shared sets. -/
private def vectorEvalLiteralCore (e : Expr) : SimpM Simp.Step := do
  let args := e.getAppArgs
  unless e.getAppFn.isConstOf ``Eval.eval && args.size ≥ 2 do
    return .continue
  let env := args[args.size - 2]!
  let subject := args[args.size - 1]!
  let .const hd _ := subject.getAppFn | return .continue
  unless constructedVectorHeads.contains hd do return .continue
  -- dispatch on the element type instead of trying lemmas in sequence
  let subjectTy ← withDefault <| whnf (← inferType subject)
  unless subjectTy.isAppOf ``Vector do return .continue
  let elemTy ← withDefault <| whnf (subjectTy.getAppArgs[0]!)
  let lemmaName := if elemTy.isAppOf ``Expression then
    ``ProvableType.eval_fields else ``eval_vector
  try
    let proof ← withDefault <| mkAppM lemmaName #[env, subject]
    let some (_, lhs0, rhs0) := (← inferType proof).eq? | return .continue
    -- alias-typed subjects (`U32`, `SHA256State`, …) carry their own `Eval`
    -- instances and hide behind regular defs; validate at full transparency
    -- (the struct projection lift's precedent for pure-validation checks)
    unless lhs0 == e || (← withTransparency .all <| isDefEq lhs0 e) do return .continue
    return .visit { expr := rhs0, proof? := some proof }
  catch _ => return .continue

simproc vectorEvalLiteral (Eval.eval _ _) := vectorEvalLiteralCore
attribute [circuit_norm] vectorEvalLiteral

/-- Length of a syntactic `List` literal (`List.cons … List.nil` spine), if closed. -/
private partial def listLiteralLength? (l : Expr) : Option Nat :=
  if l.isAppOfArity ``List.cons 3 then (listLiteralLength? l.appArg!).map (· + 1)
  else if l.isAppOfArity ``List.nil 1 then some 0
  else none

/-- Refresh the size proof of a literal `Vector.mk` whose proof has gone stale:
`Vector.mk xs h ~~> Vector.mk xs (h' : xs.size = n)` when `h`'s *stated* array is not
the current `xs`.

Simp rewrites inside `xs` (offset arithmetic in subcircuit-output literals) while
keeping the original size proof via proof-irrelevant congruence. Any later lemma that
binds the proof to a metavariable — `Vector.map_mk` matching `Vector.map ?f (Vector.mk
?xs ?h)` — then `checkTypes` the stale proof against the rewritten `xs`, and that
definitional comparison walks the two arrays element by element through unreduced
`localLength` offsets: seconds per match. The refreshed proof is `Eq.refl n` hinted at
`xs.size = n`, so the same `checkTypes` becomes a syntactic match, and the kernel
validates the hint by eager `Array.size` reduction, which walks only the list spine and
never inspects the elements. -/
def vectorMkProofRefreshCore (e : Expr) : SimpM Simp.Step := do
  unless e.isAppOfArity ``Vector.mk 4 do return .continue
  let #[α, n, xs, h] := e.getAppArgs | return .continue
  let some (_, szApp, _) := (← inferType h).eq? | return .continue
  -- fire only on a stale proof over a closed literal array with a literal length,
  -- where `Array.size xs` is guaranteed to reduce to `n` by spine-walking alone
  if szApp.isAppOfArity ``Array.size 2 && szApp.appArg! == xs then return .continue
  unless xs.isAppOfArity ``List.toArray 2 do return .continue
  let some len := listLiteralLength? xs.appArg! | return .continue
  unless n.nat? == some len do return .continue
  let natTy := mkConst ``Nat
  let szXs := mkApp2 (mkConst ``Array.size e.getAppFn.constLevels!) α xs
  let freshH := mkApp2 (mkConst ``id [.zero])
    (mkApp3 (mkConst ``Eq [.one]) natTy szXs n)
    (mkApp2 (mkConst ``Eq.refl [.one]) natTy n)
  return .visit { expr := mkApp4 e.getAppFn α n xs freshH, proof? := none }

simproc vectorMkProofRefresh (Vector.mk _ _) := vectorMkProofRefreshCore
attribute [circuit_norm] vectorMkProofRefresh

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

attribute [circuit_norm] ProvableStruct.structEvalProjectionProc
  ProvableStruct.structEvalLiteralProc ProvableStruct.structEvalProjectionEvalProc

end ProvableStruct
