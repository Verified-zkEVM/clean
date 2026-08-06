import Clean.Circuit.Explicit

/-!
# `computable_witnesses`

Automation for the common `FormalCircuitBase.ComputableWitnesses` proof shape.

The tactic uses controlled simp sets and unfolds only a `main` declaration in the current
scope; child subcircuit constants remain opaque, and their obligations are discharged
through the composition lemmas and `grind` rules in `Clean.Circuit.Subcircuit`.
-/

open Lean Meta Simp Elab Tactic

/-- Unfold circuit-valued wrapper definitions while respecting explicit-circuit boundaries. -/
elab "unfold_formal_circuit_consts" : tactic => do
  withMainContext do
    let noUnfold ← labelled `explicit_circuit_no_unfold
    let unfoldTypes ← labelled `explicit_circuit_unfold_type
    let names ← collectUnfoldableCircuitDecls (← getMainTarget) #[]
      (some noUnfold) (some unfoldTypes)
    for name in names do
      try
        evalTactic (← `(tactic| unfold $(mkIdent name)))
      catch _ =>
        pure ()

/-- Like `unfold_formal_circuit_consts`, but unfolds only constants whose type lands in
plain `Circuit` — inner wrapper defs like `add32` — never `FormalCircuit`-variant bundles,
so child subcircuits stay opaque for the composition machinery. -/
elab "unfold_plain_circuit_consts" : tactic => do
  withMainContext do
    let noUnfold ← labelled `explicit_circuit_no_unfold
    let unfoldTypes ← labelled `explicit_circuit_unfold_type
    let names ← collectUnfoldableCircuitDecls (← getMainTarget) #[]
      (some noUnfold) (some unfoldTypes)
    for name in names do
      let some ci := (← getEnv).find? name | continue
      unless ci.type.getForallBody.getAppFn.isConstOf `Circuit do continue
      try
        evalTactic (← `(tactic| unfold $(mkIdent name)))
      catch _ =>
        pure ()

namespace ComputableWitnesses

/--
Split equalities between applications of the same structure constructor using the
constructor's generated `injEq` theorem. This is supplied only to the controlled simp
passes in `computable_witnesses`; it does not affect the global simp set.
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
  try
    let params := lhs.getAppArgs[:info.numParams].toArray.map some
    let lhsFields := lhs.getAppArgs[info.numParams:].toArray.map some
    let rhsFields := rhs.getAppArgs[info.numParams:].toArray.map some
    let proof ← withTransparency .default <|
      mkAppOptM injEqName (params ++ lhsFields ++ rhsFields)
    let some (_, _, conjunction) := (← inferType proof).eq? | return .continue
    return .visit { expr := conjunction, proof? := some proof }
  catch _ =>
    return .continue

simproc structEqSplit (_ = _) := structEqSplitProc

/-- Heads under which concrete circuits' `localLength` metadata appears in
computable-witness goals. -/
private def localLengthHeads : List Name :=
  [`FormalCircuitBase.localLength, `ElaboratedCircuit.localLength,
   `Subcircuit.localLength, `Operations.localLength]

/-- Reduce a `localLength`-shaped term with the `circuit_norm` simp set — the same way
soundness proofs obtain lengths. This turns `Operations.localLength` of concrete
operation lists into arithmetic over bundled-circuit metadata projections *without*
executing the list: `whnf` evaluates such a list element by element (quadratic vector
pushes for `mapFinRange`-built circuits), which blows the heartbeat budget on larger
gadgets, while this path costs a few hundred heartbeats. -/
private def simpLocalLength (e : Expr) : MetaM Simp.Result := do
  let some ext ← getSimpExtension? `circuit_norm | return { expr := e }
  let ctx ← Simp.mkContext
    { zeta := true, beta := true, proj := true, iota := true, instances := true }
    (simpTheorems := #[← ext.getTheorems]) (← getSimpCongrTheorems)
  return (← Meta.simp e ctx).1

/-- Evaluate a closed ℕ-expression to a literal by folding `+`/`*` and whnf-reducing
leaves (the shape `elaborate_circuit` leaves `localLength` metadata in: arithmetic over
explicit-structure projections, whose whnf is a cheap literal-field lookup). Refuses to
whnf an `Operations.localLength` head — that executes the operations list; such terms
must go through `simpLocalLength` first. -/
private partial def natValOf (e : Expr) : MetaM (Option Nat) := do
  if let some k := e.rawNatLit? then return some k
  match_expr e with
  | HAdd.hAdd _ _ _ _ a b => do
      let some x ← natValOf a | return none
      let some y ← natValOf b | return none
      return some (x + y)
  | HMul.hMul _ _ _ _ a b => do
      let some x ← natValOf a | return none
      let some y ← natValOf b | return none
      return some (x * y)
  | Nat.add a b => do
      let some x ← natValOf a | return none
      let some y ← natValOf b | return none
      return some (x + y)
  | Nat.mul a b => do
      let some x ← natValOf a | return none
      let some y ← natValOf b | return none
      return some (x * y)
  | OfNat.ofNat _ k _ => natValOf k
  | _ => do
      if e.getAppFn.isConstOf `Operations.localLength then return none
      let e' ← try withDefault <| whnf e catch _ => return none
      if e' == e then return none
      natValOf e'

/-- Assert `localLength = <numeral>` equations for every closed `localLength`
application in the goal. `Subcircuit`'s offset index makes these terms unrewritable by
`simp` in dependent positions (no motive) — but a standalone copy of the term simplifies
fine, so each equation is proved by `circuit_norm` simp plus a defeq step on the reduced
form only. As hypotheses, `grind`'s arithmetic and `omega` can bridge the offset
spellings. -/
elab "assert_local_lengths" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  -- scan hypotheses too: after the structural split, length terms often live in
  -- intro'd premises rather than the leaf's conclusion
  let mut scan := #[tgt]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      scan := scan.push (← instantiateMVars decl.type)
  let seen ← IO.mkRef ((∅ : Std.HashSet Expr))
  let eqs ← IO.mkRef (#[] : Array (Expr × Simp.Result × Nat))
  for tgt in scan do
   tgt.forEach fun e => do
    let .const name _ := e.getAppFn | return ()
    unless localLengthHeads.contains name do return ()
    if e.hasLooseBVars || e.hasMVar then return ()
    if (← seen.get).contains e then return ()
    seen.modify (·.insert e)
    let r ← try simpLocalLength e catch _ => return ()
    let some k ← try natValOf r.expr catch _ => return () | return ()
    eqs.modify (·.push (e, r, k))
  let mut i := 0
  for (e, r, k) in (← eqs.get) do
    let lit := mkNatLit k
    let eqType ← mkEq e lit
    -- the defeq gap is only between the simp-reduced form and the numeral (cheap
    -- metadata projections + arithmetic); the reduction from the original spelling is
    -- carried by the simp proof, so neither elaborator nor kernel ever defeq-executes
    -- the raw operations list
    let finish ← mkExpectedTypeHint (← mkEqRefl r.expr) (← mkEq r.expr lit)
    -- re-key at the original spelling: simp states its proof for the beta/projection
    -- normal form of `e`; the hint bridges that (cheap) defeq gap so users of the
    -- hypothesis see exactly the goal's spelling
    let proof ← match r.proof? with
      | some p => mkExpectedTypeHint (← mkEqTrans p finish) eqType
      | none => mkExpectedTypeHint finish eqType
    liftMetaTactic fun goal => do
      let goal ← goal.assert (Name.mkSimple s!"h_ll_{i}") eqType proof
      let (_, goal) ← goal.intro1P
      return [goal]
    i := i + 1

/-- Definitional reduction of concrete `localLength` metadata to numerals. As a
`dsimproc` the rewrite is a defeq step, so it also applies inside `Subcircuit`'s
dependent offset positions where propositional rewrites cannot build a motive. -/
def reduceLocalLengthCore : Simp.DSimproc := fun e => do
  let .const name _ := e.getAppFn | return .continue
  unless name == `FormalCircuitBase.localLength ||
      name == `ElaboratedCircuit.localLength do return .continue
  if e.hasLooseBVars || e.hasMVar then return .continue
  let some k ← try natValOf e catch _ => return .continue | return .continue
  return .visit (mkNatLit k)

/- shape-only pattern: the localLength constants live downstream of this file, so they
cannot be named in the pattern; the proc bails immediately on other heads. Declared
without attribute registration — the tactic's controlled simp passes reference it by
name; registering it into any shared set would change normal forms for every other
user of that set. -/
dsimproc_decl reduceLocalLength (_) := reduceLocalLengthCore

/-- Definitional reduction of child-output metadata (`c.output v m` and its
`ElaboratedCircuit.output c.main v m` spelling) to its explicit form (usually a
`varFromOffset` window). Unfolds ONLY bundle-typed constants and the metadata
projections — never `varFromOffset` or witness IR — so the eval simp lemmas keep
matching. As a dsimproc this also fires on binder-nested occurrences (simp enters
binders with fvars), including parameterized children like
`(KeccakRound.circuit roundConstants[i]).main`, which no closed universal fact can
state. -/
def reduceOutputMetadataCore : Simp.DSimproc := fun e => do
  let .const nm _ := e.getAppFn | return .continue
  unless nm == `FormalCircuitBase.output || nm == `ElaboratedCircuit.output do
    return .continue
  let arity := (← getConstInfo nm).type.getForallBinderNames.length
  unless e.getAppNumArgs == arity do return .continue
  if e.hasLooseBVars || e.hasMVar then return .continue
  let bundleHeads : List Name :=
    [`FormalCircuitBase, `FormalCircuit, `GeneralFormalCircuit,
     `GeneralFormalCircuit.WithHint, `FormalAssertion, `ElaboratedCircuit]
  -- unfold bundle-typed constants, the metadata projections, and Var-typed helper
  -- defs (e.g. `Rotation64.output` as a named elaborated output); iterate because
  -- helpers only surface after the bundle unfolds
  let collectUnfolds (t : Expr) : MetaM (Array Name) := do
    let names ← IO.mkRef (#[] : Array Name)
    t.forEach fun sub => do
      let .const c _ := sub | return ()
      let some ci := (← getEnv).find? c | return ()
      let body := ci.type.getForallBody
      let isBundle := bundleHeads.contains body.getAppFn.constName
      let isVarTyped := body.getAppFn.isConstOf `CircuitType.Var ||
        (body.isApp && body.getAppFn.isConst &&
          body.appArg!.getAppFn.isConstOf `Expression)
      if isBundle || isVarTyped then
        names.modify (·.push c)
    return (← names.get)
  let mut w := e
  for _ in [0:3] do
    let mut thms : SimpTheorems := {}
    for c in (← collectUnfolds w) do
      thms ← thms.addDeclToUnfold c
    thms ← thms.addDeclToUnfold `FormalCircuitBase.output
    thms ← thms.addDeclToUnfold `ElaboratedCircuit.output
    let ctx ← Simp.mkContext
      { zeta := true, beta := true, proj := true, iota := true, instances := true }
      (simpTheorems := #[thms]) (← Meta.getSimpCongrTheorems)
    let w' := (← Meta.dsimp w ctx).1
    if w' == w then break
    w := w'
  if w == e || w.getAppFn.isConstOf `FormalCircuitBase.output ||
      w.getAppFn.isConstOf `ElaboratedCircuit.output then
    return .continue
  -- accept only metadata-explicit results: a bundle whose `output` falls back to
  -- `(main v n).1` reduces to a worse spelling than the original — the chainer's
  -- per-instance facts key on the `output` form
  let leakedCircuit ← IO.mkRef false
  w.forEach fun sub => do
    let .const c _ := sub | return ()
    let some ci := (← getEnv).find? c | return ()
    if ci.type.getForallBody.getAppFn.isConstOf `Circuit then
      leakedCircuit.set true
  if (← leakedCircuit.get) then return .continue
  return .visit w

dsimproc_decl reduceOutputMetadata (_) := reduceOutputMetadataCore

/-- Collect fully-applied child-output terms: `c.output v k` and its pre-normalization
spelling `(subcircuit c v k).1` (definitionally equal, handled by unification). -/
partial def collectOutputsGo (e : Expr) (seen : IO.Ref (Std.HashSet Expr))
    (acc : IO.Ref (Array Expr)) : MetaM Unit := do
  match e with
  | .app f a => collectOutputsGo f seen acc; collectOutputsGo a seen acc
  | .lam _ t b _ => collectOutputsGo t seen acc; collectOutputsGo b seen acc
  | .forallE _ t b _ => collectOutputsGo t seen acc; collectOutputsGo b seen acc
  | .letE _ t v b _ =>
      collectOutputsGo t seen acc; collectOutputsGo v seen acc; collectOutputsGo b seen acc
  | .mdata _ b => collectOutputsGo b seen acc
  | .proj _ _ b => collectOutputsGo b seen acc
  | _ => pure ()
  let .const nm _ := e.getAppFn | return ()
  let isOutput := nm == `FormalCircuitBase.output ||
    (nm == `Prod.fst && e.getAppNumArgs ≥ 1 && e.appArg!.getAppFn.isConstOf `subcircuit)
  if isOutput && !e.hasLooseBVars && !e.hasMVar then
    unless (← seen.get).contains e do
      seen.modify (·.insert e)
      unless (← instantiateMVars (← inferType e)).isForall do
        acc.modify (·.push e)

/-- Forward-chain child-output equality facts: for each collected output term, build
`output_of_input_eq` in tactic context — where the definitional dsimprocs can normalize
the `c.localLength v` bound — and re-key the fact at the goal's own eval spelling
(the lemma's conclusion uses a different, defeq eval-instance atom; `grind` congruence
works on syntactic atoms). `grind` cannot run simprocs, so letting it instantiate the
composition rules would re-create opaque length atoms. -/
elab "chain_output_facts" : tactic => withMainContext do
  try evalTactic (← `(tactic| beta_reduce)) catch _ => pure ()
  let tgt ← instantiateMVars (← getMainTarget)
  -- Universal child-output metadata facts. Binder-nested outputs (e.g. inside a
  -- `Vector.mapFinRange` lambda) cannot be chained per instance — the term has loose
  -- bvars — and `grind` does not look under binders. Instead, state
  -- `∀ v m, c.output v m = <reduced>` once per closed output prefix (bundle constant
  -- plus instances), prove it by the `circuit_norm` reduction of the metadata
  -- projection (cheap: `elaborate_circuit` stores it explicitly), and rewrite it
  -- through goal and hypotheses — `simp` rewrites under binders.
  let outputArity := (← getConstInfo `FormalCircuitBase.output).type.getForallBinderNames.length
  let prefixes ← IO.mkRef (#[] : Array Expr)
  tgt.forEach fun e => do
    unless e.getAppFn.isConstOf `FormalCircuitBase.output do return ()
    -- exact arity only: every partial application along the spine is also visited
    unless e.getAppNumArgs == outputArity do return ()
    -- binder-nested occurrences only: closed occurrences are handled per instance by
    -- the chaining loop below, and rewriting them away would detach the goal's atoms
    -- from the chained `o_chain` facts
    unless e.hasLooseBVars do return ()
    let pfx := e.appFn!.appFn!
    if pfx.hasLooseBVars || pfx.hasMVar then return ()
    prefixes.modify fun a => if a.contains pfx then a else a.push pfx
  for pfx in (← prefixes.get) do
    let emit : TacticM Unit := do
      let factData? ← forallBoundedTelescope (← inferType pfx) (some 2) fun vs _ => do
        if vs.size = 2 then do
          let app := mkAppN pfx vs
          let r ← simpLocalLength app
          if r.expr != app then do
            let eqTy ← mkEq app r.expr
            let prf ← match r.proof? with
              | some pr => pure pr
              | none => mkExpectedTypeHint (← mkEqRefl app) eqTy
            pure (some (← mkForallFVars vs eqTy, ← mkLambdaFVars vs prf))
          else do
            -- named bundles reduce definitionally, not by simp: the metadata is an
            -- explicit structure field (the manual-proof `hout := fun _ _ => rfl`).
            -- Unfold ONLY the bundle constant and its projection — full `whnf` would
            -- keep going through `varFromOffset` into an exploded element-literal that
            -- no eval simp lemma matches.
            let mut thms : SimpTheorems := {}
            let bundleHeads : List Name :=
              [`FormalCircuitBase, `FormalCircuit, `GeneralFormalCircuit,
               `GeneralFormalCircuit.WithHint, `FormalAssertion, `ElaboratedCircuit]
            let names ← IO.mkRef (#[] : Array Name)
            pfx.appArg!.forEach fun sub => do
              let .const c _ := sub | return ()
              let some ci := (← getEnv).find? c | return ()
              if bundleHeads.contains ci.type.getForallBody.getAppFn.constName then
                names.modify (·.push c)
            for c in (← names.get) do
              thms ← thms.addDeclToUnfold c
            thms ← thms.addDeclToUnfold `FormalCircuitBase.output
            thms ← thms.addDeclToUnfold `ElaboratedCircuit.output
            let ctx ← Simp.mkContext
              { zeta := true, beta := true, proj := true, iota := true, instances := true }
              (simpTheorems := #[thms]) (← getSimpCongrTheorems)
            let w := (← Meta.dsimp app ctx).1
            if w == app || w.getAppFn.isConstOf `FormalCircuitBase.output then pure none
            else do
              let eqTy ← mkEq app w
              let prf ← mkExpectedTypeHint (← mkEqRefl app) eqTy
              pure (some (← mkForallFVars vs eqTy, ← mkLambdaFVars vs prf))
        else pure none
      let some (factTy, factPrf) := factData? | return
      liftMetaTactic fun g => do
        let g ← g.assert `o_meta factTy factPrf
        let (_, g) ← g.intro1P
        return [g]
      -- goal only: `at *` would rewrite the fact with itself into `True`
      try evalTactic (← `(tactic| simp only [$(mkIdent `o_meta):term])) catch _ => pure ()
    try emit catch _ => pure ()
  withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let mut hA? : Option (Name × Expr × Expr) := none
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if ty.getAppFn.isConstOf `ProverEnvironment.AgreesBelow then
      let args := ty.getAppArgs
      if args.size ≥ 2 then
        hA? := some (decl.userName, args[args.size - 2]!, args[args.size - 1]!)
  let some (hAName, envE, envE') := hA? | return
  let seen ← IO.mkRef ((∅ : Std.HashSet Expr))
  let acc ← IO.mkRef (#[] : Array Expr)
  collectOutputsGo tgt seen acc
  for o in (← acc.get) do
    let step (lemName : Name) : TacticM Unit := do
      let lem ← mkConstWithFreshMVarLevels lemName
      let (ms, _, concl) ← forallMetaTelescope (← inferType lem)
      let some (_, lhs, rhs) := concl.eq? | throwError "conclusion not an equality"
      unless ← isDefEq lhs.appArg! o do throwError "output does not unify"
      discard <| isDefEq lhs.appFn!.appArg!.appArg! envE
      discard <| isDefEq rhs.appFn!.appArg!.appArg! envE'
      let mainG ← getMainGoal
      for m in ms do
        let mid := m.mvarId!
        unless ← mid.isAssigned do
          let mty ← instantiateMVars (← mid.getType)
          if (← inferType mty).isProp then
            setGoals [mid]
            if mty.getAppFn.isConstOf `ProverEnvironment.AgreesBelow then
              evalTactic (← `(tactic|
                exact $(mkIdent `ProverEnvironment.agreesBelow_of_le) $(mkIdent hAName)
                  (by simp only [reduceLocalLength]; omega)))
            else
              evalTactic (← `(tactic| first
                | assumption
                | ((try simp only [circuit_norm]); grind)))
      let proof ← instantiateMVars (mkAppN lem ms)
      if proof.hasExprMVar then throwError "open premises"
      -- state the fact with freshly-synthesized (canonical) eval instances: the
      -- lemma's conclusion carries composite instance spellings, and grind's
      -- congruence works on syntactic atoms — the goal-side evals (via the
      -- eval_mk rules) use the canonical synthesis
      let mut ptype ← instantiateMVars (← inferType proof)
      let mut proofF := proof
      -- re-key the fact at the goal's own eval spelling: the lemma's conclusion uses
      -- a different (defeq) eval-instance atom, and grind's congruence works on
      -- syntactic atoms; the goal is normalized before chaining, so its component
      -- evals of the output term are present as subterms
      let sides ← IO.mkRef (#[] : Array Expr)
      tgt.forEach fun sub => do
        if !sub.hasLooseBVars && sub.isApp && sub.appArg! == o then
          sides.modify fun a => if a.contains sub then a else a.push sub
      let arr ← sides.get
      if arr.size == 2 then
        try
          let e0 := arr[0]!
          let e1 := arr[1]!
          let l := if e0.appFn!.appArg!.appArg! == envE then e0 else e1
          let r := if l == e0 then e1 else e0
          let eqTy ← mkEq l r
          proofF ← mkExpectedTypeHint proof eqTy
          ptype := eqTy
        catch _ => pure ()
      setGoals [mainG]
      liftMetaTactic fun g => do
        let g ← g.assert `o_chain ptype proofF
        let (_, g) ← g.intro1P
        return [g]
    let mut done := false
    for lemName in [`FormalCircuit.output_of_input_eq, `GeneralFormalCircuit.output_of_input_eq] do
      unless done do
        let st ← Tactic.saveState
        try
          step lemName
          done := true
        catch _ =>
          st.restore

/-- Split conjunctions and intro binders down to per-obligation leaves. `apply`/`intro`
use whnf, so conjunctions hidden behind definitional unfolding (`Operations.forAll` on
concrete op lists) split as well; child obligations stay intact via the head guard. -/
private partial def splitStep (g : MVarId) (fuel : Nat) : MetaM (List MVarId) := do
  if fuel == 0 then return [g]
  let _t := (← instantiateMVars (← g.getType)).consumeMData
  -- `apply`/`intro` unify up to whnf, which also splits conjunctions reachable only
  -- by definitional unfolding (`Operations.forAll` over bind-chains). This is safe
  -- only because `unfold_formal_circuit_consts` ran first: whnf-unifying against a
  -- still-opaque inner circuit would symbolically execute it (heartbeat/memory
  -- catastrophe on the bit-decomposed gadgets, and the runtime exception escapes
  -- `try`). The `Subcircuit.ComputableWitnesses` head guard above keeps child
  -- obligations intact.
  match ← observing? (g.apply (mkConst ``And.intro)) with
  | some gs =>
    gs.foldlM (init := []) fun acc g' => do
      return acc ++ (← splitStep g' (fuel - 1))
  | none =>
    match ← observing? g.intro1P with
    | some (_, g') => splitStep g' (fuel - 1)
    | none => return [g]

private def splitStructure : TacticM Unit :=
  liftMetaTactic fun g => splitStep g 512

/-- Find a local variable of `ProvableStruct` type (e.g. an opaque circuit input) that can be
destructured: `simp`/`grind` do not iota-reduce the `match` coming from `main`'s destructuring
`let` against an opaque variable, so the tactic case-splits such variables up front. -/
private def findProvableStructVar : TacticM (Option FVarId) :=
  withMainContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      -- `.instances` whnf, not `.reducible`: inputs are typed through the `Var M F` class
      -- projection, which does not reduce at reducible transparency
      let ty ← withTransparency .instances <| whnf (← instantiateMVars decl.type)
      let .const tyName _ := ty.getAppFn | continue
      unless isStructure (← getEnv) tyName do continue
      let args := ty.getAppArgs
      unless args.size ≥ 1 do continue
      let M := mkAppN ty.getAppFn args.pop
      let inst ← try? do
        synthInstance (← mkAppM ``ProvableStruct #[M])
      if inst.isSome then
        return some decl.fvarId
    return none

/-- Destructure all `ProvableStruct`-typed local variables (fixpoint, bounded). -/
private def destructureProvableStructVars : TacticM Unit := do
  for _ in [0:8] do
    if (← getGoals).isEmpty then return
    let some fvarId ← findProvableStructVar | return
    liftMetaTactic fun goal => do
      let subgoals ← goal.cases fvarId
      return subgoals.map (·.mvarId) |>.toList

private def runComputableWitnesses (extraTerms : Array (TSyntax `term)) : TacticM Unit := do
  let lemmasArray ← extraTerms.mapM fun term =>
    `(Lean.Parser.Tactic.simpLemma| $term:term)
  let simpPass : TacticM Unit := do
    unless (← getGoals).isEmpty do
      try
        evalTactic (← `(tactic| simp only [circuit_norm, computable_witnesses_norm,
          ComputableWitnesses.structEqSplit, $lemmasArray,*]))
      catch _ =>
        pure ()
  simpPass
  unless (← getGoals).isEmpty do
    try
      evalTactic (← `(tactic| unfold $(mkIdent `main):ident))
    catch _ =>
      pure ()
    -- One boundary rule, mirroring the library's own: plain-`Circuit`-typed constants
    -- are the current circuit's own structure and always unfold; `FormalCircuit`-variant
    -- bundles are proof boundaries and never do (unfolding them destroys the
    -- `c.output`/`toSubcircuit` spellings the composition machinery patterns on, and
    -- leaving a wrapper folded makes And-unification whnf-execute the whole circuit).
    try evalTactic (← `(tactic| unfold_plain_circuit_consts)) catch _ => pure ()
    simpPass
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| intros))
  destructureProvableStructVars
  simpPass
  unless (← getGoals).isEmpty do
    -- deterministic split to leaves
    splitStructure
    -- per-leaf: cheap normalization + head dispatch
    -- Base close plus one shape-dispatched route: `Vector.ext` is only ever correct on
    -- an equality of vectors, so it is selected by inspecting the goal, not tried
    -- blindly in an alternatives chain.
    let baseClose : TSyntax `tactic ← `(tactic|
      first
        | (simp_all; done)
        | (simp_all [circuit_norm, computable_witnesses_norm]; done)
        | grind)
    let vecClose : TSyntax `tactic ← `(tactic|
      first
        | (simp_all; done)
        | (simp_all only [circuit_norm, eval_vector, Vector.map_mk, List.map_toArray,
             List.map_cons, List.map_nil, reduceOutputMetadata,
             Vector.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true,
             Vector.map_ofFn, Vector.ext_iff, Vector.getElem_ofFn, Function.comp_def,
             Vector.getElem_map, Vector.getElem_append,
             Vector.getElem_mapFinRange, Vector.getElem_mapIdx,
             Vector.getElem_set, Vector.getElem_mapRange,
             $lemmasArray,*]
           all_goals ((intros; (try split_ifs)) <;>
               ((try simp only [ProvableType.eval_varFromOffset, circuit_norm, eval_vector,
                  Vector.mapRange_succ, Vector.mapRange_zero, Vector.mk.injEq, Array.mk.injEq,
                  List.cons.injEq, and_true, $lemmasArray,*]);
                ((try and_intros) <;> grind))))
        | (refine Vector.ext fun j hj => ?_
           simp only [getElem_eval_vector, Vector.getElem_map, Vector.getElem_append,
             Vector.getElem_mapFinRange, Vector.getElem_ofFn, Vector.getElem_mapIdx]
           (try split_ifs) <;> grind [Vector.getElem_map, getElem_eval_vector])
        | grind)
    -- the window/elementwise route applies to eval-congruence goals: both sides are
    -- eval applications of the same variable term under the two environments (output
    -- windows, child-output metadata, vector states) — recognized by shape, whether
    -- the value type is a vector or a provable struct
    let isEvalCongrEq : TacticM Bool := withMainContext do
      let t := (← instantiateMVars (← getMainTarget)).consumeMData
      let some (_, lhs, rhs) := t.eq? | return false
      let ty ← instantiateMVars (← inferType lhs)
      let tyW ← withTransparency .instances <| whnf ty
      if tyW.getAppFn.isConstOf ``Vector then return true
      if lhs.isApp && rhs.isApp && lhs.appArg! == rhs.appArg! &&
          (lhs.getAppFn.isConstOf `Eval.eval || lhs.getAppFn.isConstOf `Expression.eval) then
        return true
      -- goals over witness variables/windows: agreement-based congruence territory
      return (t.find? fun e =>
        e.getAppFn.isConstOf `Expression.var ||
        e.getAppFn.isConstOf `ProvableType.varFromOffset).isSome
    -- when both sides of an eval-congruence goal share the same argument whose head is
    -- a plain (non-bundle) definition — e.g. a child's Var-typed output metadata def like
    -- `Permutation.stateVar`, already substituted for `c.output` by metadata reduction —
    -- unfold that head: it is data, not a proof boundary, and unfolding exposes the
    -- `varFromOffset` spelling the eval simp lemmas need
    let unfoldSharedEvalArgHeads : TacticM Unit := withMainContext do
      let bundleHeads : List Name :=
        [`FormalCircuitBase, `FormalCircuit, `GeneralFormalCircuit,
         `GeneralFormalCircuit.WithHint, `FormalAssertion, `Circuit]
      for _ in [0:4] do
        if (← getGoals).isEmpty then return
        let t := (← instantiateMVars (← getMainTarget)).consumeMData
        let some (_, lhs, rhs) := t.eq? | return
        unless lhs.isApp && rhs.isApp && lhs.appArg! == rhs.appArg! do return
        let .const argHead _ := lhs.appArg!.getAppFn | return
        let some ci := (← getEnv).find? argHead | return
        unless ci.hasValue do return
        -- only `Var`-typed metadata defs (e.g. a child's output helper like
        -- `Permutation.stateVar : Var KeccakState (F p)`, stored reducible-unfolded as
        -- `KeccakState (Expression (F p))`): polymorphic operator heads must keep their
        -- spelling for the vector simp lemmas, and witness-IR construction defs
        -- (`FExpr`-typed values) must keep theirs for the IR eval lemmas
        let body := ci.type.getForallBody
        let isVarTyped := body.getAppFn.isConstOf `CircuitType.Var ||
          (body.isApp && body.getAppFn.isConst &&
            body.appArg!.getAppFn.isConstOf `Expression)
        unless isVarTyped do return
        try evalTactic (← `(tactic| unfold $(mkIdent argHead):ident)) catch _ => return
    -- `grind` internalizes every hypothesis and whnf-normalizes its terms; a
    -- `localLength`-equation whose LHS is a raw operations list (e.g. Permutation's 24
    -- rounds) blows the heartbeat budget during that normalization. The equations have
    -- already done their work (offset discharge, AgreesBelow bounds) by close time.
    let clearOpsLengthHyps : TacticM Unit := withMainContext do
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        let toxic := (← instantiateMVars decl.type).find? fun e =>
          e.getAppFn.isConstOf `Operations.localLength
        if toxic.isSome then
          try liftMetaTactic fun g => do return [← g.clear decl.fvarId] catch _ => pure ()
    -- `assumption` isDefEq-matches the goal against every hypothesis; a mismatched
    -- pair of large vector terms whnf-executes them (heartbeat blowup). Syntactic
    -- matching is enough here: the chain re-keys facts at the goal's own spelling.
    let syntacticAssumption : TacticM Unit := withMainContext do
      let tgt ← instantiateMVars (← getMainTarget)
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        if (← instantiateMVars decl.type) == tgt then
          (← getMainGoal).assign decl.toExpr
          replaceMainGoal []
          return
      throwError "syntacticAssumption: no match"
    let evalCloseRun : TacticM Unit := do
      if (← getGoals).isEmpty then return
      try clearOpsLengthHyps catch _ => pure ()
      if (← try syntacticAssumption; pure true catch _ => pure false) then return
      if ← isEvalCongrEq then
        try unfoldSharedEvalArgHeads catch _ => pure ()
        dbg_trace "cw# vecClose"
        evalTactic vecClose
        dbg_trace "cw# vecClose done"
      else
        dbg_trace "cw# baseClose"
        evalTactic baseClose
        dbg_trace "cw# baseClose done"
    let leafDispatch : TacticM Unit := withMainContext do
      -- inaccessible hyp names (from intro1P) break the chainer's delab roundtrip
      try evalTactic (← `(tactic| expose_names)) catch _ => pure ()
      -- leaf-local simp (normalizes loop-instantiated lengths), then dispatch
      try
        evalTactic (← `(tactic| simp only [circuit_norm, computable_witnesses_norm,
          ComputableWitnesses.structEqSplit, reduceLocalLength, reduceOutputMetadata,
          $lemmasArray,*] at *))
      catch _ => pure ()
      if (← getGoals).isEmpty then return
      dbg_trace "cw# pre-assert"
      evalTactic (← `(tactic| assert_local_lengths))
      dbg_trace "cw# post-assert"
      withMainContext do
        let t := (← instantiateMVars (← getMainTarget)).consumeMData
        let .const headName _ := t.getAppFn | evalCloseRun
        if headName == `Subcircuit.ComputableWitnesses then
          let tryVariant (nm : Name) : TacticM Bool := do
            let st ← Tactic.saveState
            try
              -- offset_eq variants keep the subcircuit's type-index offset separate
              -- from the computability offset: unifying a single-`n` rule against two
              -- defeq-but-differently-spelled offsets makes isDefEq whnf-execute the
              -- operations list (heartbeat blowup on mapFinRange-built circuits). The
              -- `m = n` premise is discharged arithmetically over the asserted lengths.
              evalTactic (← `(tactic| refine $(mkIdent nm) _
                (by
                  (try simp only [circuit_norm, computable_witnesses_norm,
                    reduceLocalLength, $lemmasArray,*]) <;> omega) fun h_agrees => ?_))
              pure true
            catch _ =>
              st.restore
              pure false
          let mut applied := false
          for nm in [`FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq,
              `GeneralFormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq,
              `GeneralFormalCircuit.WithHint.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq,
              `FormalAssertion.toSubcircuit_computableWitnesses_onlyAccessedBelow_of_offset_eq] do
            unless applied do
              if ← tryVariant nm then applied := true
          dbg_trace s!"cw# variant applied={applied}"
          if applied then
            simpPass
            dbg_trace "cw# post-variant simpPass"
            unless (← getGoals).isEmpty do
              evalTactic (← `(tactic| (try chain_output_facts)))
              unless (← getGoals).isEmpty do
                evalCloseRun
          else
            evalTactic (← `(tactic| grind))
        else
          dbg_trace "cw# chain (non-CW head)"
          evalTactic (← `(tactic| (try chain_output_facts)))
          dbg_trace "cw# chained"
          unless (← getGoals).isEmpty do
            evalCloseRun
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      leafDispatch
    setGoals []

/--
Prove the standard computable-witness obligation using a controlled normalization pass,
unfolding of the current `main` declaration (child subcircuit constants remain opaque),
structural splitting of the operations/output conjunction, and `grind`.

Extra simp lemmas may be supplied as `computable_witnesses [lemma₁, lemma₂]` — e.g. a child
bundle name to reduce its `output`/`localLength` metadata when witness expressions embed the
child's output under a binder, where `grind`'s E-matching cannot reach it.
-/
syntax "computable_witnesses" ("[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| computable_witnesses $[[$terms:term,*]]?) =>
      runComputableWitnesses (terms.map (fun terms => terms.getElems) |>.getD #[])

/-- Diagnostic variant of `computable_witnesses` without the `simp_all` fallback, so
`grind`'s failure state is visible. Not for committed proofs. -/
syntax "computable_witnesses_probe" ("[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| computable_witnesses_probe $[[$terms:term,*]]?) => do
      let lemmasArray ← (terms.map (fun terms => terms.getElems) |>.getD #[]).mapM fun term =>
        `(Lean.Parser.Tactic.simpLemma| $term:term)
      evalTactic (← `(tactic| simp only [circuit_norm, computable_witnesses_norm,
        ComputableWitnesses.structEqSplit, $lemmasArray,*]))
      try evalTactic (← `(tactic| unfold $(mkIdent `main):ident)) catch _ => pure ()
      evalTactic (← `(tactic| simp only [circuit_norm, computable_witnesses_norm,
        ComputableWitnesses.structEqSplit, $lemmasArray,*]))
      evalTactic (← `(tactic| intros))
      destructureProvableStructVars
      evalTactic (← `(tactic| simp only [circuit_norm, computable_witnesses_norm,
        ComputableWitnesses.structEqSplit, $lemmasArray,*]))
      evalTacticSeq (← `(tacticSeq|
        apply And.intro
        · intros
          (try and_intros) <;> grind
        · grind))

end ComputableWitnesses
