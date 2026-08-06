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

/-- Evaluate a closed ℕ-expression to a literal by whnf plus folding of `+`/`*`
(the shape `elaborate_circuit` leaves `localLength` metadata in). -/
private partial def natValOf (e : Expr) : MetaM (Option Nat) := do
  let e ← try withDefault <| whnf e catch _ => return none
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
  | _ => return none

/-- Assert `localLength = <numeral>` equations (definitional, by `rfl`) for every closed
`localLength` application in the goal. `Subcircuit`'s offset index makes these terms
unrewritable by `simp` in dependent positions; as hypotheses, `grind`'s arithmetic and
`omega` can bridge the offset spellings instead. -/
elab "assert_local_lengths" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let seen ← IO.mkRef ((∅ : Std.HashSet Expr))
  let eqs ← IO.mkRef (#[] : Array (Expr × Nat))
  tgt.forEach fun e => do
    let .const name _ := e.getAppFn | return ()
    unless localLengthHeads.contains name do return ()
    if e.hasLooseBVars || e.hasMVar then return ()
    if (← seen.get).contains e then return ()
    seen.modify (·.insert e)
    let some k ← try natValOf e catch _ => return () | return ()
    eqs.modify (·.push (e, k))
  let mut i := 0
  for (e, k) in (← eqs.get) do
    let eqType ← mkEq e (mkNatLit k)
    let proof ← mkExpectedTypeHint (← mkEqRefl e) eqType
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
cannot be named in the pattern; the proc bails immediately on other heads -/
dsimproc reduceLocalLength (_) := reduceLocalLengthCore

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
    let step : TacticM Unit := do
      let lem ← mkConstWithFreshMVarLevels `FormalCircuit.output_of_input_eq
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
                | (simp only [circuit_norm]; grind)))
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
    let st ← Tactic.saveState
    try step
    catch _ => st.restore

/-- Split conjunctions and intro binders down to per-obligation leaves. `apply`/`intro`
use whnf, so conjunctions hidden behind definitional unfolding (`Operations.forAll` on
concrete op lists) split as well; child obligations stay intact via the head guard. -/
private partial def splitStep (g : MVarId) (fuel : Nat) : MetaM (List MVarId) := do
  if fuel == 0 then return [g]
  let t := (← instantiateMVars (← g.getType)).consumeMData
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
    let evalClose : TSyntax `tactic ← `(tactic|
      first
        | assumption
        | (congr 1 <;> first | assumption | grind)
        | (simp_all only [circuit_norm, eval_vector, Vector.map_mk, List.map_toArray,
             List.map_cons, List.map_nil, ProvableType.eval_varFromOffset, Vector.mapRange_succ,
             Vector.mapRange_zero, Vector.mk.injEq, Array.mk.injEq, List.cons.injEq, and_true,
             Vector.map_ofFn, Vector.ext_iff, Vector.getElem_ofFn, Function.comp_def,
             $lemmasArray,*]
           (try and_intros) <;> grind)
        | (refine Vector.ext fun j hj => ?_
           simp only [getElem_eval_vector, Vector.getElem_map, Vector.getElem_append,
             Vector.getElem_mapFinRange, Vector.getElem_ofFn, Vector.getElem_mapIdx]
           (try split_ifs) <;> grind [Vector.getElem_map, getElem_eval_vector])
        | grind)
    let leafDispatch : TacticM Unit := withMainContext do
      -- inaccessible hyp names (from intro1P) break the chainer's delab roundtrip
      try evalTactic (← `(tactic| expose_names)) catch _ => pure ()
      -- leaf-local simp (normalizes loop-instantiated lengths), then dispatch
      try
        evalTactic (← `(tactic| simp only [circuit_norm, computable_witnesses_norm,
          ComputableWitnesses.structEqSplit, reduceLocalLength,
          $lemmasArray,*] at *))
      catch _ => pure ()
      if (← getGoals).isEmpty then return
      evalTactic (← `(tactic| assert_local_lengths))
      withMainContext do
        let t := (← instantiateMVars (← getMainTarget)).consumeMData
        let .const headName _ := t.getAppFn | evalTactic evalClose
        if headName == `Subcircuit.ComputableWitnesses then
          let tryVariant (nm : Name) : TacticM Bool := do
            let st ← Tactic.saveState
            try
              evalTactic (← `(tactic| refine $(mkIdent nm) _ fun h_agrees => ?_))
              pure true
            catch _ =>
              st.restore
              pure false
          let mut applied := false
          for nm in [`FormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow,
              `GeneralFormalCircuit.toSubcircuit_computableWitnesses_onlyAccessedBelow,
              `FormalAssertion.toSubcircuit_computableWitnesses_onlyAccessedBelow] do
            unless applied do
              if ← tryVariant nm then applied := true
          if applied then
            simpPass
            evalTactic (← `(tactic| (try chain_output_facts)))
            evalTactic evalClose
          else
            evalTactic (← `(tactic| grind))
        else
          evalTactic (← `(tactic| ((try chain_output_facts); $evalClose:tactic)))
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      try leafDispatch
      catch e =>
        throw e
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
