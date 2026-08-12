import Clean.Circuit.Explicit
import Clean.Utils.Tactics.ProvableStructSimp

/-!
# `computable_witnesses`

Automation for `FormalCircuitBase.ComputableWitnesses` — the obligation that every
witness generator of a circuit reads the prover environment only **below its own
offset** (`ProverEnvironment.AgreesBelow`, which also holds hint/data fixed). It is the
default tactic for the `computableWitnesses` field, so most gadgets need no field at
all; hints can be passed as `computable_witnesses [lemma₁, …]` (extra simp lemmas, e.g.
a child bundle name whose metadata is otherwise stuck under a binder).

## Pipeline

1. **Normalize** with `circuit_norm` + `computable_witnesses_norm`, plus the current
   `main` (resolved from scope and self-supplied as a simp lemma) and any hints.
   `unfold_plain_circuit_consts` additionally unfolds plain-`Circuit`-typed wrapper
   defs. `FormalCircuit`-variant bundles are proof boundaries and are **never**
   unfolded — their obligations go through the composition lemmas instead.
2. **Destructure** struct variables via `provable_struct_simp`'s destructure pass
   (the CW obligation has no value-level input variable, so `input`'s only
   selectable footprint is `main`'s destructuring match, which `simp`/`grind` do
   not iota-reduce against an opaque variable).
3. **Reduce child-output metadata** (`reduceOutputMetadata`, a standalone
   theorem-free dsimp step): after every normalization pass — reduced
   `varFromOffset` windows drift into exploded element literals under further
   theorem rewriting — and directly before the split.
4. **Split** the resulting conjunction into per-obligation leaves (`splitStep`):
   syntactic `And`/`∀` head dispatch — the goal is simp-normalized here, and a
   defeq-hidden shape is left whole as a leaf (unifying against it would
   symbolically execute still-folded groups, e.g. a 32-wide `Circuit.forEach`).
   Goals headed by `Subcircuit.ComputableWitnesses` stay whole.
5. **Per leaf**: for leaves with a `Circuit.forEach` group, `ring_nf`; then
   `assert_local_lengths`, then dispatch:
   * a `Subcircuit.ComputableWitnesses` head is refined with the `_of_offset_eq`
     composition rules — separate offset metavariables, with the `m = n` premise
     discharged arithmetically, so unification never defeq-executes an operations
     list — leaving the `OnlyAccessedBelow` premise;
   * `chain_output_facts` derives child-output congruence facts
     (`FormalCircuit.output_of_input_eq` instances, re-keyed at the goal's own eval
     spelling) plus universal metadata facts for binder-nested outputs;
   * the close routes by shape (`isEvalCongrEq`): vector/eval-congruence goals get the
     staged vector route (structural `simp_all`, close-hint step, then per-branch
     `split_ifs` → `envUnify` → `grind`); everything else takes the base route
     (`envUnify`, projection respelling, `grind` first, curated `simp_all` fallbacks).

## Key supporting pieces

* `reduceLocalLength` (dsimproc): definitional reduction of bundled `localLength`
  metadata to numerals (or symbolic normal forms for parameterized circuits). As a
  definitional rewrite it also fires inside `Subcircuit`'s dependent offset positions,
  where propositional rewrites cannot build a motive. It never touches
  `Operations.localLength` of a raw operations list — computing that by `whnf`
  executes the list (quadratic vector pushes for `mapFinRange`-built circuits);
  `assert_local_lengths` handles those spellings with a `circuit_norm`-simp-first
  reduction and asserts the equations as hypotheses with propositional proofs.
* `reduceOutputMetadata` (dsimproc, its own pre-split step): definitional in-place
  reduction of child output metadata, including binder-nested and parameterized
  children which no closed universal fact can state.
* `@[computable_witnesses_metadata]` (label attribute): opt-in marker for Var-typed
  gadget output-helper defs (`Permutation.stateVar`, `BLAKE3.G.output`, …) that the
  close may delta-expand to expose their `varFromOffset` spelling. Opt-in, because
  return-type shape cannot distinguish safe helpers from spellings the chained facts
  key on.
* All unfolding used by the tactic is **environment-clean** (`Meta.deltaExpand` +
  theorem-free `dsimp`): `simp [X]`/`unfold X` on a cross-module constant generates
  `X.eq_*` equation lemmas in the using module, and sibling modules doing this for a
  shared child collide on import.

Performance invariants (violating any of these historically produced 200 000-heartbeat
timeouts): never whnf-execute an operations list, never unfold a bundle, never let
`grind` internalize a hypothesis whose spelling contains a raw operations list
(`clearOpsLengthHyps`), and match goals against hypotheses syntactically before
attempting defeq (`syntacticAssumption`).
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
        replaceMainGoal [← Meta.unfoldTarget (← getMainGoal) name]
      catch _ =>
        pure ()

/-- Like `unfold_formal_circuit_consts`, but unfolds only constants whose type lands in
plain `Circuit` — inner wrapper defs like `add32` — never `FormalCircuit`-variant bundles,
so child subcircuits stay opaque for the composition machinery. -/
def unfoldPlainCircuitConsts : TacticM Unit := do
  withMainContext do
    let noUnfold ← labelled `explicit_circuit_no_unfold
    let unfoldTypes ← labelled `explicit_circuit_unfold_type
    let names ← collectUnfoldableCircuitDecls (← getMainTarget) #[]
      (some noUnfold) (some unfoldTypes)
    for name in names do
      let some ci := (← getEnv).find? name | continue
      unless ci.type.getForallBody.getAppFn.isConstOf `Circuit do continue
      try
        replaceMainGoal [← Meta.unfoldTarget (← getMainGoal) name]
      catch _ =>
        pure ()

elab "unfold_plain_circuit_consts" : tactic => unfoldPlainCircuitConsts

namespace ComputableWitnesses

/-- Heads under which concrete circuits' `localLength` metadata appears in
computable-witness goals. -/
def localLengthHeads : List Name :=
  [`FormalCircuitBase.localLength, `ElaboratedCircuit.localLength,
   `Subcircuit.localLength, `Operations.localLength]

/-- Run `x` under a local heartbeat sub-budget, converting a runtime timeout into
`none`. Used for `assert_local_lengths`' speculative length reductions, which would
otherwise symbolically execute opaque terms and kill the whole tactic (the runtime
exception escapes `try`). -/
def withProbeBudget {α : Type} (x : MetaM α) : MetaM (Option α) :=
  tryCatchRuntimeEx
    (withCurrHeartbeats do
      withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := 1000000 }) do
        some <$> x)
    (fun _ => pure none)

/-- Reduce a `localLength`-shaped term with the `circuit_norm` simp set — the same way
soundness proofs obtain lengths. This turns `Operations.localLength` of concrete
operation lists into arithmetic over bundled-circuit metadata projections *without*
executing the list: `whnf` evaluates such a list element by element (quadratic vector
pushes for `mapFinRange`-built circuits), which blows the heartbeat budget on larger
gadgets, while this path costs a few hundred heartbeats. -/
def simpLocalLength (e : Expr) : MetaM Simp.Result := do
  let some ext ← getSimpExtension? `circuit_norm | return { expr := e }
  let ctx ← Simp.mkContext
    { zeta := true, beta := true, proj := true, iota := true, instances := true }
    (simpTheorems := #[← ext.getTheorems]) (← getSimpCongrTheorems)
  return (← Meta.simp e ctx).1

/-! ### Meta simp

Every simp step of the tactic goes through `Lean.Meta.simpGoal`/`simpAll` with contexts
built once per invocation (`CwSimp.build` below). Quoted `simp` syntax resolves lemma
names at the use site, where an unresolvable name silently disables the entire call;
the meta path fails loudly at build time and skips re-elaborating the lemma lists on
every leaf. With the default `failIfUnchanged`, the meta calls keep quoted simp's
fail-on-no-progress behavior, so `try`/`attempt` wrappers retain their meaning. -/

/-- A registered simp attribute's theorem set, failing loudly if the set is unknown. -/
def getAttrTheorems (attr : Name) : CoreM SimpTheorems := do
  let some ext ← getSimpExtension? attr
    | throwError "computable_witnesses: unknown simp set '{attr}'"
  ext.getTheorems

/-- A registered simp attribute's simproc set, failing loudly if the set is unknown. -/
def getAttrSimprocs (attr : Name) : CoreM Simprocs := do
  let some ext ← Simp.getSimprocExtension? attr
    | throwError "computable_witnesses: unknown simproc set '{attr}'"
  ext.getSimprocs

/-- The entry-0 base of every quoted `simp only`: `eq_self` and `iff_self`
(`simpOnlyBuiltins`). Named lemmas are merged into this entry, so they take precedence
over the attribute sets, which simp tries in array order after it. -/
def simpOnlyBase : MetaM SimpTheorems :=
  Lean.Elab.Tactic.simpOnlyBuiltins.foldlM (·.addConst ·) ({} : SimpTheorems)

/-- Extend `init` with global lemma names (compile-time-checked ``name``s). -/
def theoremsOf (names : Array Name) (init : SimpTheorems) : MetaM SimpTheorems :=
  names.foldlM (init := init) fun thms n => thms.addConst n

/-- The meta form of `simp only [...]` on the main goal (`hyps := true` for
`... at *`, which like the quoted form simps the non-dependent prop hypotheses). -/
def metaSimp (ctx : Simp.Context) (procs : SimprocsArray := #[]) (hyps := false) :
    TacticM Unit := withMainContext do
  let g ← getMainGoal
  let fvarIds ← if hyps then g.getNondepPropHyps else pure #[]
  let (result?, _) ← Meta.simpGoal g ctx procs (fvarIdsToSimp := fvarIds)
  match result? with
  | none => replaceMainGoal []
  | some (_, g') => replaceMainGoal [g']

/-- The meta form of `simp_all only [...]` on the main goal. `simp_all` elaborates its
config as `Simp.ConfigCtx`, so `contextual := true` is part of its semantics — set it
here rather than in each stored context, which may be shared with `simp` positions. -/
def metaSimpAll (ctx : Simp.Context) (procs : SimprocsArray := #[]) : TacticM Unit :=
  withMainContext do
    let ctx ← ctx.setConfig { ctx.config with contextual := true }
    let (result?, _) ← Meta.simpAll (← getMainGoal) ctx procs
    match result? with
    | none => replaceMainGoal []
    | some g => replaceMainGoal [g]

/-- `circuit_norm`-only context and simprocs (the extension lookups are cached). -/
def cnSimp : TacticM (Simp.Context × SimprocsArray) := do
  return (← Simp.mkContext {}
    (simpTheorems := #[← simpOnlyBase, ← getAttrTheorems `circuit_norm])
    (← getSimpCongrTheorems), #[← getAttrSimprocs `circuit_norm])

/-- Meta `grind` (default configuration) on the main goal. -/
def metaGrind : TacticM Unit := do
  Lean.Elab.Tactic.grind (← getMainGoal) {} (only := false) (ps := #[]) (seq? := none)

/-- Meta `intros` on the main goal. -/
def metaIntros : TacticM Unit := do
  let (_, g) ← (← getMainGoal).intros
  replaceMainGoal [g]

/-- Meta `intros` on every goal. -/
def metaIntrosAll : TacticM Unit := do
  let mut acc := #[]
  for g in (← getGoals) do
    let (_, g') ← g.intros
    acc := acc.push g'
  setGoals acc.toList

/-- Meta `and_intros`: recursively split a syntactic `And` goal. Syntactic matching
only — the close routes' goals are simp-normalized here, and whnf-matching a defeq-
hidden conjunction could execute an operations list. -/
partial def andIntrosCore (g : MVarId) : MetaM (List MVarId) := do
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless t.isAppOfArity ``And 2 do return [g]
  let gs ← g.applyConst ``And.intro
  let mut acc := []
  for g' in gs do
    acc := acc ++ (← andIntrosCore g')
  return acc

/-- Meta `beta_reduce` on the main goal's target. -/
def betaReduceGoal : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let t' ← Core.betaReduce t
  unless t' == t do replaceMainGoal [← g.change t']

/-- Evaluate a closed ℕ-expression to a literal by folding `+`/`*` and whnf-reducing
leaves (the shape `elaborate_circuit` leaves `localLength` metadata in: arithmetic over
explicit-structure projections, whose whnf is a cheap literal-field lookup). Refuses to
whnf an `Operations.localLength` head — that executes the operations list; such terms
must go through `simpLocalLength` first. -/
partial def natValOf (e : Expr) : MetaM (Option Nat) := do
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
def assertLocalLengths : TacticM Unit := withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  -- scan hypotheses too: after the structural split, length terms often live in
  -- intro'd premises rather than the leaf's conclusion
  let mut scan := #[tgt]
  for decl in ← getLCtx do
    unless decl.isImplementationDetail do
      scan := scan.push (← instantiateMVars decl.type)
  let seen ← IO.mkRef ((∅ : Std.HashSet Expr))
  let eqs ← IO.mkRef (#[] : Array (Expr × Simp.Result × Option Nat))
  for tgt in scan do
   tgt.forEach fun e => do
    let .const name _ := e.getAppFn | return ()
    unless localLengthHeads.contains name do return ()
    if e.hasLooseBVars || e.hasMVar then return ()
    if (← seen.get).contains e then return ()
    seen.modify (·.insert e)
    unless (← try inferType e catch _ => return ()).isConstOf `Nat do return ()
    -- budgeted: simp/whnf on exotic length spellings (e.g. folded `forEach` groups)
    -- can be a runaway; skip the term rather than kill the tactic
    let some r ← withProbeBudget (try simpLocalLength e catch _ => pure { expr := e }) | return ()
    let some k? ← withProbeBudget (try natValOf r.expr catch _ => pure none) | return ()
    if k?.isNone && r.expr == e then return ()
    eqs.modify (·.push (e, r, k?))
  let mut i := 0
  for (e, r, k?) in (← eqs.get) do
    -- symbolic lengths (parameterized circuits, e.g. `Num2Bits.circuit (n+1)`) assert
    -- their simp normal form instead of a numeral — omega gets the bound arithmetic
    -- either way
    let lit := match k? with | some k => mkNatLit k | none => r.expr
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

elab "assert_local_lengths" : tactic => assertLocalLengths

/-- Definitional reduction of concrete `localLength` metadata to numerals. As a
`dsimproc` the rewrite is a defeq step, so it also applies inside `Subcircuit`'s
dependent offset positions where propositional rewrites cannot build a motive. -/
def reduceLocalLengthCore : Simp.DSimproc := fun e => do
  let .const name _ := e.getAppFn | return .continue
  unless name == `FormalCircuitBase.localLength ||
      name == `ElaboratedCircuit.localLength do return .continue
  if e.hasLooseBVars || e.hasMVar then return .continue
  if let some k ← try natValOf e catch _ => pure none then
    return .visit (mkNatLit k)
  -- parameterized circuits have symbolic lengths (e.g. `Num2Bits.circuit (n+1)` has
  -- localLength `n+1`); the metadata projection is still a cheap definitional step
  unless (← inferType e).isConstOf `Nat do return .continue
  let w := (← try withDefault <| whnf e catch _ => return .continue).headBeta
  if w == e then return .continue
  let leaked := w.find? fun sub =>
    sub.getAppFn.isConstOf `FormalCircuitBase.localLength ||
    sub.getAppFn.isConstOf `ElaboratedCircuit.localLength ||
    sub.getAppFn.isConstOf `Operations.localLength ||
    sub.getAppFn.isConstOf `Circuit
  if leaked.isSome then return .continue
  return .visit w

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
  -- reduce WITHOUT `addDeclToUnfold`: unfolding via simp generates the constant's
  -- equation lemmas in the current module, and two sibling modules generating them
  -- for the same shared child (e.g. `Xor32.circuit`) collide on import. `deltaExpand`
  -- rewrites the Expr directly; the theorem-free dsimp then reduces the exposed
  -- projections and betas.
  let cfgCtx ← Simp.mkContext
    { zeta := true, beta := true, proj := true, iota := true, instances := true }
    (simpTheorems := #[]) (← Meta.getSimpCongrTheorems)
  let mut w := e
  for _ in [0:4] do
    let allowed := (← collectUnfolds w).push `FormalCircuitBase.output
      |>.push `ElaboratedCircuit.output
    let expanded ← Meta.deltaExpand w (allowed.contains ·)
    let w' := (← Meta.dsimp expanded cfgCtx).1
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

/-- Retype equalities whose type is a reducible Vector alias
(`BLAKE3State := ProvableVector U32 16`): the alias hides the `Vector` head from
every `Eq (Vector …)`-keyed simp lemma (`Vector.ext_iff`, `Vector.mk.injEq`, …), at any
depth in the goal. Definitional, so it is a pure respelling. -/
def retypeVectorAliasEqCore : Simp.DSimproc := fun e => do
  unless e.isAppOfArity ``Eq 3 do return .continue
  let args := e.getAppArgs
  let T := args[0]!
  if T.getAppFn.isConstOf ``Vector then return .continue
  let T' ← withReducible <| whnf T
  unless T'.getAppFn.isConstOf ``Vector do return .continue
  let u ← getLevel T'
  return .visit (mkApp3 (mkConst ``Eq [u]) T' args[1]! args[2]!)

dsimproc_decl retypeVectorAliasEq (_ = _) := retypeVectorAliasEqCore

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
def chainOutputFacts : TacticM Unit := withMainContext do
  try betaReduceGoal catch _ => pure ()
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
            -- environment-clean reduction (no addDeclToUnfold: it generates the
            -- constant's equation lemmas in this module, colliding on import when a
            -- sibling module does the same for a shared child bundle)
            let bundleHeads : List Name :=
              [`FormalCircuitBase, `FormalCircuit, `GeneralFormalCircuit,
               `GeneralFormalCircuit.WithHint, `FormalAssertion, `ElaboratedCircuit]
            let names ← IO.mkRef (#[`FormalCircuitBase.output, `ElaboratedCircuit.output] : Array Name)
            pfx.appArg!.forEach fun sub => do
              let .const c _ := sub | return ()
              let some ci := (← getEnv).find? c | return ()
              if bundleHeads.contains ci.type.getForallBody.getAppFn.constName then
                names.modify (·.push c)
            let allowed ← names.get
            let ctx ← Simp.mkContext
              { zeta := true, beta := true, proj := true, iota := true, instances := true }
              (simpTheorems := #[]) (← getSimpCongrTheorems)
            let w := (← Meta.dsimp (← Meta.deltaExpand app (allowed.contains ·)) ctx).1
            if w == app || w.getAppFn.isConstOf `FormalCircuitBase.output then pure none
            else do
              let eqTy ← mkEq app w
              let prf ← mkExpectedTypeHint (← mkEqRefl app) eqTy
              pure (some (← mkForallFVars vs eqTy, ← mkLambdaFVars vs prf))
        else pure none
      let some (factTy, factPrf) := factData? | return
      let factFVar ← withMainContext do
        let g ← getMainGoal
        let g ← g.assert `o_meta factTy factPrf
        let (fvarId, g) ← g.intro1P
        replaceMainGoal [g]
        pure fvarId
      -- goal only: `at *` would rewrite the fact with itself into `True`
      try
        withMainContext do
          let thms ← (← simpOnlyBase).add (.fvar factFVar) #[] (.fvar factFVar)
          metaSimp (← Simp.mkContext {} (simpTheorems := #[thms]) (← getSimpCongrTheorems))
      catch _ => pure ()
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
    -- re-enter the CURRENT main goal's context: facts chained for earlier outputs
    -- (e.g. the inner output of a nested `RhoPi.output (Theta.output …)`) must be
    -- visible to this step's premises, and the entry-time context predates them
    let step (lemName : Name) : TacticM Unit := withMainContext do
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
              let hA ← mid.withContext do
                let some decl := (← mid.getDecl).lctx.findFromUserName? hAName
                  | throwError "agreement hypothesis vanished"
                pure decl.toExpr
              -- apply the bare constant: the tighter bound is fixed only by conclusion
              -- unification, so the term cannot be pre-built (`mkAppM` rejects open
              -- metavariables); assigning the agreement premise then pins the bound
              let gs ← mid.apply
                (← mkConstWithFreshMVarLevels `ProverEnvironment.agreesBelow_of_le)
              let mut leGoal? := none
              for g in gs do
                let gty ← instantiateMVars (← g.getType)
                if gty.getAppFn.isConstOf `ProverEnvironment.AgreesBelow then
                  g.withContext do
                    unless ← isDefEq gty (← inferType hA) do
                      throwError "agreement hypothesis does not match"
                    g.assign hA
                else if (← inferType gty).isProp then
                  -- the `≤` side condition; apply also lists the bound's own ℕ
                  -- metavariable as a goal, solved by the assignment above
                  leGoal? := some g
              if let some leGoal := leGoal? then
                setGoals [leGoal]
                metaSimp (← Simp.mkContext {} (simpTheorems := #[← simpOnlyBase])
                    (← getSimpCongrTheorems))
                  (← SimprocsArray.add #[] ``reduceLocalLength (post := true))
                unless (← getGoals).isEmpty do Omega.omegaDefault
              else
                setGoals []
            else
              let closed ← try (← getMainGoal).assumption; replaceMainGoal []; pure true
                catch _ => pure false
              unless closed do
                let (cnCtx, cnProcs) ← cnSimp
                try metaSimp cnCtx cnProcs catch _ => pure ()
                metaGrind
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

elab "chain_output_facts" : tactic => chainOutputFacts

partial def splitStep (g : MVarId) (fuel : Nat) : MetaM (List MVarId) := do
  if fuel == 0 then return [g]
  let t := (← instantiateMVars (← g.getType)).consumeMData
  -- child obligations stay whole for the composition rules
  if t.getAppFn.isConstOf `Subcircuit.ComputableWitnesses then return [g]
  -- syntactic head dispatch only: the goal is simp-normalized here, so `And`/`∀`
  -- structure is syntactic, and a defeq-hidden shape is a leaf for the close routes
  -- (unifying against it would symbolically execute still-folded groups)
  if t.isAppOfArity ``And 2 then
    if let some gs ← observing? (g.apply (mkConst ``And.intro)) then
      return ← gs.foldlM (init := []) fun acc g' => do
        return acc ++ (← splitStep g' (fuel - 1))
  if t.isForall then
    if let some (_, g') ← observing? g.intro1P then
      return ← splitStep g' (fuel - 1)
  return [g]

def splitStructure : TacticM Unit :=
  liftMetaTactic fun g => splitStep g 512

/-- Vector route, structural `simp_all` lemmas. -/
def vecStructuralLemmas : Array Name := #[
  ``eval_vector, ``Vector.map_mk, ``List.map_toArray, ``List.map_cons, ``List.map_nil,
  ``Vector.mk.injEq, ``Array.mk.injEq, ``List.cons.injEq, ``and_true,
  ``Vector.map_ofFn, ``Vector.ext_iff, ``Vector.getElem_ofFn, ``Function.comp_def,
  ``Vector.getElem_map, ``Vector.getElem_append, ``Vector.getElem_mapFinRange,
  ``Vector.getElem_mapIdx, ``Vector.getElem_set, ``Vector.getElem_mapRange]

/-- Vector route, goal-only close-hint step lemmas. -/
def closeHintLemmas : Array Name := #[
  ``eval_vector, ``Vector.ext_iff, ``Vector.getElem_set, ``Vector.getElem_ofFn,
  ``Vector.getElem_map, ``Vector.map_ofFn]

/-- Vector route, per-branch (post-`split_ifs`) lemmas. -/
def branchLemmas : Array Name := #[
  ``ProvableType.eval_varFromOffset, ``eval_vector, ``Vector.mapRange_succ,
  ``Vector.mapRange_zero, ``Vector.mk.injEq, ``Array.mk.injEq, ``List.cons.injEq,
  ``and_true, ``Function.comp_apply]

/-- `Vector.ext` fallback route's elementwise lemmas. -/
def extElementLemmas : Array Name := #[
  ``getElem_eval_vector, ``Vector.getElem_map, ``Vector.getElem_append,
  ``Vector.getElem_mapFinRange, ``Vector.getElem_ofFn, ``Vector.getElem_mapIdx]

/-- Simp contexts and simproc arrays for one `computable_witnesses` invocation, built
once by `CwSimp.build` — hints are resolved there, loudly. -/
structure CwSimp where
  /-- Normalization: attribute sets + hints, with the in-scope `main` self-supplied. -/
  normCtx : Simp.Context
  /-- The two attribute sets' simprocs. -/
  normProcs : SimprocsArray
  /-- Attribute sets without hints: the leaf `at *` pass and the base-route
  `simp_all only` fallback. -/
  baseCtx : Simp.Context
  /-- `normProcs` + `reduceOutputMetadata`, for the offset-premise discharge. -/
  dischargeProcs : SimprocsArray
  /-- Vector route, structural `simp_all`. -/
  vecCtx : Simp.Context
  /-- `circuit_norm` procs + `retypeVectorAliasEq` (vector-route steps). -/
  vecProcs : SimprocsArray
  /-- Vector route, goal-only close-hint step (norm + `closing` hints participate). -/
  closeHintCtx : Simp.Context
  /-- Vector route, per-branch simp after `split_ifs`. -/
  branchCtx : Simp.Context
  /-- `circuit_norm` simprocs alone. -/
  cnProcs : SimprocsArray
  /-- `Vector.ext` fallback route's elementwise lemmas. -/
  extCtx : Simp.Context
  /-- Theorem-free context for the standalone output-metadata dsimp step. -/
  dsimpCtx : Simp.Context
  /-- `reduceOutputMetadata` alone, for that step. -/
  outputMetaProcs : SimprocsArray
  /-- Final fallback: default simp set on top of the attribute sets. -/
  fullCtx : Simp.Context
  fullProcs : SimprocsArray

/-- Resolve one hint term: a simp-set name contributes its whole set; a global theorem
is added as a rewrite, a global definition as an unfold (the same paths quoted
`simp [foo]` takes); anything else — local hypotheses included — elaborates as a term.
Unknown names fail here, loudly, instead of silently disabling a downstream call. -/
def addHint (thms : SimpTheorems) (sets : Array SimpTheorems) (t : TSyntax `term) :
    TacticM (SimpTheorems × Array SimpTheorems) := do
  if let `($id:ident) := t then
    if let some ext ← getSimpExtension? id.getId then
      return (thms, sets.push (← ext.getTheorems))
    let declName? ← try pure (some (← resolveGlobalConstNoOverload id))
      catch _ => pure none
    if let some declName := declName? then
      if ← isProp (← getConstInfo declName).type then
        return (← thms.addConst declName, sets)
      else
        return (← thms.addDeclToUnfold declName, sets)
  let e ← Tactic.elabTerm t none
  if let .fvar fvarId := e then
    return (← thms.add (.fvar fvarId) #[] e, sets)
  return (← thms.add (.other (← mkFreshUserName `cw_hint)) #[] e, sets)

/-- Build all simp machinery for one invocation. The in-scope `main` is self-supplied
as an unfold (all resolutions — a constant absent from the goal contributes no
rewrites). `closing` hints participate only in the close routes' goal-only steps, never
in `simp_all`/`at *`/whole-circuit normalization, so recursive eval decompositions
(e.g. `eval_vector_set`) stay affordable. -/
def CwSimp.build (extraTerms closeTerms : Array (TSyntax `term)) : TacticM CwSimp := do
  let cn ← getAttrTheorems `circuit_norm
  let cwn ← getAttrTheorems `computable_witnesses_norm
  let cnProcs : SimprocsArray := #[← getAttrSimprocs `circuit_norm]
  let cwnProcs ← getAttrSimprocs `computable_witnesses_norm
  let mut normHints ← simpOnlyBase
  for mainName in (← try resolveGlobalConst (mkIdent `main) catch _ => pure []) do
    normHints ← normHints.addDeclToUnfold mainName
  let mut hintSets : Array SimpTheorems := #[]
  for t in extraTerms do
    (normHints, hintSets) ← addHint normHints hintSets t
  let mut closeHints := normHints
  let mut closeSets := hintSets
  for t in closeTerms do
    (closeHints, closeSets) ← addHint closeHints closeSets t
  let congr ← getSimpCongrTheorems
  let mut normProcs := cnProcs.push cwnProcs
  for p in [``reduceLocalLength, ``retypeVectorAliasEq] do
    normProcs ← SimprocsArray.add normProcs p (post := true)
  let dischargeProcs ← SimprocsArray.add normProcs ``reduceOutputMetadata (post := true)
  let outputMetaProcs ← SimprocsArray.add #[] ``reduceOutputMetadata (post := true)
  let vecProcs ← SimprocsArray.add cnProcs ``retypeVectorAliasEq (post := true)
  return {
    normCtx := ← Simp.mkContext {}
      (simpTheorems := #[normHints, cn, cwn] ++ hintSets) congr
    normProcs
    baseCtx := ← Simp.mkContext {} (simpTheorems := #[← simpOnlyBase, cn, cwn]) congr
    dischargeProcs
    vecCtx := ← Simp.mkContext {}
      (simpTheorems := #[← theoremsOf vecStructuralLemmas (← simpOnlyBase), cn]) congr
    vecProcs
    closeHintCtx := ← Simp.mkContext {}
      (simpTheorems := #[← theoremsOf closeHintLemmas closeHints, cn] ++ closeSets)
      congr
    branchCtx := ← Simp.mkContext {}
      (simpTheorems := #[← theoremsOf branchLemmas closeHints, cn] ++ closeSets)
      congr
    cnProcs
    extCtx := ← Simp.mkContext {}
      (simpTheorems := #[← theoremsOf extElementLemmas (← simpOnlyBase)]) congr
    dsimpCtx := ← Simp.mkContext {} (simpTheorems := #[]) congr
    outputMetaProcs
    fullCtx := ← Simp.mkContext {}
      (simpTheorems := #[← getSimpTheorems, cn, cwn]) congr
    fullProcs := #[← Simp.getSimprocs] ++ normProcs
  }

/-- The per-leaf dispatch/close stage of `computable_witnesses`, shared by the main
entry (per split leaf) and the standalone `computable_witnesses_close`. -/
def runLeafDispatch (cw : CwSimp) : TacticM Unit := do
  let simpPass : TacticM Unit := do
    unless (← getGoals).isEmpty do
      try metaSimp cw.normCtx cw.normProcs catch _ => pure ()
  -- the window/elementwise route applies to eval-congruence goals: both sides are
  -- eval applications of the same variable term under the two environments (output
  -- windows, child-output metadata, vector states) — recognized by shape, whether
  -- the value type is a vector or a provable struct
  let isEvalCongrEq : TacticM Bool := withMainContext do
    let t := (← instantiateMVars (← getMainTarget)).consumeMData
    -- witness-window / child-output atoms mark eval-congruence territory whatever
    -- the goal's connective shape (equality, conjunction of equalities, …)
    if (t.find? fun e =>
        e.getAppFn.isConstOf `Expression.var ||
        e.getAppFn.isConstOf `ProvableType.varFromOffset ||
        e.getAppFn.isConstOf `FormalCircuitBase.output ||
        e.getAppFn.isConstOf `ElaboratedCircuit.output).isSome then
      return true
    let some (_, lhs, rhs) := t.eq? | return false
    let ty ← instantiateMVars (← inferType lhs)
    let tyW ← withTransparency .instances <| whnf ty
    if tyW.getAppFn.isConstOf ``Vector then return true
    if lhs.isApp && rhs.isApp && lhs.appArg! == rhs.appArg! &&
        (lhs.getAppFn.isConstOf `Eval.eval || lhs.getAppFn.isConstOf `Expression.eval) then
      return true
    return false
  -- Var-typed metadata helper defs tagged `@[computable_witnesses_metadata]`
  -- (`Permutation.stateVar`, `BLAKE3.G.output`, …) block the eval simp lemmas;
  -- delta-expand them in the goal to expose their `varFromOffset` spelling.
  -- Environment-clean (`unfold` would generate the helper's equation lemmas here
  -- and collide with sibling modules doing the same) and shape-agnostic
  -- (conjunction goals included). Opt-in by label: return-type shape cannot
  -- separate safe helpers from spellings the chainer's facts key on.
  let unfoldSharedEvalArgHeads : TacticM Unit := withMainContext do
    let labeledSet ← labelled `computable_witnesses_metadata
    if labeledSet.isEmpty then return
    let ctx ← Simp.mkContext
      { zeta := true, beta := true, proj := true, iota := true, instances := true }
      (simpTheorems := #[]) (← Meta.getSimpCongrTheorems)
    let mut t := (← instantiateMVars (← getMainTarget)).consumeMData
    let mut changed := false
    -- iterate: labeled helpers can be nested inside other labeled helpers
    -- (`Rotation32.output` inside `BLAKE3.G.output`)
    for _ in [0:4] do
      let names ← IO.mkRef (#[] : Array Name)
      t.forEach fun sub => do
        let .const c _ := sub.getAppFn | return ()
        if labeledSet.contains c then
          names.modify fun a => if a.contains c then a else a.push c
      let allowed ← names.get
      if allowed.isEmpty then break
      let expanded ← Meta.deltaExpand t (allowed.contains ·)
      let t' := (← Meta.dsimp expanded ctx).1
      if t' == t then break
      t := t'
      changed := true
    unless changed do return
    liftMetaTactic fun g => do return [← g.change t]
  -- `grind` internalizes every hypothesis and whnf-normalizes its terms; a
  -- `localLength`-equation whose LHS is a raw operations list (e.g. Permutation's 24
  -- rounds) blows the heartbeat budget during that normalization. The equations have
  -- already done their work (offset discharge, AgreesBelow bounds) by close time.
  let clearOpsLengthHyps : TacticM Unit := withMainContext do
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      -- `Operations.forAll`-shaped hypotheses are raw obligations (e.g. induction
      -- hypotheses of recursive circuits): the close cannot use them, but simp_all
      -- and grind normalize/e-match their entire operations list
      let toxic := (← instantiateMVars decl.type).find? fun e =>
        e.getAppFn.isConstOf `Operations.localLength ||
        e.getAppFn.isConstOf `Operations.forAll
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
    -- expose labeled helper metadata before routing: the expansion produces the
    -- `varFromOffset` atoms the route test looks for
    try unfoldSharedEvalArgHeads catch _ => pure ()
    -- witness-window goals are the same expression under the two environments: rewrite
    -- every in-bound `env.get i` to `env'.get i` via the agreement hypothesis (omega
    -- discharges the bound side conditions) so they close by rfl, and mixed goals reach
    -- `grind` with the get-atoms already identified — orders of magnitude cheaper than
    -- letting grind e-match its way through the window arithmetic
    let envUnify : TacticM Unit := do
      unless (← getGoals).isEmpty do
        metaIntrosAll
        let hga? ← withMainContext do
          let mut found : Option (Lean.Ident × Bool) := none
          for decl in ← getLCtx do
            if decl.isImplementationDetail then continue
            let ty ← instantiateMVars decl.type
            if ty.getAppFn.isConstOf `ProverEnvironment.AgreesBelow then
              found := some (mkIdent decl.userName, true)
            else if ty.isAppOfArity ``And 2 then
              -- the unfolded form: (∀ i < b, env.get i = env'.get i) ∧ hint ∧ data
              let l := ty.appFn!.appArg!
              if l.isForall && (l.find? fun e =>
                  e.getAppFn.isConstOf `Environment.get).isSome then
                found := some (mkIdent decl.userName, true)
            else if ty.isForall && (ty.find? fun e =>
                e.getAppFn.isConstOf `Environment.get).isSome then
              found := some (mkIdent decl.userName, false)
          pure found
        if let some (hga, proj) := hga? then
          if proj then
            evalTactic (← `(tactic|
              all_goals (try (simp (disch := omega) only [($hga).1]; try rfl))))
          else
            evalTactic (← `(tactic|
              all_goals (try (simp (disch := omega) only [$hga:ident]; try rfl))))
    let attempt (act : TacticM Unit) : TacticM Bool := do
      let st ← Tactic.saveState
      try act; pure true
      catch _ => st.restore; pure false
    if ← isEvalCongrEq then
      let vecMain : TacticM Unit := do
        metaSimpAll cw.vecCtx cw.vecProcs
        -- user hints goal-only: in the `simp_all` above they would rewrite every
        -- chain-fact hypothesis (all legs' window facts) at every leaf — a
        -- heartbeat blowup for recursive eval decompositions (eval_vector_set)
        unless (← getGoals).isEmpty do
          try metaSimp cw.closeHintCtx cw.vecProcs catch _ => pure ()
        let gs ← getGoals
        for g in gs do
          setGoals [g]
          metaIntros
          evalTactic (← `(tactic| (try split_ifs)))
          let gs2 ← getGoals
          for g2 in gs2 do
            setGoals [g2]
            try metaSimp cw.branchCtx cw.cnProcs catch _ => pure ()
            -- split conjunctions before unifying environments: window conjuncts then
            -- close by rfl inside envUnify, leaving grind only the input-derived parts
            let mut split := []
            for g' in (← getGoals) do
              split := split ++ (← try andIntrosCore g' catch _ => pure [g'])
            setGoals split
            envUnify
            for g' in (← getGoals) do
              setGoals [g']
              metaGrind
        setGoals []
      if ← attempt vecMain then return
      if ← attempt (do
          let [g] ← (← getMainGoal).applyConst ``Vector.ext
            | throwError "Vector.ext: unexpected goals"
          let (_, g) ← g.intro `j
          let (_, g) ← g.intro `hj
          replaceMainGoal [g]
          metaSimp cw.extCtx
          evalTactic (← `(tactic|
            (try split_ifs) <;> grind [Vector.getElem_map, getElem_eval_vector]))) then
        return
      metaGrind
    else
      -- grind first: on already-dispatched leaves it is the cheapest closer by an
      -- order of magnitude; the curated simp_all forms only run when it fails
      -- unify the environments first: legs whose goal is a pure witness-window fact
      -- close by rfl right here, and the rest reach grind with fewer distinct atoms
      envUnify
      if (← getGoals).isEmpty then return
      if ← attempt metaGrind then return
      if ← attempt (do
          metaSimpAll cw.baseCtx cw.normProcs
          unless (← getGoals).isEmpty do throwError "open goals") then return
      metaSimpAll cw.fullCtx cw.fullProcs
      unless (← getGoals).isEmpty do
        throwError "computable_witnesses: could not close goal"
  let leafDispatch : TacticM Unit := withMainContext do
    -- inaccessible hyp names (from intro1P) break the chainer's delab roundtrip
    try replaceMainGoal [← (← getMainGoal).exposeNames] catch _ => pure ()
    -- leaf-local simp (normalizes loop-instantiated lengths), then dispatch
    -- deliberately WITHOUT the user hints: this simp hits `at *`, and close-stage
    -- hints (e.g. recursive eval decompositions like `eval_vector_set`) rewriting
    -- every chain fact in every hypothesis is a heartbeat blowup; hints reach
    -- hypotheses via the close routes' `simp_all` instead
    if (← getGoals).isEmpty then return
    assertLocalLengths
    withMainContext do
      let t := (← instantiateMVars (← getMainTarget)).consumeMData
      let .const headName _ := t.getAppFn | evalCloseRun
      if headName == `Subcircuit.ComputableWitnesses then
        -- offset_eq variants keep the subcircuit's type-index offset separate
        -- from the computability offset: unifying a single-`n` rule against two
        -- defeq-but-differently-spelled offsets makes isDefEq whnf-execute the
        -- operations list (heartbeat blowup on mapFinRange-built circuits). The
        -- `m = n` premise is discharged arithmetically over the asserted lengths.
        -- `WithHint`'s rule takes the input variable explicitly (extra underscore).
        let tryVariant (nm : Name) : TacticM Bool := do
          let st ← Tactic.saveState
          try
            let gs ← (← getMainGoal).apply (← mkConstWithFreshMVarLevels nm)
            -- two premise goals survive unification: the `m = n` offset equation and
            -- the `OnlyAccessedBelow` continuation — identified by shape, not
            -- position (`OnlyAccessedBelow` is only definitionally a `∀`, so the
            -- non-`Eq` goal is the continuation; `intro` unfolds it to a binder)
            let mut offsetGoal? := none
            let mut contGoal? := none
            for g in gs do
              if (← instantiateMVars (← g.getType)).isAppOfArity ``Eq 3 then
                offsetGoal? := some g
              else
                contGoal? := some g
            let some offsetGoal := offsetGoal? | throwError "no offset premise goal"
            let some contGoal := contGoal? | throwError "no continuation goal"
            let (_, contGoal) ← contGoal.intro `h_agrees
            -- offset premise: normalize the length spellings, then close
            -- arithmetically over the asserted lengths
            setGoals [offsetGoal]
            try metaSimp cw.normCtx cw.dischargeProcs catch _ => pure ()
            unless (← getGoals).isEmpty do Omega.omegaDefault
            setGoals [contGoal]
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
        if applied then
          simpPass
          unless (← getGoals).isEmpty do
            try chainOutputFacts catch _ => pure ()
            unless (← getGoals).isEmpty do
              evalCloseRun
        else
          -- no composition rule applied: still normalize before grind — witness IR
          -- and metadata spellings are not grind-reachable in raw form
          simpPass
          unless (← getGoals).isEmpty do
            metaGrind
      else
        try chainOutputFacts catch _ => pure ()
        unless (← getGoals).isEmpty do
          evalCloseRun
  leafDispatch

def runComputableWitnesses (extraTerms closeTerms : Array (TSyntax `term)) : TacticM Unit := do
  let cw ← CwSimp.build extraTerms closeTerms
  -- expose the offset binder before the first simp: rewriting under it makes the whole
  -- pass pay simp's congruence-through-binder overhead (~12% measured). Introducing
  -- `input` as well would save more but drifts the operations spelling away from what
  -- `Circuit.forEach.forAll` keys on (struct-splitting of the free input variable).
  -- Delta-expansion keeps the environment clean (no equation lemmas).
  withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    if t.getAppFn.isConstOf `FormalCircuitBase.ComputableWitnesses then
      let t' ← Meta.deltaExpand t (· == `FormalCircuitBase.ComputableWitnesses)
      unless t' == t do
        liftMetaTactic fun g => do return [← g.change t']
      let (_, g) ← (← getMainGoal).intro `n
      replaceMainGoal [g]
  let simpPass : TacticM Unit := do
    unless (← getGoals).isEmpty do
      try metaSimp cw.normCtx cw.normProcs catch _ => pure ()
  simpPass
  unless (← getGoals).isEmpty do
    -- One boundary rule, mirroring the library's own: plain-`Circuit`-typed constants
    -- are the current circuit's own structure and always unfold; `FormalCircuit`-variant
    -- bundles are proof boundaries and never do (unfolding them destroys the
    -- `c.output`/`toSubcircuit` spellings the composition machinery patterns on, and
    -- leaving a wrapper folded makes And-unification whnf-execute the whole circuit).
    let tBefore ← withMainContext do instantiateMVars (← getMainTarget)
    try unfoldPlainCircuitConsts catch _ => pure ()
    -- re-normalize only if the unfold exposed anything
    let tAfter ← withMainContext do instantiateMVars (← getMainTarget)
    unless tAfter == tBefore do simpPass
  unless (← getGoals).isEmpty do
    metaIntros
  unless (← getGoals).isEmpty do
    let nGoalsBefore := (← getGoals).length
    let hypsBefore ← withMainContext do return (← getLCtx).getFVarIds.size
    -- destructure-only reuse of `provable_struct_simp`: its selection (the CW
    -- obligation has no value-level input variable, so `input`'s only selectable
    -- footprint is `main`'s stuck destructuring match) and field-based naming. Its
    -- alternating simp must not run here (goal is `circuit_norm`-normal, where the
    -- getElem lemmas loop) — the conditional `simpPass` below re-normalizes
    for _ in [0:8] do
      unless ← ProvableStructSimp.destructurePass do break
    -- re-normalize only if a struct variable was destructured
    let changed ← do
      if (← getGoals).isEmpty then pure false
      else if (← getGoals).length != nGoalsBefore then pure true
      else withMainContext do return (← getLCtx).getFVarIds.size != hypsBefore
    if changed then simpPass
  unless (← getGoals).isEmpty do
    -- child-output metadata reduction as its own step: after every normalization
    -- pass (reduced windows drift under further rewriting), directly before the split
    try metaSimp cw.dsimpCtx cw.outputMetaProcs catch _ => pure ()
  unless (← getGoals).isEmpty do
    -- deterministic split to leaves
    splitStructure
    -- per-leaf: cheap normalization + head dispatch
    -- Base close plus one shape-dispatched route: `Vector.ext` is only ever correct on
    -- an equality of vectors, so it is selected by inspecting the goal, not tried
    -- blindly in an alternatives chain.
    let goals ← getGoals
    for g in goals do
      setGoals [g]
      runLeafDispatch cw
    setGoals []

/--
Prove the standard computable-witness obligation. Default tactic for the
`computableWitnesses` field — most gadgets need no field at all. See the module
docstring for the pipeline: normalize (with the in-scope `main` self-supplied as a simp
lemma), destructure inputs, split into per-obligation leaves, then per leaf dispatch the
subcircuit composition rules, chain child-output congruence facts, and close by goal
shape.

Extra simp lemmas may be supplied as `computable_witnesses [lemma₁, lemma₂]` — e.g. a
child bundle name to reduce its `output`/`localLength` metadata when witness expressions
embed the child's output under a binder, where `grind`'s E-matching cannot reach it.

A second hint list `computable_witnesses [..] closing [lemma₁, lemma₂]` participates only
in the close routes' goal-only simp steps, after the goal is split to leaves. Use it for
rewrites that decompose evaluation recursively (`eval_vector_set`, `eval_fromLimbs`-style
lemmas): in the normalization positions those would rewrite every chain-fact hypothesis
or the whole-circuit goal and blow the heartbeat budget.
-/
syntax "computable_witnesses" ("[" term,* "]")? ("closing " "[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| computable_witnesses $[[$terms:term,*]]? $[closing [$closeTerms:term,*]]?) =>
      runComputableWitnesses (terms.map (fun terms => terms.getElems) |>.getD #[])
        (closeTerms.map (fun terms => terms.getElems) |>.getD #[])

/-- Run only the per-leaf dispatch/close stage of `computable_witnesses` on the current
goal: leaf-local normalization, `assert_local_lengths`, subcircuit composition-rule
dispatch, child-output chaining, and the shape-dispatched close routes. For manual
proofs that do the structural decomposition themselves — each machine-closable leg
becomes `computable_witnesses_close`, and only legs needing a bespoke lemma stay
hand-written. Accepts the same two hint lists as `computable_witnesses`. -/
syntax "computable_witnesses_close" ("[" term,* "]")? ("closing " "[" term,* "]")? : tactic

elab_rules : tactic
  | `(tactic| computable_witnesses_close $[[$terms:term,*]]? $[closing [$closeTerms:term,*]]?) => do
      let cw ← CwSimp.build
        (terms.map (fun terms => terms.getElems) |>.getD #[])
        (closeTerms.map (fun terms => terms.getElems) |>.getD #[])
      runLeafDispatch cw

end ComputableWitnesses
