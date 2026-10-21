import Lean.Elab.Tactic
import Clean.Halo2.Subcircuit
import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Halo2.Tactics.CircuitProofStart
import Clean.Halo2.Tactics.AbstractOutputs

/-!
# `circuit_proof_start2` — the atomic-binds proof prefix (CPS v2)

Implements `Clean/Halo2/atomic-binds-design.md`: the peel instantiates every used bind's
continuation at a **do-binder-named atom**, so the proof state mirrors the do-block and
concrete output terms never propagate. Distilled from the v2-manual exemplars
(`Action/{SpendAuthority,AddressIntegrity,ValueCommit}.lean`, commits 378ec475 →
59452517) — the tactic emits exactly those proofs' framework blocks:

- **(a)** intro the config (destructured through products, binder names recovered from
  the `synthesize` pattern-match), enter the `soundness_iff`/`completeness_iff` form
  with the house binder names, split the placed env into `place`/`env`;
- **(b)** `dsimp only [] at *` (iota-reduces the destructured-config matches), then land
  `output_eq` on the raw do-block output via `ElaboratedCircuit.output_eq`;
- **(c)** per bind, one block — THE IN-PEEL ENGINE (design doc, "The in-peel engine
  (subcircuit rewriting v2)"): single `operations_bind` peel (`constraints_append` at
  `constraints`, plus `extendsWitnesses_append` at `witnesses` and the goal's
  constraints side in the completeness direction), `output_bind` at `output_eq`, split
  off the chunk as `<name>_spec` (call binds) / `region_<k>` (raw binds), canonicalize
  the output spelling (`output_call'`), mint the atom by
  `generalize <name>_eq : <canonical output> = <name>` under a
  `revert constraints output_eq` — BEFORE the continuation's occurrences diverge — and
  fold the offsets (`nextRegionIndex_call` + the `foldCallRegionCount` simproc). Then
  the bind's chunk CONVERTS in the same block, by direct term application of the
  `SubcircuitRw` leaf lemmas at arguments in hand — no post-pass, no re-matching:
  * a CALL chunk weakens in place to the child's `EnvA → A → Spec` (soundness), or
    strengthens the goal's just-split conjunct to `EnvA ∧ A ∧ PA` and asserts the
    derived `<name>_spec : EnvA → A → PA → Spec ∧ ProverSpec`, consuming the witness
    chunk (completeness); the `wit_<name>` extract atoms mint from the contract;
  * a RAW chunk splits STRUCTURALLY first (the `chunk_split` constructor set,
    `Clean/Halo2/Attributes.lean` — leaves stay pristine), embedded and ∀-bound
    `.call` chunks convert at ground truth (loop families under the binder, the
    round-`i` witness CONSTRUCTED from the bind's own witness chunk, never located),
    and the remainder opens with `circuit_norm`;
  * failure semantics are HARD (maintainer ruling): a call the peel uncovered that
    cannot convert is an error naming the bind — never a silently-raw chunk;
- **(d)** terminal `pure`: close the op list, land `output_eq` on the final atom; a
  terminal REAL step gets the same per-bind conversion block (`out_spec`);
- **(f)** landing (maintainer model, AddressIntegrity 90912413): `provable_type_simp`
  decomposes types into the components that actually occur; normalize ONLY the
  rule-sources `input_eq`/`output_eq` (so their equations fire on normalized spellings);
  then ONE pass over every other hypothesis and the goal that uses
  `input_eq` and `output_eq` themselves AS REWRITE RULES — `output_eq` firing
  left-to-right (circuit spelling → declared output) — together with the CALLER'S
  LEMMA LIST (`circuit_proof_start2 [<child bridges, Spec/Assumptions unfolds>]`).
  With a complete list, trivially-composing parents close by `simp_all`/`grind`;
- **(g)** the no-call-left-behind scan: post-landing, any surviving call-keyed
  constraint chunk (a shape the structural set does not cover) is a hard error.

Known gaps: raw binds whose value IS used mint no atom yet (none in the sample); the
atom mint hard-errors on the dependent-occurrence `generalize` failure (Merkle
HashLayer, not yet on cps2) — its occurrence-filtered root fix is the one deferred item.
-/

open Lean Elab Tactic Meta

namespace Halo2

initialize registerTraceClass `Halo2.circuit_proof_start2

namespace CircuitProofStart2

open CircuitProofStart (bestEffort)

/-- Run a tactic given by syntax, best-effort; degraded steps are traced
(`set_option trace.Halo2.circuit_proof_start2 true`). -/
def run? (stx : TSyntax `tactic) : TacticM Unit := do
  let s ← saveState
  try evalTactic stx
  catch e =>
    trace[Halo2.circuit_proof_start2] "step degraded: {stx}\n{e.toMessageData}"
    s.restore

/-- The current type of the hypothesis named `n` (instantiated), or `none`. -/
def hypType? (n : Name) : TacticM (Option Expr) := withMainContext do
  let some decl := (← getLCtx).findFromUserName? n | return none
  instantiateMVars decl.type

/-- From a layouter `Constraints place env ((body).operations i) i` /
`ExtendsWitnesses place env ((body).operations i) i` type (ops second-to-last), or a
region `RegionOperations.Constraints place self env ((body).operations self)` /
`.ExtendsWitnesses …` type (ops last), the `body` circuit term. -/
def bodyOfChunkType? (ty : Expr) : Option Expr := do
  let args := ty.getAppArgs
  guard (args.size ≥ 2)
  let pick (ops : Expr) : Option Expr := do
    if ops.isAppOfArity ``Halo2.Circuit.operations 5 then return ops.getArg! 3
    else if ops.isAppOfArity ``Halo2.RegionCircuit.operations 5 then return ops.getArg! 3
    else none
  pick args[args.size - 2]! <|> pick args[args.size - 1]!

/-- Decompose a monadic bind application: `(x >>= f)` → `(x, f)`. -/
def bindParts? (body : Expr) : Option (Expr × Expr) :=
  if body.isAppOf ``Bind.bind then
    let args := body.getAppArgs
    if args.size ≥ 2 then some (args[args.size - 2]!, args[args.size - 1]!) else none
  else none

/-- The do-binder name for a bind: the continuation lambda's binder, with leading
underscores stripped (`_lp` → `lp`). For a hygienic/anonymous binder on a call bind
(H's review note #5, "Chain's slot") the name is pinned: `out` when the continuation
is a terminal `pure` (the call discards its output — `let _ ← X.call …; pure ()`),
otherwise the called bundle's base name (`loop` for `(loop n w).call …`). -/
def binderNameOf (x f : Expr) : Name :=
  let stem : Option Name :=
    match f with
    | .lam n .. =>
      if n.hasMacroScopes then none
      else
        let s := n.toString
        if s.startsWith "_" then
          let t := s.dropWhile (· == '_') |>.toString
          if t.isEmpty then none else some (Name.mkSimple t)
        else some n
    | _ => none
  stem.getD (if isCall x && contIsPure f then `out else calleeName x)
where
  /-- Whether `x` is a `.call` application. -/
  isCall (x : Expr) : Bool :=
    x.isAppOf ``Halo2.FormalCircuit.call || x.isAppOf ``Halo2.FormalRegionCircuit.call
  /-- Whether the continuation body is a terminal `pure` (nothing after this bind). -/
  contIsPure (f : Expr) : Bool :=
    match f with
    | .lam _ _ b _ => b.consumeMData.isAppOf ``Pure.pure
    | _ => false
  /-- The called bundle's base name: the `child` argument of `.call` — 4th-from-last
  for a region call (`child config offset input`), 3rd-from-last for a layouter call
  (`child config input`); `x` as the last resort for a non-call bind. -/
  calleeName (x : Expr) : Name :=
    let args := x.getAppArgs
    let child? : Option Expr :=
      if x.isAppOf ``Halo2.FormalRegionCircuit.call && args.size ≥ 4 then
        some args[args.size - 4]!
      else if x.isAppOf ``Halo2.FormalCircuit.call && args.size ≥ 3 then
        some args[args.size - 3]!
      else none
    match child? with
    | some c => match c.getAppFn.constName? with
      | some n => Name.mkSimple n.getString!
      | none => `x
    | none => `x

/-- Whether the continuation actually uses its binder. -/
def binderUsed (f : Expr) : Bool :=
  match f with
  | .lam _ _ b _ => b.hasLooseBVar 0
  | _ => true

/-- Collect the closed canonical-output subterms of `e` not already equal to a local
atom (reuses the AbstractOutputs collector, filtered to `FormalCircuit.output` /
`FormalRegionCircuit.output` heads). -/
def newCanonicalOutputs (e : Expr) : TacticM (Array Expr) := withMainContext do
  let (_, outs) ← (AbstractOutputs.collectOutputs e).run #[]
  let mut fresh := #[]
  for o in outs do
    if AbstractOutputs.isCanonicalOutput o then
      -- skip if some hypothesis already defines this output as an atom
      if (← SubcircuitRw.findOutputLocal? o).isNone then
        fresh := fresh.push o
  return fresh

/-- Mint atoms for `outs` (innermost-first) with base name `n` (numbered `n`, `n_2`, …
on collisions/multiples): revert `hyps`, generalize, re-intro `hyps` in the SAME order.
The defining equations are named `h_<atom>`. -/
def mintAtoms (outs : Array Expr) (n : Name) (hyps : Array Name) :
    TacticM (Array (Name × Name)) := do
  if outs.isEmpty then return #[]
  -- revert the carrier hypotheses (they hold the occurrences); reverse order so the
  -- FIRST listed hyp ends up outermost, matching the re-intro order below
  for h in hyps.reverse do
    run? (← `(tactic| revert $(mkIdent h):ident))
  let minted ← withMainContext do
    let mut args : Array GeneralizeArg := #[]
    let mut minted : Array (Name × Name) := #[]
    let lctx ← getLCtx
    let mut k := 0
    for o in outs do
      let base := if k == 0 then n else Name.mkSimple s!"{n}_{k+1}"
      let xn := if lctx.findFromUserName? base |>.isSome then
        Name.mkSimple s!"{base}'" else base
      let hn := Name.mkSimple s!"{xn}_eq"
      args := args.push { expr := o, xName? := xn, hName? := hn }
      minted := minted.push (xn, hn)
      k := k + 1
    let g ← getMainGoal
    -- HARD by default (maintainer ruling — no silent skips): a dependent occurrence
    -- can make `generalize`'s all-occurrences motive type-incorrect (known repro:
    -- Merkle HashLayer's hash-output binder). No landed cps2 proof hits this today;
    -- when one does, this surfaces loudly and gets the occurrence-filtered mint fix
    -- at the root rather than a silent concrete-spelling fallback.
    let (_, g') ← try g.generalize args catch e =>
      throwError "circuit_proof_start2: minting `{n}` failed — the abstracted motive \
        is not type correct (a dependent occurrence of the output term){indentD e.toMessageData}"
    replaceMainGoal [g']
    pure minted
  -- re-intro in list order (first listed = outermost binder)
  for h in hyps do
    run? (← `(tactic| intro $(mkIdent h):ident))
  return minted

/-- Subterms `Circuit.output x' i` / `RegionCircuit.output x' i` of `e` whose circuit
`x'` is (syntactically) the raw step `x` just peeled — the raw-bind analogue of the
canonical call outputs. Collected BEFORE any reduction so every occurrence still shares
the one spelling. -/
partial def rawOutputsOf (x : Expr) (e : Expr) : Array Expr :=
  go e #[]
where
  go (e : Expr) (acc : Array Expr) : Array Expr :=
    let isRawOut :=
      (e.isAppOfArity ``Halo2.Circuit.output 5 || e.isAppOfArity ``Halo2.RegionCircuit.output 5)
        && e.getArg! 3 == x
    let acc := if isRawOut then (if acc.contains e then acc else acc.push e) else acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ d b _ => go b (go d acc)
    | .forallE _ d b _ => go b (go d acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ b => go b acc
    | _ => acc

/-- The TYPE-directed mint gate (see the design doc's "Raw binds, loops, and the mint
gate"): a used binder mints iff its value is CELL-VALUED — the spellings that
metastasize through continuations. Index-valued binders (`currentRegion`'s
`RegionIndex`, ℕ) must stay literal for the region-count folding; Unit-valued ones
carry nothing. Everything else (cells, `Var` records, vectors of cells) mints. -/
def binderTypeMints (f : Expr) : TacticM Bool := do
  let .lam _ d _ _ := f | return false
  let d ← withTransparency .instances <| whnf (← instantiateMVars d)
  let head := d.getAppFn.constName?
  -- the ONE principled exclusion: index-valued binders must stay literal for the
  -- region-count folding. Everything else that is used mints — the defining equation
  -- reconstructs the concrete spelling wherever a proof needs it.
  return !(head == some ``Nat || head == some ``Halo2.RegionIndex
    || head == some ``Unit || head == some ``PUnit || head == some ``Int)

/-- Fully-applied `FormalCircuit.extract`/`FormalRegionCircuit.extract` subterms of `e`
(closed, no loose bvars — ∀-bound loop contracts are skipped: `generalize` cannot
abstract open terms). The extract-side analogue of the canonical call outputs (design
doc: "the extract value gets the same treatment — `wit_<binder>` atom"). -/
partial def extractTermsOf (e : Expr) : Array Expr :=
  go e #[]
where
  go (e : Expr) (acc : Array Expr) : Array Expr :=
    let isExtract :=
      (e.isAppOfArity ``Halo2.FormalCircuit.extract 13
        || e.isAppOfArity ``Halo2.FormalRegionCircuit.extract 14)
      && !e.hasLooseBVars
    let acc := if isExtract then (if acc.contains e then acc else acc.push e) else acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ d b _ => go b (go d acc)
    | .forallE _ d b _ => go b (go d acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b => go b acc
    | .proj _ _ b => go b acc
    | _ => acc

/-- Mint `wit_<binder>` atoms for the child-extract terms appearing in hypothesis
`src` (the just-converted contract speaks the child's extract). Skips Unit-like
witnesses. The defining equations reduce in the landing pass via the child's
`_extract_eq` bridge, landing them on the concrete extract spelling. -/
def mintExtracts (src : Name) (binder : Name) : TacticM (Array Name) := do
  let some ty ← hypType? src | return #[]
  let mut outs : Array Expr := #[]
  for e in extractTermsOf ty do
    let wty ← withTransparency .instances <| whnf (← instantiateMVars (← inferType e))
    let whead := wty.getAppFn.constName?
    unless whead == some ``Unit || whead == some ``PUnit do
      outs := outs.push e
  return (← mintAtoms outs (Name.mkSimple s!"wit_{binder}") #[src]).map (·.2)

/-- Split the witness-side chunk hypothesis into its conjunct leaves — the scoped
witness sources the completeness conversion draws from. Each source is a
`(proof, type)` pair built by `And.left/right` projection; no context scan ever
happens (the in-peel engine's ground-truth discipline). -/
partial def shatterSources (proof ty : Expr) (acc : Array (Expr × Expr)) :
    MetaM (Array (Expr × Expr)) := do
  let ty := ty.consumeMData
  match ty.and? with
  | some (a, b) =>
    let acc ← shatterSources (← mkAppM ``And.left #[proof]) a acc
    shatterSources (← mkAppM ``And.right #[proof]) b acc
  | none => return acc.push (proof, ty)

/-- The scoped completeness walker (the in-peel engine's goal side). Walks goal
proposition `p` in positive polarity; every call-keyed constraint chunk is
strengthened in place to its `EnvA ∧ A ∧ PA` precondition bundle, with the witness
fact taken from `sources` — the shattered conjuncts of THIS bind's witness chunk,
augmented under each ∀ binder by instantiating ∀-typed sources at the goal's own
binder (which is how loop families convert under the binder: the round-`i` witness
is `source i`, constructed, never located). Returns `(some (p', proof : p' → p))`
with the derived contract statements — already abstracted over any binders between
them and the top (loop families come out as `∀ i, EnvA i → A i → PA i → Spec i ∧
ProverSpec i`) — or `(none, #[])` if `p` contains no call-keyed chunk.

Failure semantics are HARD (maintainer ruling): a matched chunk with no source
counterpart, or a failing leaf instantiation, is an error naming the chunk — there
is no silently-unconverted outcome for a chunk the walk can see. -/
partial def walkGoalScoped (p : Expr) (sources : Array (Expr × Expr)) :
    TacticM (Option (Expr × Expr) × Array (Name × Expr × Expr)) := do
  let p := (← instantiateMVars p).consumeMData
  -- Leaf: a call-keyed constraint chunk. Its witness MUST be among the sources.
  if let some c ← SubcircuitRw.matchChunk? p then
    -- source lookup: reducible pass first (identical spellings — the common case),
    -- then a default-transparency pass on the SAME tiny scoped set — the goal side
    -- can spell a region index `i₀ + regionCount …` (constraints_append) where the
    -- witness side spells `(step …).nextRegionIndex i₀` (operations_bind); those are
    -- defeq, not reducibly so. No storm risk: the candidates are this bind's own
    -- witness conjuncts, child/config compare stays fail-fast.
    -- single REDUCIBLE pass, `useOpsIdx`: the ops-index compare is uniform across the
    -- goal and witness sides, so witness matching needs no relaxed-transparency retry.
    let mut found : Option (Expr × Expr) := none
    for s in sources do
      if ← SubcircuitRw.witnessMatches? c s.2 (useOpsIdx := true) then
        found := some s
        break
    let some (witProof, witTy) := found
      -- no counterpart among THIS bind's sources: a later bind's chunk, pre-split by
      -- the goal-side structural pass at region level — its own peel turn converts
      -- it. A genuine miss is caught by the post-landing no-call-left-behind scan.
      | do trace[Halo2.circuit_proof_start2] "scoped walk: no source for chunk, skipping"
           return (none, #[])
    -- emit the contract at the OPS-index (defeq to the `Constraints` region-arg, but
    -- the spelling the minted output atom carries), so the child's `.output …` in the
    -- derived statement lands on the atom REDUCIBLY — no relaxed-transparency pass.
    let c := { c with regionIdx := c.opsIdx }
    let some (bundle, strengthenProof) ← SubcircuitRw.completenessLeaf? c p witProof witTy
      | throwError "circuit_proof_start2: the completeness strengthening leaf failed \
          to instantiate at chunk:{indentExpr p}"
    let some (dTy, dProof) ← SubcircuitRw.derivedStatement c witProof witTy
      | throwError "circuit_proof_start2: the derived contract statement failed to \
          instantiate at chunk:{indentExpr p}"
    -- suggested name: the child bundle's base name (`round_spec` for a loop over
    -- `round` — H's naming rule: child-derived for embedded/loop conversions)
    let base := match c.child.getAppFn.constName? with
      | some n => Name.mkSimple n.getString!
      | none => `out
    return (some (bundle, strengthenProof), #[(base, dTy, dProof)])
  match p.and? with
  | some (a, b) =>
    let (ra, da) ← walkGoalScoped a sources
    let (rb, db) ← walkGoalScoped b sources
    match ra, rb with
    | none, none => return (none, #[])
    | _, _ =>
      let (a', pa) := ra.getD (a, ← identProof a)
      let (b', pb) := rb.getD (b, ← identProof b)
      return (some (← mkAppM ``And #[a', b'],
        ← mkAppM ``SubcircuitRw.and_mono #[pa, pb]), da ++ db)
  | none =>
  match SubcircuitRw.or? p with
  | some (a, b) =>
    let (ra, da) ← walkGoalScoped a sources
    let (rb, db) ← walkGoalScoped b sources
    match ra, rb with
    | none, none => return (none, #[])
    | _, _ =>
      let (a', pa) := ra.getD (a, ← identProof a)
      let (b', pb) := rb.getD (b, ← identProof b)
      return (some (← mkAppM ``Or #[a', b'],
        ← mkAppM ``SubcircuitRw.or_mono #[pa, pb]), da ++ db)
  | none =>
  if p.isArrow then
    let a := p.bindingDomain!
    let b := p.bindingBody!
    let (rb, db) ← walkGoalScoped b sources
    match rb with
    | none => return (none, #[])
    | some (b', pb) =>
      return (some (← mkArrow a b',
        ← mkAppM ``SubcircuitRw.imp_mono #[← identProof a, pb]), db)
  else if p.isForall then
    forallBoundedTelescope p (some 1) fun xs body => do
      let #[x] := xs | return (none, #[])
      -- augment: every ∀-typed source whose domain matches the goal binder yields
      -- its instantiation at that binder (shattered further through ∧)
      let mut srcs := sources
      for s in sources do
        if s.2.isForall then
          if ← withTransparency .reducible <| isDefEq s.2.bindingDomain! (← inferType x) then
            srcs ← shatterSources (mkApp s.1 x) (s.2.bindingBody!.instantiate1 x) srcs
      let (rb, db) ← walkGoalScoped body srcs
      -- abstract the derived statements over the binder where they mention it
      let db' ← db.mapM fun (base, ty, proof) => do
        if ty.containsFVar x.fvarId! || proof.containsFVar x.fvarId! then
          return (base, ← mkForallFVars #[x] ty, ← mkLambdaFVars #[x] proof)
        return (base, ty, proof)
      match rb with
      | none => return (none, db')
      | some (body', pbody) =>
        let motiveOld ← mkLambdaFVars #[x] body
        let motiveNew ← mkLambdaFVars #[x] body'
        let hfun ← mkLambdaFVars #[x] pbody
        let proof ← mkAppOptM ``SubcircuitRw.forall_mono
          #[← inferType x, motiveNew, motiveOld, hfun]
        return (some (← mkForallFVars #[x] body', proof), db')
  else
    return (none, #[])
where
  identProof (p : Expr) : MetaM Expr := do
    withLocalDeclD `h p fun h => mkLambdaFVars #[h] h

/-- In-peel completeness conversion at one bind (the in-peel engine's goal side):
walk the goal with `walkGoalScoped`, sources = the shattered witness chunk
`witChunk`; strengthen the goal in place; assert each derived contract as
`<binder>_spec` (primes on collision); mint the `wit_<binder>` extract atoms from
the closed derived contracts. `required` (call binds): zero conversions is a hard
error — the peel uncovered a `.call`, so the goal MUST convert. The witness chunk
is cleared when consumed (always for call binds; for raw chunks, when it held
nothing but call witnesses). Returns the minted wit-equation names. -/
def convertGoalScoped (binder : Name) (witChunk : Name) (required : Bool) :
    TacticM (Array Name) := withMainContext do
  let some decl := (← getLCtx).findFromUserName? witChunk
    | if required then
        throwError "circuit_proof_start2: call bind '{binder}': witness chunk \
          {witChunk} vanished before conversion"
      else return #[]
  let witTy ← instantiateMVars decl.type
  let sources ← shatterSources (.fvar decl.fvarId) witTy #[]
  let goalMVar ← getMainGoal
  let target ← instantiateMVars (← goalMVar.getType)
  let (res, derived) ← walkGoalScoped target sources
  match res with
  | none =>
    if required then
      throwError "circuit_proof_start2: call bind '{binder}': the goal contains no \
        constraint chunk matching the call — nothing to convert"
    return #[]
  | some (newGoal, proof) =>
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newGoal (tag := `strengthened)
    goalMVar.assign (mkApp proof newMVar)
    let mut g := newMVar.mvarId!
    let mut names : Array Name := #[]
    -- name the derived contracts `<binder>_spec` (call binds: the do-binder; raw
    -- binds: the walker's child-derived base — `round_spec` for a loop over
    -- `round`), priming on collision; the witness chunk's own name does not count
    -- (call binds: the contract REPLACES it)
    let taken ← g.withContext do
      let mut t : Array Name := #[]
      for d in ← getLCtx do
        unless d.isImplementationDetail || d.fvarId == decl.fvarId do
          t := t.push d.userName
      pure t
    for (childBase, dTy, dProof) in derived do
      let base := if required then s!"{binder}_spec" else s!"{childBase.getString!}_spec"
      let mut nm := Name.mkSimple base
      while taken.contains nm || names.contains nm do
        nm := Name.mkSimple (nm.getString! ++ "'")
      let g' ← g.assert nm (← instantiateMVars dTy) (← instantiateMVars dProof)
      let (_, g'') ← g'.intro1P
      g := g''
      names := names.push nm
    -- clear the consumed witness chunk — CALL binds only: the derived contract
    -- replaces it. Raw chunks always keep theirs, even ∀-call-families: loop
    -- parents legitimately open the call boundary per round to recover the raw
    -- witness equations that build their honest-value chains (MulIncomplete's
    -- `hsteps`), and the derived family's PA premises need exactly those.
    if required then
      g ← g.tryClearMany #[decl.fvarId]
    replaceMainGoal [g]
    let mut witEqs : Array Name := #[]
    for nm in names do
      witEqs := witEqs ++ (← mintExtracts nm binder)
    return witEqs

/-- In-peel soundness conversion of a call bind's chunk (the in-peel engine,
`atomic-binds-design.md`): the chunk hypothesis IS the call-keyed constraint chunk —
read the contract arguments off it, weaken it in place to the child's
`EnvAssumptions → Assumptions → Spec` via the soundness leaf, then mint the
`wit_<binder>` extract atoms from the converted contract. No search, no miss modes:
a failure here is a HARD error naming the bind (maintainer ruling — soft degradation
breeds silently-raw chunks). Returns the minted wit-equation names. -/
def convertCallChunkSound (chunkName binder : Name) : TacticM (Array Name) := do
  withMainContext do
    let some decl := (← getLCtx).findFromUserName? chunkName
      | throwError "circuit_proof_start2: call bind '{binder}': \
          chunk hypothesis {chunkName} vanished before conversion"
    let ty ← instantiateMVars decl.type
    let some c ← SubcircuitRw.matchChunk? ty
      | throwError "circuit_proof_start2: call bind '{binder}': chunk is not a \
          call-keyed constraint chunk:{indentExpr ty}"
    -- emit the contract at the OPS-index (defeq to the `Constraints` region-arg, but
    -- the spelling the minted output atom carries), so the child's `.output …` in the
    -- weakened chunk lands on the atom REDUCIBLY — no relaxed-transparency output pass.
    let c := { c with regionIdx := c.opsIdx }
    let some (concl, proof) ← SubcircuitRw.soundnessLeaf? c ty
      | throwError "circuit_proof_start2: call bind '{binder}': the soundness leaf \
          failed to instantiate (child {indentExpr c.child}\n) at chunk:{indentExpr ty}"
    let goal ← getMainGoal
    let hExpr := mkApp proof (.fvar decl.fvarId)
    let (_, goal') ← (← goal.assert chunkName concl hExpr).intro1P
    let goal' ← goal'.tryClearMany #[decl.fvarId]
    replaceMainGoal [goal']
  mintExtracts chunkName binder

/-- One per-bind block. `sound := true` for the soundness direction; `region := true`
for region-level bundles (region append lemmas, no offset folding). Returns `none`
when the chunk hypothesis no longer holds a bind (terminal reached); otherwise the
chunk name, whether it was a call bind, and the wit-atom equations minted by the
in-peel conversion. -/
def peelOneBind (sound region : Bool) (chunkHyp : Name) (regionIdx : Nat)
    (unfolds : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM (Option (Name × Bool × Array Name)) := do
  let ty? ← hypType? chunkHyp
  let some ty := ty? | do
    trace[Halo2.circuit_proof_start2] "peel stop: no hyp {chunkHyp}"
    return none
  let some body := bodyOfChunkType? ty | do
    let opsHead := if _h : ty.getAppArgs.size ≥ 2 then
      toString (ty.getAppArgs[ty.getAppArgs.size-2]!.getAppFn.constName?) else "-"
    trace[Halo2.circuit_proof_start2]
      "peel stop: head={ty.getAppFn}, nargs={ty.getAppArgs.size}, opsHead={opsHead}"
    return none
  let some (x, f) := bindParts? body | do
    trace[Halo2.circuit_proof_start2] "peel stop: not a bind {body.getAppFn}"
    return none
  let nm := binderNameOf x f
  let isCall := x.isAppOf ``Halo2.FormalCircuit.call
    || x.isAppOf ``Halo2.FormalRegionCircuit.call
  -- loop-combinator steps (registry heads) are atomic raw steps: never spine-split —
  -- they are single application nodes, and the registry keeps them out of the
  -- auto-unfolds (the actual protection); their chunks share the raw `region_<k>`
  -- naming and their rounds split via the canonical tagged lemmas at raw-open time
  let chunkName := if isCall then Name.mkSimple s!"{nm}_spec"
    else Name.mkSimple s!"region_{regionIdx}"
  -- peel the constraint/witness/goal sides + the output side
  if region then
    if sound then
      run? (← `(tactic| rw [RegionCircuit.operations_bind,
        RegionOperations.constraints_append] at $(mkIdent chunkHyp):ident))
    else
      run? (← `(tactic| rw [RegionCircuit.operations_bind,
        RegionOperations.extendsWitnesses_append] at $(mkIdent chunkHyp):ident))
      run? (← `(tactic| rw [RegionCircuit.operations_bind,
        RegionOperations.constraints_append]))
    run? (← `(tactic| rw [RegionCircuit.output_bind] at $(mkIdent `output_eq):ident))
  else if sound then
    run? (← `(tactic| rw [Circuit.operations_bind, constraints_append]
      at $(mkIdent chunkHyp):ident))
    run? (← `(tactic| rw [Circuit.output_bind] at $(mkIdent `output_eq):ident))
  else
    run? (← `(tactic| rw [Circuit.operations_bind, extendsWitnesses_append]
      at $(mkIdent chunkHyp):ident))
    run? (← `(tactic| rw [Circuit.operations_bind, constraints_append]))
    run? (← `(tactic| rw [Circuit.output_bind] at $(mkIdent `output_eq):ident))
  run? (← `(tactic| obtain ⟨$(mkIdent chunkName):ident, $(mkIdent chunkHyp):ident⟩
    := $(mkIdent chunkHyp):ident))
  -- canonicalize output spellings, then mint the atom for a used binder
  let canon : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ←
    if region then
      #[``FormalRegionCircuit.output_call, ``FormalRegionCircuit.output_call'].mapM
        fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
    else
      #[``FormalCircuit.output_call'].mapM
        fun n => `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
  if sound then
    run? (← `(tactic| simp only [$canon,*]
      at $(mkIdent chunkHyp):ident $(mkIdent `output_eq):ident))
  else
    run? (← `(tactic| simp only [$canon,*]
      at $(mkIdent chunkHyp):ident $(mkIdent `output_eq):ident ⊢))
  if isCall && binderUsed f then
    if let some ty' ← hypType? chunkHyp then
      let outs ← newCanonicalOutputs ty'
      discard <| mintAtoms outs nm #[chunkHyp, `output_eq]
  -- a LAYOUTER-level raw or loop bind whose value passes the TYPE gate mints too
  -- (design doc, "Raw binds, loops, and the mint gate": mint iff no consumer rebinds
  -- the output by concrete address — at the layouter level every consumer is
  -- opacity-respecting, while region gates address cells by (column, rotation), so
  -- region raw binds keep their concrete spellings; value-level region atoms are
  -- CPS3, issue #428): collect the still-shared `(x).output i` spelling, generalize
  -- it to the do-binder name, and reduce ONLY the defining equation to its concrete
  -- boundary fact (for loops: the closed-form output via the tagged loop lemmas) —
  -- the continuation keeps the atom. Index-valued binders (`currentRegion`) never
  -- mint: their arithmetic must stay literal for the folds.
  if !region && !isCall && binderUsed f then
    if ← binderTypeMints f then
      let mut outs : Array Expr := #[]
      if let some tyC ← hypType? chunkHyp then
        outs := outs ++ rawOutputsOf x tyC
      if let some tyO ← hypType? `output_eq then
        for o in rawOutputsOf x tyO do
          if !outs.contains o then outs := outs.push o
      let minted ← mintAtoms outs nm #[chunkHyp, `output_eq]
      for (_, hn) in minted do
        run? (← `(tactic| simp only [circuit_norm, $unfolds,*] at $(mkIdent hn):ident))
  -- fold the offsets (layouter only; region binds share one region index). The fold
  -- set covers EVERY preceding-step kind, not just `.call`: a raw `assignRegion`/
  -- `loadTable` step's `operations`/`nextRegionIndex` must reduce here too, on BOTH
  -- the witness chunk and the goal, so the region INDEX of the split-off chunk lands
  -- in one spelling on both sides. Otherwise the goal side (whose prior raw bind's
  -- `chunk_split` already unfolded `(assignRegion …).operations`) and the witness side
  -- (untouched) diverge — `i₀ + regionCount [Operation.region …]` vs
  -- `i₀ + regionCount ((assignRegion …).operations i₀)` — defeq but not reducibly, the
  -- residue that used to force a relaxed-transparency compare. Region counts of raw
  -- steps stay symbolic (they collapse to literals in landing); we only converge the
  -- `operations`/`nextRegionIndex` spelling.
  unless region do
    if sound then
      run? (← `(tactic| simp only [FormalCircuit.nextRegionIndex_call, foldCallRegionCount]
        at $(mkIdent chunkHyp):ident $(mkIdent `output_eq):ident))
    else
      run? (← `(tactic| simp only [FormalCircuit.nextRegionIndex_call, foldCallRegionCount]
        at $(mkIdent chunkHyp):ident $(mkIdent `output_eq):ident ⊢))
  -- ── in-peel engine: a call chunk converts to its contract HERE, with every
  -- argument in hand — no post-pass re-matching (design doc, "The in-peel engine").
  -- Soundness weakens the chunk hypothesis in place; completeness strengthens the
  -- goal's just-split conjunct to `EnvA ∧ A ∧ PA` and asserts the derived
  -- `<binder>_spec`, consuming the witness chunk. The `wit_<binder>` extract atoms
  -- mint from the converted contract in the same block. Failures are hard errors
  -- (maintainer ruling). ──
  if isCall then
    let witEqs ←
      if sound then convertCallChunkSound chunkName nm
      else convertGoalScoped nm chunkName (required := true)
    return some (chunkName, isCall, witEqs)
  -- ── raw (non-call) chunks: STRUCTURAL split first (`chunk_split` — constructor
  -- lemmas only, so leaves and especially embedded `.call` boundaries keep their
  -- pristine spellings), then in-peel conversion of any embedded or ∀-bound call
  -- chunks (inlined region calls, loop combinators over child bundles) at ground
  -- truth, then the remainder opens with `circuit_norm` (gates land as before;
  -- content-free chunks vanish) ──
  run? (← `(tactic| simp only [chunk_split] at $(mkIdent chunkName):ident))
  let mut rawWitEqs : Array Name := #[]
  unless sound do
    -- goal side (completeness): the same structural set, then the scoped conversion
    -- against the just-split witness chunk — BEFORE the circuit_norm open, so both
    -- sides still share the pristine spellings
    run? (← `(tactic| simp only [chunk_split]))
    rawWitEqs ← convertGoalScoped nm chunkName (required := false)
  run? (← `(tactic| simp only [circuit_norm, $unfolds,*] at $(mkIdent chunkName):ident))
  let cleared ← withMainContext do
    let some decl := (← getLCtx).findFromUserName? chunkName | return true
    if (← instantiateMVars decl.type).isConstOf ``True then
      return true
    return false
  if cleared then
    run? (← `(tactic| clear $(mkIdent chunkName):ident))
    return some (Name.anonymous, false, rawWitEqs)  -- consumed, nothing to track
  -- soundness conversion runs AFTER the open: the call boundary is opaque to
  -- circuit_norm (chunks stay pristine), and converting last keeps the emitted
  -- contract out of the open-simp's reach — reducing a contract's `.Spec` bundle
  -- projection without its bridges is a whnf bomb (FullWidth's sealed inner region)
  if sound then
    withMainContext do
      if let some decl := (← getLCtx).findFromUserName? chunkName then
        SubcircuitRw.runSoundness decl.fvarId (strict := true) (useOpsIdx := true)
  return some (chunkName, isCall, rawWitEqs)

/-- Find a call-keyed constraint chunk subterm of `e` — the no-call-left-behind scan.
A `.call` whose constraints survive to the end of the prefix means a circuit shape
the in-peel engine does not cover; that must be a LOUD failure (the growth model:
add the constructor's `@[chunk_split]` lemma), never a silently-raw chunk. Binders
are entered by telescope so ∀-bound loop chunks are seen. -/
partial def findCallChunk (e : Expr) : MetaM (Option Expr) := do
  if e.isAppOf ``RegionOperations.Constraints || e.isAppOf ``Halo2.Constraints then
    if (← SubcircuitRw.matchChunk? e).isSome then
      return some e
  match e with
  | .app f a =>
    if let some r ← findCallChunk f then return some r
    findCallChunk a
  | .forallE .. =>
    forallBoundedTelescope e (some 1) fun _ body => findCallChunk body
  | .lam .. =>
    lambdaBoundedTelescope e 1 fun _ body => findCallChunk body
  | .letE _ t v b _ =>
    if let some r ← findCallChunk t then return some r
    if let some r ← findCallChunk v then return some r
    findCallChunk b
  | .mdata _ b => findCallChunk b
  | .proj _ _ b => findCallChunk b
  | _ => return none

/-- The v2 runner. The caller's list is CPS1-style: bundle constants yield on-the-fly
contract bridges (`mkBundleBridges`), everything else is an unfold lemma (linted for
`circuit_norm` redundancy). Factored circuit defs in `main` (synth wrappers) unfold
automatically (`autoUnfoldsOfMain`), so the bind loop sees the do-block. -/
def run (sound region : Bool) (terms : Option (Array Term)) : TacticM Unit := do
  -- ── (a) intro the config through products; binder names come out of the pattern
  -- matches via the dsimp in (b), so positional names suffice here ──
  let heads : List Name :=
    [``FormalCircuit.Soundness, ``FormalCircuit.Completeness,
     ``FormalRegionCircuit.Soundness, ``FormalRegionCircuit.Completeness]
  let bundleBinderNames : Array Name := #[`cfg, `offset]
  let mut guard := 0
  while guard < 8 do
    let ty ← withMainContext do instantiateMVars (← getMainTarget)
    if heads.any ty.isAppOf then
      break
    unless ty.isForall do break
    let nm := bundleBinderNames.getD guard (Name.mkSimple s!"cfg_binder_{guard}")
    run? (← `(tactic| intro $(mkIdent nm):ident))
    -- destructure through PRODUCTS only (a config tuple); never into structures
    let mut inner := 0
    while inner < 8 do
      let done ← withMainContext do
        let some decl := (← getLCtx).findFromUserName? `cfg | return true
        let cty ← whnfR (← instantiateMVars decl.type)
        if cty.isAppOf ``Prod then
          bestEffort <| liftMetaTactic fun g => do
            let subgoals ← g.cases decl.fvarId
              #[⟨true, [Name.mkSimple s!"cfg_{inner+1}", `cfg]⟩]
            pure (subgoals.map (·.mvarId)).toList
          return false
        return true
      if done then break
      inner := inner + 1
    guard := guard + 1
  -- resolve the caller's list + the auto-unfolds (goal is now `<head> main …`)
  let (userUnfolds, bridges) ← CircuitProofStart.mkUnfoldLemmas terms
  let autoUnfolds ← CircuitProofStart.autoUnfoldsOfMain (excludeLoops := true)
  let unfolds := userUnfolds ++ (← autoUnfolds.mapM fun n =>
    `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term))
  let iffName : Name :=
    if region then
      if sound then ``FormalRegionCircuit.soundness_iff
      else ``FormalRegionCircuit.completeness_iff
    else
      if sound then ``FormalCircuit.soundness_iff else ``FormalCircuit.completeness_iff
  let idx : Name := if region then `self else `i₀
  if sound then
    run? (← `(tactic| rw [$(mkIdent iffName):ident]))
    run? (← `(tactic| intro $(mkIdent idx):ident $(mkIdent `env):ident
      $(mkIdent `input_var):ident $(mkIdent `input):ident $(mkIdent `output):ident
      $(mkIdent `input_eq):ident $(mkIdent `output_eq):ident $(mkIdent `env_assumptions):ident
      $(mkIdent `assumptions):ident $(mkIdent `constraints):ident))
  else
    run? (← `(tactic| rw [$(mkIdent iffName):ident]))
    run? (← `(tactic| intro $(mkIdent idx):ident $(mkIdent `env):ident
      $(mkIdent `input_var):ident $(mkIdent `input):ident $(mkIdent `output):ident
      $(mkIdent `input_eq):ident $(mkIdent `output_eq):ident $(mkIdent `witnesses):ident
      $(mkIdent `env_assumptions):ident $(mkIdent `assumptions):ident $(mkIdent `prover_assumptions):ident))
  run? (← `(tactic| obtain ⟨$(mkIdent `place):ident, $(mkIdent `env):ident⟩
    := $(mkIdent `env):ident))
  -- ── (b) definitional cleanup + output landing ──
  run? (← `(tactic| dsimp only [] at *))
  if region then
    run? (← `(tactic| simp only [ElaboratedRegionCircuit.output_eq]
      at $(mkIdent `output_eq):ident))
  else
    run? (← `(tactic| simp only [ElaboratedCircuit.output_eq]
      at $(mkIdent `output_eq):ident))
  -- open factored circuit defs (synth wrappers etc.) so the bind chain is visible
  unless unfolds.isEmpty do
    let chunk := if sound then `constraints else `witnesses
    run? (← `(tactic| simp only [$unfolds,*]
      at $(mkIdent chunk):ident $(mkIdent `output_eq):ident))
    unless sound do
      run? (← `(tactic| simp only [$unfolds,*]))
  -- ── (c) the bind loop ──
  let chunkHyp := if sound then `constraints else `witnesses
  let mut witEqs : Array Name := #[]
  let mut regionIdx := 0
  for _ in [0:32] do
    match ← peelOneBind sound region chunkHyp regionIdx unfolds with
    | some (nm, isCall, weqs) =>
      witEqs := witEqs ++ weqs
      if nm == Name.anonymous || isCall then pure ()
      else regionIdx := regionIdx + 1
    | none => break
  -- ── (d) terminal step ──
  -- A chain may end in a REAL step instead of `pure` (`do …; assignRegion "…" body`):
  -- the remaining chunk hypothesis IS that step's chunk and must be kept and
  -- registered, not cleared (clearing it silently dropped the final step's
  -- constraints — found porting FullWidth, whose add region is the terminal step).
  let terminalStep? ← do
    let some ty ← hypType? chunkHyp | pure none
    let some body := bodyOfChunkType? ty | pure none
    if body.isAppOf ``Pure.pure then pure none else pure (some body)
  match terminalStep? with
  | some body =>
    let isCall := body.isAppOf ``Halo2.FormalCircuit.call
      || body.isAppOf ``Halo2.FormalRegionCircuit.call
    let chunkName := if isCall then Name.mkSimple "out_spec"
      else Name.mkSimple s!"region_{regionIdx}"
    run? (← `(tactic| have $(mkIdent chunkName):ident := $(mkIdent chunkHyp):ident))
    run? (← `(tactic| clear $(mkIdent chunkHyp):ident))
    -- the terminal step's output IS the bundle output: canonicalize its spelling in
    -- output_eq (the bind peel does this per step; the terminal must too)
    run? (← `(tactic| simp only [FormalCircuit.output_call',
      FormalRegionCircuit.output_call, FormalRegionCircuit.output_call',
      output_assignRegion] at $(mkIdent `output_eq):ident))
    if isCall then
      -- in-peel engine: the terminal call converts like every peeled bind
      if sound then
        witEqs := witEqs ++ (← convertCallChunkSound chunkName `out)
      else
        witEqs := witEqs ++ (← convertGoalScoped `out chunkName (required := true))
    else
      -- the terminal raw chunk: structural split, then convert. A PURE region-bundle
      -- invocation `assignRegion "…" (X.call …)` (H review note 1(i)) becomes a single
      -- call chunk; on the soundness side it converts WHNF-SAFELY before any open (edge
      -- (b)): fold its region index to a literal first — otherwise the soundness leaf's
      -- `isDefEq hyp chunk` whnf's the `Constraints` region-arg's
      -- `regionCount [.region … <sealed body>]` and unfolds the seal (the whnf bomb) —
      -- then convert and SKIP the `circuit_norm` open entirely (the chunk is now a bare
      -- contract; opening it would whnf the child `Spec`/`output`/`extract`, a bundle
      -- δ-unfold, for nothing). A MIXED raw chunk (gates + embedded call) keeps the
      -- open-then-convert order: the open normalizes gates while the `.call` boundary
      -- stays opaque, so `circuit_norm` never meets the contract.
      run? (← `(tactic| simp only [chunk_split] at $(mkIdent chunkName):ident))
      let pureCall ← withMainContext do
        let some ty ← hypType? chunkName | pure false
        pure (← SubcircuitRw.matchChunk? ty).isSome
      if sound then
        if pureCall then
          run? (← `(tactic| simp only [nextRegionIndex_assignRegion, nextRegionIndex_loadTable,
            FormalCircuit.nextRegionIndex_call, foldCallRegionCount, Operations.regionCount,
            Nat.add_zero, Nat.zero_add] at $(mkIdent chunkName):ident))
          withMainContext do
            if let some decl := (← getLCtx).findFromUserName? chunkName then
              SubcircuitRw.runSoundness decl.fvarId (strict := true) (useOpsIdx := true)
        else
          run? (← `(tactic| simp only [circuit_norm, $unfolds,*] at $(mkIdent chunkName):ident))
          withMainContext do
            if let some decl := (← getLCtx).findFromUserName? chunkName then
              SubcircuitRw.runSoundness decl.fvarId (strict := true) (useOpsIdx := true)
      else
        run? (← `(tactic| simp only [chunk_split]))
        witEqs := witEqs ++ (← convertGoalScoped `out chunkName (required := false))
        run? (← `(tactic| simp only [circuit_norm, $unfolds,*] at $(mkIdent chunkName):ident))
      -- content-free terminal chunks vanish, like the peel's (an output-only step —
      -- HashPieceRound's terminal `readState` — opens to `True`)
      let cleared ← withMainContext do
        let some decl := (← getLCtx).findFromUserName? chunkName | return true
        if (← instantiateMVars decl.type).isConstOf ``True then return true
        return false
      if cleared then
        run? (← `(tactic| clear $(mkIdent chunkName):ident))
      else
        regionIdx := regionIdx + 1
        if sound then
          withMainContext do
            if let some decl := (← getLCtx).findFromUserName? chunkName then
              SubcircuitRw.runSoundness decl.fvarId (strict := true) (useOpsIdx := true)
  | none =>
    if region then
      if sound then
        run? (← `(tactic| rw [RegionCircuit.operations_pure, RegionOperations.constraints_nil]
          at $(mkIdent `constraints):ident))
      else
        run? (← `(tactic| rw [RegionCircuit.operations_pure,
          RegionOperations.constraints_nil]))
      run? (← `(tactic| rw [RegionCircuit.output_pure] at $(mkIdent `output_eq):ident))
    else
      if sound then
        run? (← `(tactic| rw [Circuit.operations_pure, constraints_nil]
          at $(mkIdent `constraints):ident))
      else
        run? (← `(tactic| rw [Circuit.operations_pure, constraints_nil]))
      run? (← `(tactic| rw [Circuit.output_pure] at $(mkIdent `output_eq):ident))
    run? (← `(tactic| clear $(mkIdent chunkHyp):ident))
  -- ── (f) landing (maintainer model, AddressIntegrity 90912413): decompose types
  -- with provable_type_simp, normalize the GIVENS, then one pass that uses `input_eq`
  -- and `output_eq` AS REWRITE RULES (component equations; `output_eq` fires
  -- left-to-right: circuit spelling → declared output) together with the caller's
  -- bridge list, over every derived hypothesis and the goal ──
  run? (← `(tactic| provable_type_simp))
  -- rule-sources: ONLY the naming equations `input_eq`/`output_eq` (cell spelling ↦
  -- declared value; that rewrite direction is forced). Row/witness equations
  -- (`region_*`) are normalized like every other hypothesis in pass 2 but are never
  -- fired by the tactic: whether to keep an output atom opaque or dissolve it into its
  -- witnessed value is a proof-dependent decision that belongs to the user half
  -- (main Clean's `circuit_proof_start` treats `h_env` the same way).
  let ruleSources : Array Name := #[`input_eq, `output_eq]
  -- pass 1: normalize ONLY the rule-sources, so their equations fire on the
  -- normalized spellings everywhere else. The caller's unfold list rides along
  -- (main Clean's CPS normalizes `h_input` with its extras too): a metadata
  -- `output` spelled via a helper def (e.g. `reads`) needs the unfold to expose
  -- its per-cell component equations.
  for g in ruleSources do
    run? (← `(tactic| simp only [circuit_norm, $(bridges ++ unfolds),*] at $(mkIdent g):ident))
  -- pass 2: derived hypotheses + goal, with input_eq/output_eq as rules
  let mut rules : Array (TSyntax `Lean.Parser.Tactic.simpLemma) :=
    #[← `(Lean.Parser.Tactic.simpLemma| circuit_norm),
      -- raw steps' region counts materialize only HERE (circuit_norm unfolds the
      -- folded nextRegionIndex in this pass) — fold them in the same fixpoint so
      -- chunk-contract indexes converge with the minted atoms' spellings
      ← `(Lean.Parser.Tactic.simpLemma| Operations.regionCount),
      ← `(Lean.Parser.Tactic.simpLemma| foldCallRegionCount)] ++ bridges ++ unfolds
  for g in ruleSources do
    rules := rules.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent g):term))
  -- pass-2 targets: everything except the rule-sources
  let pass2Excluded : Array Name := ruleSources
  let targets ← withMainContext do
    let mut ts : Array Name := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail || decl.userName.isInternal then continue
      if pass2Excluded.contains decl.userName then continue
      unless (← inferType (← instantiateMVars decl.type)).isProp do continue
      ts := ts.push decl.userName
    pure ts
  for t in targets do
    run? (← `(tactic| simp only [$rules,*] at $(mkIdent t):ident))
  run? (← `(tactic| simp only [$rules,*]))
  -- extract atoms: the GOAL joins the contracts' witness language — a parent whose
  -- extract forwards child witnesses meets the child contracts at the `wit_*` atoms
  -- (hypotheses keep their spelling: opacity stays the user's decision there)
  unless witEqs.isEmpty do
    let witLemmas ← witEqs.mapM fun n =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):term)
    run? (← `(tactic| simp only [$witLemmas,*]))
  -- ── no-call-left-behind (post-landing): any call-keyed constraint chunk still
  -- present is a circuit shape the in-peel engine does not cover — hard error, per
  -- the failure-semantics ruling. The landing has fully normalized by now, so even
  -- chunks that hid under shapes the structural set missed (an `ite`-guarded region,
  -- an untagged combinator) are visible to the scan. ──
  withMainContext do
    if sound then
      for decl in ← getLCtx do
        if decl.isImplementationDetail then continue
        if let some chunk ← findCallChunk (← instantiateMVars decl.type) then
          throwError "circuit_proof_start2: an unconverted call chunk survived in \
            hypothesis {decl.userName}:{indentExpr chunk}\nThis circuit shape is not \
            covered by the in-peel engine — tag its structural split lemma with \
            @[chunk_split] (see Clean/Halo2/Attributes.lean)."
    else
      if let some chunk ← findCallChunk (← instantiateMVars (← getMainTarget)) then
        throwError "circuit_proof_start2: an unconverted call chunk survived in the \
          goal:{indentExpr chunk}\nThis circuit shape is not covered by the in-peel \
          engine — tag its structural split lemma with @[chunk_split] (see \
          Clean/Halo2/Attributes.lean)."

end CircuitProofStart2

/-- `circuit_proof_start2` — the atomic-binds (CPS v2) proof prefix. See the module
docstring and `Clean/Halo2/atomic-binds-design.md`. Direction auto-detected from the
goal head. Adopted per proof; the v1 `circuit_proof_start` is untouched. -/
syntax (name := circuitProofStart2)
  "circuit_proof_start2" (" [" withoutPosition(term,*,?) "]")? : tactic

/-- Strip leading ∀ binders. -/
private partial def stripForalls (e : Expr) : Expr :=
  match e with
  | .forallE _ _ b _ => stripForalls b
  | e => e

@[tactic circuitProofStart2]
def evalCircuitProofStart2 : Tactic := fun stx => do
  let terms : Option (Array Term) :=
    match stx with
    | `(tactic| circuit_proof_start2 [$ts,*]) => some ts.getElems
    | _ => none
  -- direction via CPS1's detector (all four heads); region-level is not ported yet
  let some d ← CircuitProofStart.detectDirection?
    | throwError "circuit_proof_start2: goal is not a bundle Soundness/Completeness proof"
  CircuitProofStart2.run d.isSoundness d.isRegion terms

end Halo2
