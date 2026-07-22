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
- **(c)** per bind, one block: single `operations_bind` peel (`constraints_append` at
  `constraints`, plus `extendsWitnesses_append` at `witnesses` and the goal's constraints side in the
  completeness direction), `output_bind` at `output_eq`, split off the chunk as
  `<name>_spec` (call binds) / `region_<k>` (raw binds, immediately
  `circuit_norm`-opened), canonicalize the output spelling (`output_call'`), then mint
  the atom by `generalize <name>_eq : <canonical output> = <name>` under a
  `revert constraints output_eq` — BEFORE the continuation's occurrences diverge — and fold the
  offsets (`nextRegionIndex_call` + the `foldCallRegionCount` simproc);
- **(d)** terminal `pure`: close the op list, land `output_eq` on the final atom;
- **(e)** `subcircuit_rw` — per chunk hypothesis (soundness) / goal-mode once
  (completeness, emitting `h_spec_<k>` over the atoms);
- **(f)** landing (maintainer model, AddressIntegrity 90912413): `provable_type_simp`
  decomposes types into the components that actually occur; normalize ONLY the
  rule-sources `input_eq`/`output_eq` (so their equations fire on normalized spellings);
  then ONE pass over every other hypothesis and the goal that uses
  `input_eq` and `output_eq` themselves AS REWRITE RULES — `output_eq` firing
  left-to-right (circuit spelling → declared output) — together with the CALLER'S
  LEMMA LIST (`circuit_proof_start2 [<child bridges, Spec/Assumptions unfolds>]`).
  With a complete list, trivially-composing parents close by `simp_all`/`grind`.

Known gaps: raw binds whose value IS used mint no atom yet (none in the sample); the
engine should replace (not leave) the consumed completeness witness chunks — the
tactic clears them meanwhile.
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
underscores stripped (`_lp` → `lp`); for a hygienic/anonymous binder on a call bind,
the called bundle's base name (`loop` for `(loop n w).call …`); `x` as the last
resort. -/
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
  stem.getD (calleeName x)
where
  /-- The called bundle's base name: `.call`'s bundle is its third-from-last argument. -/
  calleeName (x : Expr) : Name :=
    let args := x.getAppArgs
    if (x.isAppOf ``Halo2.FormalCircuit.call || x.isAppOf ``Halo2.FormalRegionCircuit.call)
        && args.size ≥ 3 then
      match args[args.size - 3]!.getAppFn.constName? with
      | some c => Name.mkSimple c.getString!
      | none => `x
    else `x

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
    let (_, g') ← g.generalize args
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

/-- One per-bind block. `sound := true` for the soundness direction; `region := true`
for region-level bundles (region append lemmas, no offset folding). Returns `none`
when the chunk hypothesis no longer holds a bind (terminal reached). -/
def peelOneBind (sound region : Bool) (chunkHyp : Name) (regionIdx : Nat)
    (unfolds : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM (Option (Name × Bool)) := do
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
    let some ty' ← hypType? chunkHyp | return some (chunkName, isCall)
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
  -- fold the offsets (layouter only; region binds share one region index)
  unless region do
    if sound then
      run? (← `(tactic| simp only [FormalCircuit.nextRegionIndex_call, foldCallRegionCount]
        at $(mkIdent chunkHyp):ident $(mkIdent `output_eq):ident))
    else
      run? (← `(tactic| simp only [FormalCircuit.nextRegionIndex_call, foldCallRegionCount]
        at $(mkIdent chunkHyp):ident $(mkIdent `output_eq):ident ⊢))
  -- raw (non-call) chunks open immediately; content-free ones (assignments) vanish
  unless isCall do
    run? (← `(tactic| simp only [circuit_norm, $unfolds,*] at $(mkIdent chunkName):ident))
    let cleared ← withMainContext do
      let some decl := (← getLCtx).findFromUserName? chunkName | return true
      if (← instantiateMVars decl.type).isConstOf ``True then
        return true
      return false
    if cleared then
      run? (← `(tactic| clear $(mkIdent chunkName):ident))
      return some (Name.anonymous, false)  -- consumed, nothing to track
  return some (chunkName, isCall)

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
`src` (post-engine: the opened contract speaks the child's extract). Skips Unit-like
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

/-- The names of engine-emitted `h_spec_<k>` hypotheses currently in context. -/
def specHyps : TacticM (Array Name) := withMainContext do
  let mut out := #[]
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && decl.userName.getString!.startsWith "h_spec_" then
      out := out.push decl.userName
  return out

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
    run? (← `(tactic| simp only [ElaboratedCircuit.output_eq] at $(mkIdent `output_eq):ident))
  -- open factored circuit defs (synth wrappers etc.) so the bind chain is visible
  unless unfolds.isEmpty do
    let chunk := if sound then `constraints else `witnesses
    run? (← `(tactic| simp only [$unfolds,*]
      at $(mkIdent chunk):ident $(mkIdent `output_eq):ident))
    unless sound do
      run? (← `(tactic| simp only [$unfolds,*]))
  -- ── (c) the bind loop ──
  let chunkHyp := if sound then `constraints else `witnesses
  let mut callChunks : Array Name := #[]
  let mut regionIdx := 0
  for _ in [0:32] do
    match ← peelOneBind sound region chunkHyp regionIdx unfolds with
    | some (nm, isCall) =>
      if nm == Name.anonymous then pure ()
      else if isCall then callChunks := callChunks.push nm
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
    if isCall then callChunks := callChunks.push chunkName
    else
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
  -- ── (e) engine ──
  let mut witEqs : Array Name := #[]
  if sound then
    for c in callChunks do
      run? (← `(tactic| subcircuit_rw ! at $(mkIdent c):ident))
      -- the opened contract is the first time the child's EXTRACT is spelled — mint
      -- it to the `wit_<binder>` atom (design doc: extract mirrors the output
      -- treatment at every call bind); its defining equation reduces in the landing
      -- pass via the child's `_extract_eq` bridge
      witEqs := witEqs ++ (← mintExtracts c
        (c.getString!.dropSuffix "_spec" |> Name.mkSimple ∘ ToString.toString))
    -- raw chunks can carry ∀-bound `.call` constraints (loop combinators over child
    -- calls); the engine supports those, and is a silent no-op on call-free chunks
    for k in [0:regionIdx] do
      run? (← `(tactic| subcircuit_rw ! at $(mkIdent (Name.mkSimple s!"region_{k}")):ident))
  else
    -- normalize the goal AND the witness-side chunks ONCE, IDENTICALLY, before the
    -- engine: every peel is done, so nothing remains for the peel `rw`s to match and
    -- the full pass is safe. This surfaces every call chunk in the canonical spelling
    -- the goal walker matches — calls embedded in mid-chain or terminal raw regions
    -- (`assignRegion "…" (X.call …)`, FullWidth's add), and calls under region-level
    -- bind spines (BFE's `witnessCheck13`) — with region counts folded to literal
    -- indexes. Witness chunks must ride in the SAME pass: the locator's child compare
    -- is fail-fast syntactic-first, and a goal-side-only pass leaves the two sides
    -- with invisibly different spellings (Chain's slot: an `if`-valued child argument
    -- diverged only under the goal normalization).
    let mut engineTargets : Array Name := callChunks
    for k in [0:regionIdx] do
      engineTargets := engineTargets.push (Name.mkSimple s!"region_{k}")
    let locs := engineTargets.map mkIdent
    run? (← `(tactic| simp only [circuit_norm, Operations.regionCount,
      foldCallRegionCount, $unfolds,*] at $[$locs:ident]* ⊢))
    run? (← `(tactic| subcircuit_rw !))
    -- h_spec_<k> arrives in call order — name the witness atom from the k-th call's
    -- do-binder (`wit_<binder>`), falling back to the index for excess spec hyps
    let hs ← specHyps
    -- specs beyond the call binds belong to calls embedded in raw steps (e.g.
    -- `assignRegion "…" (X.call …)`): a single one is the terminal output call
    -- (`wit_out`); several are disambiguated by spec index (`wit_out_<k>`)
    let unmatched := hs.size - min hs.size callChunks.size
    for i in [0:hs.size] do
      let h := hs[i]!
      let binder :=
        if hcc : i < callChunks.size then
          (callChunks[i].getString!.dropSuffix "_spec" |> ToString.toString)
        else if unmatched == 1 then "out"
        else s!"out_{i - callChunks.size}"
      witEqs := witEqs ++ (← mintExtracts h (Name.mkSimple binder))
  -- ── (f) landing (maintainer model, AddressIntegrity 90912413): decompose types
  -- with provable_type_simp, normalize the GIVENS, then one pass that uses `input_eq`
  -- and `output_eq` AS REWRITE RULES (component equations; `output_eq` fires
  -- left-to-right: circuit spelling → declared output) together with the caller's
  -- bridge list, over every derived hypothesis and the goal ──
  if !sound then
    -- the engine consumed the call chunks' witness sides; drop the raw leftovers —
    -- but only when it actually emitted the derived `h_spec_*` statements (an engine
    -- miss must keep the witness material for the user half's manual leaf application)
    -- (TODO: subcircuit_rw should replace them itself)
    unless (← specHyps).isEmpty do
      for c in callChunks do
        run? (← `(tactic| clear $(mkIdent c):ident))
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
