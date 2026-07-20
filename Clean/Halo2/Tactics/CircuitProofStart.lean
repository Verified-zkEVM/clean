import Lean.Elab.Tactic
import Clean.Halo2.Formal
import Clean.Halo2.Tactics.ProvableTypeSimp
import Clean.Halo2.Tactics.AbstractOutputs
import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Halo2.Tactics.ContractBridges
import Clean.Utils.Tactics.CircuitProofStart

/-!
# `circuit_proof_start` — the composite prefix for halo2 bundle proofs

This is the halo2 counterpart of main Clean's `circuit_proof_start`
(`Clean/Utils/Tactics/CircuitProofStart.lean`). It **sequences** already-proven parts —
`FormalRegionCircuit.soundness_iff`/`completeness_iff` and the layouter mirrors;
`provable_type_simp`; `abstract_outputs`; `subcircuit_rw` — behind one call, with the house-style
intro names and the row-fact chaining shape the hand-written gadget proofs (`Add`, `MulComplete`,
`Mul`) spell out. **Status: under construction.** The tactic layer is still being exercised across
the corpus; the step set and their ordering are chosen empirically for the gadgets built so far and
may be revisited (see the ordering caveat below).

## Step ordering (empirical)

The ordering below is what works for the current corpus, not a proven-optimal pipeline. In
particular, `abstract_outputs` (d) runs **after** `provable_type_simp` (c); this rests on the
empirical invariant that `provable_type_simp` does not scatter a gadget's own output term before
abstraction. An **abstract-early** alternative (run `abstract_outputs` right after the
`circuit_norm` peel, where child-output spellings are uniform `(….call …).output self` forms) was
also viable at design time — it trades more canonicalization guises for maximal opacity, and would
make the "`provable_type_simp` does not scatter outputs" invariant non-load-bearing. The current
order is not a settled decision.

Given a bundle-proof goal `∀ config (offset)?, FormalRegionCircuit.Soundness …` (or the
`Completeness`/`FormalCircuit.*` variants), `circuit_proof_start [<unfold list>]`:

(a) **intro the leading bundle binders** (`cfg`, and `offset` at the region level), auto-detect the
    direction from the goal head, `rw` the matching `_iff`, and intro the post-iff binders with the
    established house names.
(b) `simp only [circuit_norm, <unfold list>]` at the direction's established target set — the
    **constraints** side: `hc`, `h_output` and the goal for soundness; `hwit`, `hA`, `hPA`,
    `h_input`, `h_output` and the goal for completeness. `try`-guarded (a multi-target
    `simp … at …` fails only when NO target progresses, so it is a no-op on an already-normal
    state).
(c) `provable_type_simp` — normalize provable-type evals to the shared component normal form.
(d) `abstract_outputs` — make every child-call output opaque (no-op on leaf gadgets).
(e) `subcircuit_rw at hc` (soundness) / `subcircuit_rw` (completeness) — consume the child chunks
    (silent no-op when there are none, e.g. leaf gadgets).
(e′) **normalize what (e) created** — chunk consumption is the first time `(child).output`/
    `.extract`/contract-projection spellings exist, so `simp only [circuit_norm, <unfold list>,
    <bridges>]` runs again over that material: `hc` for soundness, the engine-emitted `h_spec_*`
    hypotheses and the goal for completeness.

Then, **only if the state is not composite** (`stateIsComposite` — see below), the leaf-only finish:

(f) **row-fact chaining** — the copy-equation idiom that lands the copied cells on the input/output
    coordinates. Soundness: `simp only [h_input, h_output] at hc ⊢` (no `circuit_norm` — the gate
    simprocs already fired in (b)). Completeness: `simp only [circuit_norm, h_input] at hwit`, then
    `simp only [circuit_norm, h_input, hwit] at ⊢ hA`, then land `h_output` on the input/witness
    values (`simp only [circuit_norm, h_input, hwit] at h_output`) so it reads as the per-coordinate
    value equation `output_i = input_i` — the bridge a leaf whose `ProverSpec` is a value equation
    (`output = input`, e.g. WitnessPoint) needs in its user half.
(g) **cleanup** — soundness `clear`s the spent `h_input`/`h_output`. Completeness `clear`s the spent
    `h_input`/`hwit` but KEEPS `h_output` (now the value equation), which the user half references
    (Add's user half does not, but there `h_output` stays in its `eval … = output` form, counted as
    used by the gadget's return, so no unused-hyp lint fires). When the state still reads the
    input var's cells outside the equations (the mixed hint+provable input record shape, where
    (f)'s landing can be partial), the equations are KEPT — they are the only tie between the
    remaining cell reads and the input values, and the user half consumes them manually.

Each step is its own function and is **total / no-op-tolerant**. The leaf/composite discriminator
(`stateIsComposite`) is whether the soundness constraints hyp `hc` (or, at completeness, the goal)
still carries an unpeeled constraint predicate (`RegionOperations.Constraints` / `Constraints` /
`RegionOperations.ExtendsWitnesses` — checking the *predicate*, not the `.call` marker, catches
loop-based composites whose chunks are folded inside a recursive def). On a **leaf** (Add,
WitnessPoint) it is `false`, so (f)/(g) run and close the prefix onto the pure-field user half; on a
**composite** (MulComplete, Mul) it is `true`, so (f)/(g) are SKIPPED and `hc`/`h_input`/`h_output`/
`hwit` survive for the manual continuation. The composite thus stops after the universal steps
(a)–(e) and the user's manual peel picks up from there ("partial prefix + manual rest").

Note: on the composite path, `provable_type_simp` (c) also destructures the gadget's `output` and
splits `h_output` into per-component atom-left value facts (`h_output_<field>`), including the
`∀ i, <cell i> = output_zs[i]` form for a vector component — see `ProvableTypeSimp`. The composite
user halves consume those facts directly.

## The unfold list: gadget-file-names only

`circuit_proof_start [<unfold list>]` feeds its arguments into the step-(b) peel, which already runs
`circuit_norm` (`simp only [circuit_norm, <unfold list>] at …`). So the list must carry ONLY names
that are **not** already `circuit_norm` members — in practice, **names defined in the gadget's own
file**: its gate definitions, its witness programs, and its `Spec`. A name that is already a
`circuit_norm` member (a tagged theorem like `RegionCircuit.operations_bind`, or a tagged `def` like
`Constraints.withSelector` / `Witgen.evalSteps`) is pure noise — it changes nothing, and left
unchecked such entries accrete across the corpus.

To keep this from happening, `mkUnfoldLemmas` **lints every argument** (`warnRedundantUnfold`,
`circuitNormMembers`): if a passed name is already in the `circuit_norm` set (theorem origins ∪
`toUnfold`), it emits a **warning** at that argument. Under CI's `--wfail` this fails the build, so
the noise cannot re-accumulate; interactively it is a loud, precisely-located diagnostic. The lazy
witness-eval reductions (`WitgenIR.getElem_eval_*`, `VExpr.getElem_eval_*`) are already
`@[circuit_norm ↓]`, so the raw structural recursors (`WitgenIROver.eval`, `VExprOver.eval`,
`WitgenIROver.ofFExpr`) never belong in a list — they are deliberately untagged to preserve the
opaque-until-consumed discipline, and the getElem-keyed lemmas do the reduction without them.

**Bundle entries.** A list entry that resolves to a **formal-circuit bundle** (`round`, `loop`) is
NOT unfolded — delta-unfolding a bundle materializes its proof-carrying structure literal, the
whnf/kernel hazard. Instead its contract bridges (`derive_contract_bridges` on the fly — the
per-projection `rfl` equations) are built and fed to step (e′), so the child's contract arrives
open without the consumer declaring or naming any bridge lemmas.

A shared **spec** unfold that the gadget's user half genuinely needs (e.g.
`Halo2.Ironwood.Point.nondegenerateAdd`, unfolded so `grind` can close AddIncomplete's completeness) is the
one legitimate non-own-file entry — it is neither `circuit_norm` noise nor another gadget's circuit
internals, but the same category as the gadget's own `Spec`. It is not linted (it is not a
`circuit_norm` member).

## Direction detection

The goal at proof start is `∀ config (offset)?, HEAD …` where `HEAD` is one of the four constants
`FormalRegionCircuit.Soundness`, `FormalRegionCircuit.Completeness`, `FormalCircuit.Soundness`,
`FormalCircuit.Completeness`. We strip the leading `∀`s (introducing them as the bundle's
`config`/`offset` binders) until the body's head constant is one of those four, which fixes both
axes.

**Reducible-only weak-head is load-bearing.** `Soundness`/`Completeness` are ordinary
(semireducible) `def`s, so a *default*-transparency `whnf` UNFOLDS them into their own
`∀ self env input, … → Spec …` body — the head constant then becomes a `∀`, never one of the
four, and the peel loop walks straight into the definition's binders and lands on `Spec`
(unknown head) → no direction. We therefore weak-head-normalize at **reducible** transparency
(`whnfR`), which leaves the four defs folded so their head constants are visible. (This was the
skeleton's detection bug: it used `whnf`, so it rejected every real bundle goal.)

* **region vs layouter** — `FormalRegionCircuit.*` (uses `self`, and has an `offset` bundle binder)
  vs `FormalCircuit.*` (uses `i₀`, no `offset`);
* **soundness vs completeness** — the `.Soundness` vs `.Completeness` suffix, which selects the
  `_iff` lemma, the post-iff intro name list (soundness has no `hwit`; completeness does), and the
  step (b)/(e)/(f) target sets.

The number of leading bundle binders is read off the telescope, not hard-coded: we intro `∀`s with
generated names (`cfg`, then `offset` if a second binder remains before the head) until the head
matches. If the goal is already past the leading binders (head is a `Soundness`/`Completeness`
application directly), no bundle binder is introduced.

## House names (the one unavoidable naming choice)

The post-`_iff` binders are introduced as (matching the region/layouter `_iff` RHS binder order):

* soundness:  `self`/`i₀`, `env`, `input_var`, `input`, `output`, `h_input`, `h_output`, `_hE`, `hA`, `hc`
* completeness: `self`/`i₀`, `env`, `input_var`, `input`, `output`, `h_input`, `h_output`, `hwit`, `_hE`, `hA`, `hPA`

`_hE` (the `EnvAssumptions` hypothesis) is underscore-prefixed: no leaf gadget's user half touches
it, and the linter would flag it otherwise. The verifier/prover assumptions land on `hA` in BOTH
directions (soundness's `Assumptions input`, completeness's `Assumptions ∧ ProverAssumptions` view),
so user halves say `obtain … := hA` uniformly. Downstream user halves refer to these names; the
migrated gadgets were aligned to them (the only edit their user halves needed — e.g. Add's
soundness `h_assumptions` → `hA`, completeness `hlast` → `hPA`).
-/

open Lean Elab Tactic Meta

namespace Halo2

namespace CircuitProofStart

/-- The four supported bundle-proof head constants, and the axes they fix. -/
inductive Direction where
  | regionSoundness | regionCompleteness | layouterSoundness | layouterCompleteness
deriving Repr, BEq, Inhabited

namespace Direction

/-- `true` for the two soundness directions. -/
def isSoundness : Direction → Bool
  | regionSoundness | layouterSoundness => true
  | _ => false

/-- `true` for the two region-level directions (`self`/`offset`); `false` for layouter (`i₀`). -/
def isRegion : Direction → Bool
  | regionSoundness | regionCompleteness => true
  | _ => false

/-- The head constant this direction corresponds to. -/
def headConst : Direction → Name
  | regionSoundness => ``FormalRegionCircuit.Soundness
  | regionCompleteness => ``FormalRegionCircuit.Completeness
  | layouterSoundness => ``FormalCircuit.Soundness
  | layouterCompleteness => ``FormalCircuit.Completeness

/-- The `_iff` lemma to `rw` for this direction. -/
def iffLemma : Direction → Name
  | regionSoundness => ``FormalRegionCircuit.soundness_iff
  | regionCompleteness => ``FormalRegionCircuit.completeness_iff
  | layouterSoundness => ``FormalCircuit.soundness_iff
  | layouterCompleteness => ``FormalCircuit.completeness_iff

/-- The recognized head constant of `e`, if it is one of the four bundle-proof heads. -/
def ofHead? (e : Expr) : Option Direction :=
  match e.getAppFn.constName? with
  | some n =>
    if n == ``FormalRegionCircuit.Soundness then some regionSoundness
    else if n == ``FormalRegionCircuit.Completeness then some regionCompleteness
    else if n == ``FormalCircuit.Soundness then some layouterSoundness
    else if n == ``FormalCircuit.Completeness then some layouterCompleteness
    else none
  | none => none

/-- The region-index binder name (`self` at region level, `i₀` at layouter level). -/
def regionIdxName (d : Direction) : Name := if d.isRegion then `self else `i₀

/-- The post-`_iff` binder names, in the `_iff` RHS order. Soundness has no `hwit`; completeness
does and ends with `hPA` (its ProverAssumptions) rather than soundness's constraints hyp `hc`. The
`EnvAssumptions` hypothesis is `_hE` (unused by leaf user halves; underscore avoids the linter). -/
def introNames (d : Direction) : List Name :=
  let idx := d.regionIdxName
  if d.isSoundness then
    [idx, `env, `input_var, `input, `output, `h_input, `h_output, `_hE, `hA, `hc]
  else
    [idx, `env, `input_var, `input, `output, `h_input, `h_output, `hwit, `_hE, `hA, `hPA]

end Direction

/-- Whether the goal (or any prefix of its leading `∀` telescope) is a halo2 bundle-proof head.
`forallTelescopeReducing` would peel past the leading bundle binders AND into the `Soundness`
definition's own `∀`s, so we instead peel binders one at a time and stop at the first recognized
head. We weak-head-normalize at **reducible** transparency (`whnfR`): a default `whnf` would
unfold the semireducible `Soundness`/`Completeness` defs and hide their head constant (see the
module docstring — this was the skeleton's detection bug). Non-mutating. -/
def detectDirection? : TacticM (Option Direction) := withMainContext do
  let rec go (ty : Expr) (fuel : Nat) : MetaM (Option Direction) := do
    let ty ← whnfR ty
    if let some d := Direction.ofHead? ty then
      return some d
    match fuel, ty with
    | fuel + 1, .forallE n t b bi =>
      withLocalDecl n bi t fun x => go (b.instantiate1 x) fuel
    | _, _ => return none
  go (← instantiateMVars (← getMainTarget)) 8

/-- Step (a) part 1: intro the leading bundle binders (`config`, and `offset` at region level),
returning the detected `Direction`. Introduces `∀`-binders with generated names until the goal's
head constant is one of the four bundle-proof heads. Fails loudly if no such head is ever reached
(the goal is not a bundle proof). -/
def introBundleBindersAndDetect : TacticM Direction := do
  -- fixed generated names for the leading bundle binders, in order (`cfg` matches the migrated
  -- gadgets' user halves, which refer to the config as `cfg`)
  let bundleNames : Array Name := #[`cfg, `offset]
  let mut i := 0
  -- guard against runaway (bundle prefixes are at most `config offset`)
  for _ in [0:8] do
    let goalTy ← withMainContext do instantiateMVars (← getMainTarget)
    if let some d := Direction.ofHead? goalTy then
      return d
    -- not yet at the head: must be a leading `∀`; intro it
    unless goalTy.isForall do
      throwError "circuit_proof_start: goal is not a bundle Soundness/Completeness proof (head is {goalTy.getAppFn})"
    let nm := if i < bundleNames.size then bundleNames[i]! else Name.mkSimple s!"cfg_binder_{i}"
    evalTactic (← `(tactic| intro $(mkIdent nm):ident))
    i := i + 1
  throwError "circuit_proof_start: could not locate a bundle Soundness/Completeness head after introducing leading binders"

/-- Step (a) part 2: `rw` the direction's `_iff` and intro the post-iff binders with the house
names. Immediately after introducing the placed environment binder `env`
(`env : Placed (Prover)Environment F`), destructure it into its two fields — the placement
`place : RegionIndex → ℕ` and the underlying environment `env : (Prover)Environment F` — so that
every `env.place`/`env.env` projection in the introduced hypotheses and goal reduces to bare
`place`/`env`, and any engine-reconstructed `Placed` literal becomes `⟨place, env⟩` over the two
variables. Both directions, both region and layouter paths (all four go through this loop).

`subcircuit_rw` (step e) needs no special handling: `SubcircuitRw.placedEnv?` reconstructs the
`⟨place, env⟩` literal from the bare pair when the common-`penv` projection shape is absent, so
the engine's `*_placed` leaves instantiate directly against the split context. -/
def rwIffAndIntro (d : Direction) : TacticM Unit := do
  let iff := mkIdent d.iffLemma
  evalTactic (← `(tactic| rw [$iff:ident]))
  for nm in d.introNames do
    evalTactic (← `(tactic| intro $(mkIdent nm):ident))
    if nm == `env then
      evalTactic (← `(tactic| obtain ⟨$(mkIdent `place):ident, $(mkIdent `env):ident⟩ := $(mkIdent `env):ident))

/-- The set of names that are already `circuit_norm` members — the union of the extension's
simp-theorem origins (tagged theorems) and its `toUnfold` set (tagged `def`s, e.g.
`Constraints.withSelector`, `Witgen.evalSteps`). Empty if the extension is somehow absent (never,
in a build that imported `circuit_norm`). Used to lint the unfold list (see `warnRedundantUnfold`). -/
def circuitNormMembers : CoreM NameSet := do
  match ← getSimpExtension? `circuit_norm with
  | none => return {}
  | some ext =>
    let thms ← SimpExtension.getTheorems ext
    let mut s : NameSet := {}
    for o in SimpTheorems.lemmaNames thms |>.toList do
      s := s.insert (Origin.key o)
    for n in SimpTheorems.toUnfold thms |>.toList do
      s := s.insert n
    return s

/-- **Unfold-list lint (the gadget-file-names-only rule).** `circuit_proof_start [<list>]` and the
peel-step `simp only [circuit_norm, …]` calls it feeds already run `circuit_norm`, so the list must
carry ONLY names *not* already in that set — in practice, names defined in the gadget's own file
(its gates, witness programs, `Spec`). A passed name that is already a `circuit_norm` member is pure
noise: it changes nothing and, left unchecked, accretes across the corpus. We emit a **warning** on
each such argument. Under CI's `--wfail` this fails the build, so the class of noise cannot
re-accumulate; interactively it is a loud, precisely-located diagnostic. Non-identifier arguments
(rare — the list is idents in practice) are left alone. -/
def warnRedundantUnfold (t : Term) (members : NameSet) : TacticM Unit := do
  -- resolve the argument to a global constant, if it is a plain (possibly dotted) identifier
  let names ← try
      pure (← resolveGlobalConst t.raw)
    catch _ => pure []
  for n in names do
    if members.contains n then
      logWarningAt t m!"circuit_proof_start: `{n}` is already a `@[circuit_norm]` member, so passing \
it in the unfold list is redundant (it changes nothing). Remove it — the unfold list should carry \
only names defined in this gadget's own file (gates, witness programs, `Spec`)."
      return

/-- Whether the constant is a formal-circuit bundle: its type, behind any parameter binders, is a
`FormalRegionCircuit`/`FormalCircuit` application. -/
def isBundleConst (n : Name) : MetaM Bool := do
  let some info := (← getEnv).find? n | return false
  forallTelescopeReducing info.type fun _ ty =>
    match ty.getAppFn.constName? with
    | some ``FormalRegionCircuit => return true
    | some ``FormalCircuit => return true
    | _ => return false

/-- Contract bridges for a bundle constant, as inline `simpLemma` terms: bind the bundle's
parameters, run `ContractBridges.buildBridges` on the applied bundle (yielding the closed
`∀ params, (bundle params).Spec = <reduced>` equations and their `rfl` proofs), and quote each
proof back to syntax. This is `derive_contract_bridges` on the fly — the caller passes the bundle
itself in the unfold list and never declares or names the bridge lemmas. -/
def mkBundleBridges (n : Name) : TermElabM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  let some info := (← getEnv).find? n | return #[]
  let bridges ← forallTelescopeReducing info.type fun params _ =>
    Halo2.ContractBridges.buildBridges n (mkAppN (mkConst n (info.levelParams.map mkLevelParam)) params)
  bridges.mapM fun (_, ty, pf) => do
    -- ascribe the bridge's `lhs = rhs` statement: the proof is a bare `Eq.refl`, whose inferred
    -- type is the useless `lhs = lhs`
    let stx ← Term.exprToSyntax (← mkExpectedTypeHint pf ty)
    `(Lean.Parser.Tactic.simpLemma| $stx:term)

/-- Build the extra-lemma `simpLemma` syntaxes from the user's `[<unfold list>]`, warning on any
argument that is already a `circuit_norm` member (see `warnRedundantUnfold`). A list entry that
resolves to a **formal-circuit bundle** is NOT unfolded (delta-unfolding a bundle materializes its
proof-carrying structure literal — the whnf/kernel hazard); instead its contract bridges are built
on the fly and returned separately, to be applied by the post-chunk normalize step (e′), where the
child's contract projections first appear. -/
def mkUnfoldLemmas (terms : Option (Array Term)) :
    TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma) ×
             Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  match terms with
  | some ts =>
    let members ← circuitNormMembers
    let mut unfold := #[]
    let mut bridges := #[]
    for t in ts do
      let names ← try pure (← resolveGlobalConst t.raw) catch _ => pure []
      match ← names.findM? (fun n => isBundleConst n) with
      | some n => bridges := bridges ++ (← mkBundleBridges n)
      | none =>
        warnRedundantUnfold t members
        unfold := unfold.push (← `(Lean.Parser.Tactic.simpLemma| $t:term))
    return (unfold, bridges)
  | none => pure (#[], #[])

/-- Step (b): `simp only [circuit_norm, <unfold list>]` at the direction's established constraints
target set. Soundness peels `hc`, `h_output` and the goal (the constraints hyp, the output-value
equation, and the goal `Spec`). Completeness peels `hwit`, `hA`, `hPA`, `h_input`, `h_output` and
the goal — the witness hyp, the (prover) assumptions, the input/output equations, and the goal
constraints (matching the reference completeness prefix). The whole call is `try`-guarded: a
multi-target `simp only … at …` fails only
when NO target makes progress, so this is a no-op on a gadget already in normal form. -/
def peelConstraints (d : Direction) (unfold : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM Unit := do
  if d.isSoundness then
    -- Peel the constraints hyp and the output-value equation, AND the goal (the `Spec`): the
    -- unfold list carries the gadget's `Spec` def (e.g. `RoundInvariant`), which must fire at the
    -- goal too — otherwise a composite gadget's user half has to re-run `simp [circuit_norm, Spec]`
    -- by hand. `try`-guarded, so it stays a no-op on a leaf whose `Spec` is already atomic.
    try evalTactic (← `(tactic| simp +instances only [circuit_norm, $unfold,*] at $(mkIdent `hc):ident $(mkIdent `h_output):ident ⊢)) catch _ => pure ()
  else
    try evalTactic (← `(tactic| simp +instances only [circuit_norm, $unfold,*] at $(mkIdent `hwit):ident $(mkIdent `hA):ident $(mkIdent `hPA):ident $(mkIdent `h_input):ident $(mkIdent `h_output):ident ⊢)) catch _ => pure ()

/-- Step (c): `provable_type_simp` (never fails; runs to a fixpoint). -/
def normalizeProvable : TacticM Unit := do
  try evalTactic (← `(tactic| provable_type_simp)) catch _ => pure ()

/-- Step (d): `abstract_outputs` (silent no-op on leaf gadgets — no child outputs). -/
def abstractOutputs : TacticM Unit := do
  try evalTactic (← `(tactic| abstract_outputs)) catch _ => pure ()

/-- Step (e): consume the child chunks — `subcircuit_rw at hc` (soundness) / `subcircuit_rw`
(completeness). Silent no-op when there are no chunks (leaf gadgets), so this is total.

No env re-bundling is needed on either path: `SubcircuitRw.placedEnv?` reconstructs
`⟨place, env⟩` from the split pair for the completeness `*_placed` leaves (its split-shape
fallback), and soundness's leaves read `place`/`env` positionally. -/
def consumeChunks (d : Direction) : TacticM Unit := do
  if d.isSoundness then
    try evalTactic (← `(tactic| subcircuit_rw at $(mkIdent `hc):ident)) catch _ => pure ()
  else
    try evalTactic (← `(tactic| subcircuit_rw)) catch _ => pure ()

/-- The engine-emitted `h_spec_*` hypotheses (the completeness-side child contracts). -/
def specHypIdents : TacticM (Array Ident) := withMainContext do
  let mut acc : Array Ident := #[]
  for decl in ← getLCtx do
    if !decl.isImplementationDetail && decl.userName.getString!.startsWith "h_spec" then
      acc := acc.push (mkIdent decl.userName)
  return acc

/-- Step (e′): normalize what `subcircuit_rw` created. The child chunks' consumption is the first
time `(child).output`/`.extract`/contract-projection spellings exist, so the `circuit_norm` set —
including the gadget's own tagged output lemmas — plus the unfold list and any on-the-fly contract
bridges (bundle entries of the unfold list) must run again over that material: `hc` for soundness,
the engine-emitted `h_spec_*` hypotheses and the goal for completeness. `try`-guarded no-op on
leaves (nothing new appeared). -/
def normalizeEmitted (d : Direction)
    (unfold bridges : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Unit := do
  if d.isSoundness then
    try evalTactic (← `(tactic| simp +instances only [circuit_norm, $(unfold ++ bridges),*] at $(mkIdent `hc):ident)) catch _ => pure ()
  else
    let specHyps ← specHypIdents
    for h in specHyps do
      try evalTactic (← `(tactic| simp +instances only [circuit_norm, $(unfold ++ bridges),*] at $h:ident)) catch _ => pure ()
    try evalTactic (← `(tactic| simp +instances only [circuit_norm, $(unfold ++ bridges),*])) catch _ => pure ()

/-- Whether an expression still carries **unpeeled circuit structure** — an application of one of
the constraint predicates `RegionOperations.Constraints` / `Constraints` (layouter) /
`RegionOperations.ExtendsWitnesses`. This is the leaf/composite discriminator that survives the
loop case: a **leaf** gadget (Add), once its constraints hyp is fully peeled by step (b), holds
only pure field equations — no constraint-predicate application remains; a **composite** gadget
(MulComplete, Mul) still carries `Constraints … ((loop/…).operations …)` (its child chunks, whether
directly exposed or hidden behind a recursive loop def), which its manual continuation peels and
routes into the child lemmas. Checking for the *predicate* rather than the `.call` marker is what
catches loop-based composites, whose chunks are folded inside the recursion. -/
def exprHasCircuitStructure (e : Expr) : Bool :=
  e.find? (fun sub =>
    match sub.getAppFn.constName? with
    | some ``RegionOperations.Constraints => true
    | some ``Halo2.Constraints => true
    | some ``RegionOperations.ExtendsWitnesses => true
    | _ => false) |>.isSome

/-- `true` when the state is still composite: the soundness constraints hyp `hc` (or, at
completeness, the goal) still carries an unpeeled constraint predicate. The leaf-only finish
(step (f) + cleanup) is skipped when this holds, leaving `hc`/`h_input`/`h_output`/`hwit` intact
for the manual continuation. A missing target hyp counts as leaf (nothing to protect). -/
def stateIsComposite (d : Direction) : TacticM Bool := withMainContext do
  if d.isSoundness then
    match (← getLCtx).findFromUserName? `hc with
    | some decl => return exprHasCircuitStructure (← instantiateMVars decl.type)
    | none => return false
  else
    return exprHasCircuitStructure (← instantiateMVars (← getMainTarget))

/-- Whether a hypothesis with the given user name exists (the splitter in
`provable_type_simp` may have consumed `h_output` into per-component facts). -/
def hypExists (n : Name) : TacticM Bool := withMainContext do
  return ((← getLCtx).findFromUserName? n).isSome

/-- Step (f): the row-fact chaining idiom, per the established shapes. Soundness lands the copied
input/output cells on the input coordinates in the constraints hyp and the goal
(`simp only [h_input, h_output] at hc ⊢`). Completeness first lands `hwit` on the input coordinates
(`simp only [circuit_norm, h_input] at hwit`), then propagates it into the goal and `hA`
(`simp only [circuit_norm, h_input, hwit] at ⊢ hA`). Each is `try`-guarded: a leaf/no-copy gadget
whose hyps are already in normal form is a no-op. -/
def rowFactChaining (d : Direction) : TacticM Unit := do
  let hOut ← hypExists `h_output
  if d.isSoundness then
    -- `h_output` plays `hwit`'s role, landing the copied output cells alongside the input cells
    -- in the constraints hyp and the goal. (No `circuit_norm` here: the gate simprocs already
    -- fired in step (b); re-running them is wasted work and risks re-folding the split conjuncts.)
    if hOut then
      try evalTactic (← `(tactic| simp +instances only [$(mkIdent `h_input):ident, $(mkIdent `h_output):ident] at $(mkIdent `hc):ident ⊢)) catch _ => pure ()
    else
      try evalTactic (← `(tactic| simp +instances only [$(mkIdent `h_input):ident] at $(mkIdent `hc):ident ⊢)) catch _ => pure ()
  else
    try evalTactic (← `(tactic| simp +instances only [circuit_norm, $(mkIdent `h_input):ident] at $(mkIdent `hwit):ident)) catch _ => pure ()
    try evalTactic (← `(tactic| simp +instances only [circuit_norm, $(mkIdent `h_input):ident, $(mkIdent `hwit):ident] at ⊢ $(mkIdent `hA):ident $(mkIdent `hPA):ident)) catch _ => pure ()
    -- Land `h_output` on the input/witness values. A leaf whose `ProverSpec` is a value equation
    -- (`output = input`, e.g. WitnessPoint) leaves that obligation as a goal conjunct over the free
    -- `output` coords; after this rewrite `h_output` reads as the per-coordinate value equation
    -- (`output_i = input_i`), which its user half supplies directly (kept in scope by the
    -- `try clear` below). No-op / cleared for a gadget whose completeness goal is pure constraints
    -- (e.g. Add).
    if hOut then
      try evalTactic (← `(tactic| simp +instances only [circuit_norm, $(mkIdent `h_input):ident, $(mkIdent `hwit):ident] at $(mkIdent `h_output):ident)) catch _ => pure ()

/-- Whether an expression still carries a **folded child contract** — an application of a
bundle's `Spec`/`ProverSpec` projection (the shape `subcircuit_rw` leaves for consumers of
`.call` chunks, including `∀`-bound loop chunks). While such applications remain, the
input/output equations must survive the finish: after the consumer opens the contract
bridges, the child's cell-spelled values need `h_input`/`h_output` to land on the parent's
locals. -/
def exprHasFoldedContract (e : Expr) : Bool :=
  e.find? (fun sub =>
    match sub.getAppFn.constName? with
    | some ``FormalRegionCircuit.Spec => true
    | some ``FormalRegionCircuit.ProverSpec => true
    | some ``FormalCircuit.Spec => true
    | some ``FormalCircuit.ProverSpec => true
    | _ => false) |>.isSome

/-- Whether the goal or any hypothesis — other than the `exclude`d hypotheses and the
vars' own declarations — mentions a var whose name is `name` or starts with `name_`
(the destructure pass renames `input_var` to `input_var_<field>` components, which must
count as references for the cleanup's load-bearing check). `false` when none exists. -/
def stateReferencesFVar (name : Name) (exclude : List Name) : TacticM Bool := withMainContext do
  let prefixStr := name.toString ++ "_"
  let vars := (← getLCtx).foldl (init := (#[] : Array FVarId)) fun acc d =>
    if !d.isImplementationDetail &&
        (d.userName == name || (d.userName.toString.startsWith prefixStr)) then
      acc.push d.fvarId
    else acc
  if vars.isEmpty then return false
  let refs := fun (e : Expr) => vars.any e.containsFVar
  if refs (← instantiateMVars (← getMainTarget)) then
    return true
  for d in ← getLCtx do
    if d.isImplementationDetail || vars.contains d.fvarId || exclude.contains d.userName then
      continue
    if refs (← instantiateMVars d.type) then
      return true
  return false

/-- `true` when any hypothesis or the goal still carries a folded child contract. -/
def stateHasFoldedContract : TacticM Bool := withMainContext do
  if exprHasFoldedContract (← instantiateMVars (← getMainTarget)) then
    return true
  for decl in ← getLCtx do
    if !decl.isImplementationDetail then
      if exprHasFoldedContract (← instantiateMVars decl.type) then
        return true
  return false

/-- Cleanup: drop the input/output (and, for completeness, witness) equations that steps (b)/(f)
have already fully consumed — matching the reference proofs' `clear` after row-fact chaining. Kept
`try`-guarded and total: if a hypothesis is still referenced (a diverging gadget's manual half may
need it), `clear` fails and is silently skipped, leaving it in scope.

When the state still reads the input var's cells outside the equations themselves, the input
equations are kept even if step (f) fired — a PARTIAL landing (the mixed hint+provable input
record shape: direct fields land, nested/hint components may not) leaves them as the only tie
between the remaining cell reads and the input values, and the user half must consume them
manually. A leaf whose state ended in normal form (no `input_var` reference outside the
equations) still drops them, as before. -/
def clearConsumed (d : Direction) : TacticM Unit := do
  -- a consumer of child contracts — folded, or already opened by (e′)'s bridges but with the
  -- engine-emitted `h_spec_*` hypotheses still to consume — needs the input/output equations
  -- in its manual continuation; keep them (the linter treats them as used via the return)
  if (← stateHasFoldedContract) || !(← specHypIdents).isEmpty then
    return
  if ← stateReferencesFVar `input_var [`h_input, `h_output, `hwit] then
    return
  if d.isSoundness then
    if ← hypExists `h_output then
      try evalTactic (← `(tactic| clear $(mkIdent `h_input):ident $(mkIdent `h_output):ident)) catch _ => pure ()
    else
      try evalTactic (← `(tactic| clear $(mkIdent `h_input):ident)) catch _ => pure ()
  else
    -- `h_input`/`hwit` are always spent by the finish. `h_output` is deliberately KEPT: after the
    -- value-landing in the finish it reads as the per-coordinate value equation
    -- (`output_i = input_i`), which a leaf whose `ProverSpec` is a value equation (WitnessPoint)
    -- needs in its user half. A pure-constraint gadget (Add) does not reference it — but the finish
    -- leaves it in its original `eval … = output` form, which the linter treats as used by the
    -- gadget's return, so this does not introduce an unused-hyp lint.
    try evalTactic (← `(tactic| clear $(mkIdent `h_input):ident $(mkIdent `hwit):ident)) catch _ => pure ()

/-- The composite runner: steps (a)–(f) plus the consumed-equation cleanup, each no-op-tolerant.

Steps (a)–(e) are universal (intro / peel / `provable_type_simp` / `abstract_outputs` /
`subcircuit_rw`); they are idempotent or no-op-tolerant and never mangle a composite gadget's
constraints. The row-fact chaining (f) — the VALUE-REPLACEMENT half — also runs universally:
it rewrites the constraint/witness hypotheses and the goal with the `h_input`/`h_output`/`hwit`
equations, so every hint-program eval and copied-cell read lands on its prover-value variable.
On a composite this is safe (folded child chunks are operations-data, not eval atoms) and is
what lets the manual continuation live at VALUES instead of hand-bridging framework spellings.
Only the destructive cleanup — clearing the spent equations — stays leaf-gated: on a **leaf**
(Add) it drops them, closing the prefix; on a **composite** (MulComplete, Mul) they survive for
the manual continuation (and `clearConsumed`'s own folded-contract/`h_spec_*`/reference guards
protect them besides). -/
def run (terms : Option (Array Term)) : TacticM Unit := do
  let d ← introBundleBindersAndDetect
  rwIffAndIntro d
  let (unfold, bridges) ← mkUnfoldLemmas terms
  peelConstraints d unfold
  normalizeProvable
  abstractOutputs
  consumeChunks d
  normalizeEmitted d unfold bridges
  rowFactChaining d
  unless (← stateIsComposite d) do
    clearConsumed d

end CircuitProofStart

/-- `circuit_proof_start [<unfold list>]` — the halo2 bundle-proof prefix, a composition of the
proven parts (`soundness_iff`/`completeness_iff`, `provable_type_simp`, `abstract_outputs`,
`subcircuit_rw`) behind one call. Auto-detects the direction (region/layouter × soundness/
completeness) from the goal head, intros the house-named binders, peels the constraints with
`circuit_norm` plus the given unfold list, normalizes provable evals, makes child outputs opaque,
consumes the child chunks, and runs the row-fact chaining idiom. Every step is no-op-tolerant, so
the call composes with a manual continuation wherever a gadget's proof diverges. See the module
docstring.

**Token sharing.** Main Clean's `circuit_proof_start`
(`Clean/Utils/Tactics/CircuitProofStart.lean`) already owns the `circuit_proof_start` token; this
file adds an `elab_rules` to that *same* syntax. Lean tries the most-recently-imported `elab_rules`
first, so on a halo2 bundle head this rule fires; on any other goal it `throwUnsupportedSyntax`es,
and Lean falls back to main Clean's rule (which handles main Clean's `Soundness`/`Completeness`
heads). The two never both run — direction detection (`detectDirection?`, non-mutating) is the
discriminator. -/
elab_rules : tactic
  | `(tactic| circuit_proof_start $[[$terms:term,*]]?) => do
    -- defer to main Clean's identically-named tactic unless this is a halo2 bundle goal
    let some _ ← CircuitProofStart.detectDirection? | throwUnsupportedSyntax
    let terms := terms.map (·.getElems)
    CircuitProofStart.run terms

end Halo2
