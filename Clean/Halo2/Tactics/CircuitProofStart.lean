import Lean.Elab.Tactic
import Clean.Halo2.Formal
import Clean.Halo2.Tactics.ProvableTypeSimp
import Clean.Halo2.Tactics.AbstractOutputs
import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Utils.Tactics.CircuitProofStart

/-!
# `circuit_proof_start` — the composite prefix for halo2 bundle proofs

This is the halo2 counterpart of main Clean's `circuit_proof_start`
(`Clean/Utils/Tactics/CircuitProofStart.lean`), but it is a **composition of already-proven
parts**, not new machinery. Every step it runs is a tactic that already carries the migration's
soundness/completeness burden (`FormalRegionCircuit.soundness_iff`/`completeness_iff` and the
layouter mirrors; `provable_type_simp`; `abstract_outputs`; `subcircuit_rw`). This file only
sequences them behind one call, with the house-style intro names and the row-fact chaining shape
that the hand-written gadget proofs (`Add`, `MulComplete`, `Mul`) spell out today.

## What it does (the settled pipeline)

Given a bundle-proof goal `∀ config (offset)?, FormalRegionCircuit.Soundness …` (or the
`Completeness`/`FormalCircuit.*` variants), `circuit_proof_start [<unfold list>]`:

(a) **intro the leading bundle binders** (`config`, and `offset` at the region level), auto-detect
    the direction from the goal head, `rw` the matching `_iff`, and intro the post-iff binders with
    the established house names.
(b) `simp only [circuit_norm, <unfold list>]` at the direction's established target set — the
    **constraints** side (`hc` and `h_output` for soundness; `hwit` and the goal for completeness).
(c) `provable_type_simp` — normalize provable-type evals to the shared component normal form.
(d) `abstract_outputs` — make every child-call output opaque (no-op on leaf gadgets).
(e) `subcircuit_rw at hc` (soundness) / `subcircuit_rw` (completeness) — consume the child chunks
    (silent no-op when there are none, e.g. leaf gadgets).
(f) **row-fact chaining** — the `simp only [circuit_norm, h_input] …` idiom that lands the copied
    input cells on the input coordinates (soundness: `at hc ⊢`; completeness: chain `hwit` first,
    then `at ⊢ hA`).

Each step is its own function and is **total / no-op-tolerant**: a step that finds nothing to do
leaves the state untouched (e.g. a leaf gadget skips (d)/(e); a gadget with no copy equations skips
part of (f)). So the composite **stops gracefully** at whatever point a gadget's proof genuinely
diverges, and the user's manual continuation picks up from there — the "partial prefix + manual
rest" composability the migration requires.

## Direction detection

The goal at proof start is `∀ config (offset)?, HEAD …` where `HEAD` is one of the four constants
`FormalRegionCircuit.Soundness`, `FormalRegionCircuit.Completeness`, `FormalCircuit.Soundness`,
`FormalCircuit.Completeness`. We `whnf`-strip the leading `∀`s (introducing them as the bundle's
`config`/`offset` binders) until the body's head constant is one of those four, which fixes both
axes:

* **region vs layouter** — `FormalRegionCircuit.*` (uses `self`, and has an `offset` bundle binder)
  vs `FormalCircuit.*` (uses `i₀`, no `offset`);
* **soundness vs completeness** — the `.Soundness` vs `.Completeness` suffix, which selects the
  `_iff` lemma, the post-iff intro name list (soundness has no `hwit`; completeness does), and the
  step (b)/(e)/(f) target sets.

The number of leading bundle binders is read off the telescope, not hard-coded: we intro `∀`s with
generated names (`config`, then `offset` if a second binder remains before the head) until the head
matches. If the goal is already past the leading binders (head is a `Soundness`/`Completeness`
application directly), no bundle binder is introduced.

## House names (the one unavoidable naming choice)

The post-`_iff` binders are introduced as:

* soundness:  `self`/`i₀`, `env`, `input_var`, `input`, `output`, `h_input`, `h_output`, `hE`, `hA`, `hc`
* completeness: `self`/`i₀`, `env`, `input_var`, `input`, `output`, `h_input`, `h_output`, `hwit`, `hE`, `hA`, `hPA`

matching the region/layouter `_iff` RHS binder order. Downstream user halves refer to these names;
the migrated gadgets were aligned to them (the only edit their user halves needed).
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
does and ends with `hPA` (its ProverAssumptions) rather than soundness's constraints hyp `hc`. -/
def introNames (d : Direction) : List Name :=
  let idx := d.regionIdxName
  if d.isSoundness then
    [idx, `env, `input_var, `input, `output, `h_input, `h_output, `hE, `hA, `hc]
  else
    [idx, `env, `input_var, `input, `output, `h_input, `h_output, `hwit, `hE, `hA, `hPA]

end Direction

/-- Whether the goal (or any prefix of its leading `∀` telescope) is a halo2 bundle-proof head.
`forallTelescopeReducing` would peel past the leading bundle binders AND into the `Soundness`
definition's own `∀`s, so we instead peel binders one at a time and stop at the first recognized
head. Non-mutating. -/
def detectDirection? : TacticM (Option Direction) := withMainContext do
  let rec go (ty : Expr) (fuel : Nat) : MetaM (Option Direction) := do
    let ty ← whnf ty
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
  -- fixed generated names for the leading bundle binders, in order
  let bundleNames : Array Name := #[`config, `offset]
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
names. -/
def rwIffAndIntro (d : Direction) : TacticM Unit := do
  let iff := mkIdent d.iffLemma
  evalTactic (← `(tactic| rw [$iff:ident]))
  for nm in d.introNames do
    evalTactic (← `(tactic| intro $(mkIdent nm):ident))

/-- Build the extra-lemma `simpLemma` syntaxes from the user's `[<unfold list>]`. -/
def mkUnfoldLemmas (terms : Option (Array Term)) :
    TacticM (Array (TSyntax `Lean.Parser.Tactic.simpLemma)) := do
  match terms with
  | some ts => ts.mapM fun t => `(Lean.Parser.Tactic.simpLemma| $t:term)
  | none => pure #[]

/-- Step (b): `simp only [circuit_norm, <unfold list>]` at the direction's established constraints
target set. Soundness targets `hc` and `h_output`; completeness targets `hwit` and the goal. Every
target is guarded by `try`, so a gadget whose constraints hyp needs no such peel (or lacks
`h_output` in scope) is tolerated. -/
def peelConstraints (d : Direction) (unfold : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) :
    TacticM Unit := do
  if d.isSoundness then
    try evalTactic (← `(tactic| simp +instances only [circuit_norm, $unfold,*] at $(mkIdent `hc):ident $(mkIdent `h_output):ident)) catch _ => pure ()
  else
    try evalTactic (← `(tactic| simp +instances only [circuit_norm, $unfold,*] at $(mkIdent `hwit):ident ⊢)) catch _ => pure ()

/-- Step (c): `provable_type_simp` (never fails; runs to a fixpoint). -/
def normalizeProvable : TacticM Unit := do
  try evalTactic (← `(tactic| provable_type_simp)) catch _ => pure ()

/-- Step (d): `abstract_outputs` (silent no-op on leaf gadgets — no child outputs). -/
def abstractOutputs : TacticM Unit := do
  try evalTactic (← `(tactic| abstract_outputs)) catch _ => pure ()

/-- Step (e): consume the child chunks — `subcircuit_rw at hc` (soundness) / `subcircuit_rw`
(completeness). Silent no-op when there are no chunks (leaf gadgets), so this is total. -/
def consumeChunks (d : Direction) : TacticM Unit := do
  if d.isSoundness then
    try evalTactic (← `(tactic| subcircuit_rw at $(mkIdent `hc):ident)) catch _ => pure ()
  else
    try evalTactic (← `(tactic| subcircuit_rw)) catch _ => pure ()

/-- Step (f): the row-fact chaining idiom, per the established shapes. Soundness lands the copied
input cells on the input coordinates in the constraints hyp and the goal (`simp only [circuit_norm,
h_input] at hc ⊢`). Completeness first lands `hwit` on the input coordinates, then propagates it
into the goal and `hA` (`simp only [circuit_norm, h_input] at hwit`; then
`simp only [circuit_norm, h_input, hwit] at ⊢ hA`). Each is `try`-guarded: a leaf/no-copy gadget
whose hyps are already in normal form is a no-op. -/
def rowFactChaining (d : Direction) : TacticM Unit := do
  if d.isSoundness then
    -- soundness analogue of the completeness idiom: `h_output` plays `hwit`'s role, landing the
    -- copied output cells alongside the input cells in the constraints hyp and the goal.
    try evalTactic (← `(tactic| simp +instances only [circuit_norm, $(mkIdent `h_input):ident, $(mkIdent `h_output):ident] at $(mkIdent `hc):ident ⊢)) catch _ => pure ()
  else
    try evalTactic (← `(tactic| simp +instances only [circuit_norm, $(mkIdent `h_input):ident] at $(mkIdent `hwit):ident)) catch _ => pure ()
    try evalTactic (← `(tactic| simp +instances only [circuit_norm, $(mkIdent `h_input):ident, $(mkIdent `hwit):ident] at ⊢ $(mkIdent `hA):ident)) catch _ => pure ()

/-- The composite runner: steps (a)–(f), each no-op-tolerant. -/
def run (terms : Option (Array Term)) : TacticM Unit := do
  let d ← introBundleBindersAndDetect
  rwIffAndIntro d
  let unfold ← mkUnfoldLemmas terms
  peelConstraints d unfold
  normalizeProvable
  abstractOutputs
  consumeChunks d
  rowFactChaining d

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
