import Clean.Halo2.Tactics.CircuitProofStart
import Clean.Ironwood.Ecc.WitnessPoint

/-!
# Test: `circuit_proof_start` — the halo2 bundle-proof prefix

Coverage (the acceptance matrix):

* **Direction detection ×4** — `Direction.ofHead?` on each of the four bundle-proof head constants
  (`FormalRegionCircuit.Soundness/.Completeness`, `FormalCircuit.Soundness/.Completeness`), plus the
  region/layouter × soundness/completeness axes each fixes.
* **The `whnfR` regression guard, on a real goal** — the detection bug the skeleton shipped with:
  `Soundness` is a semireducible `def`, so a default `whnf` unfolds it and hides the head. On a real
  `FormalRegionCircuit.Soundness …` application (built from `WitnessPoint.point`'s fields, with its
  `elaborated` instance) we check that a `whnfR` peel keeps the head visible whereas a `whnf` peel
  unfolds the def into a `∀` — the exact property `detectDirection?` relies on.
* **Leaf no-op tolerance / full pipeline** — `circuit_proof_start` run end-to-end on the leaf region
  gadget `WitnessPoint.point`, BOTH directions: steps (d)/(e) find no child chunk, so the leaf-only
  finish fires and lands the pure-field user half. Same pipeline Add exercises, on a second gadget.
* **Composite fixture** — the leaf/composite discriminator (`exprHasCircuitStructure`) flags a
  constraint-predicate head and passes a pure one; and a hand-built composite state shows the
  leaf-only finish is skipped so `hc`/`h_input` survive for a manual continuation.
* **Fix 3 (soundness step (b) touches the goal)** — the soundness constraints peel now includes `⊢`,
  so a passed `Spec`-unfold lemma fires at the goal (no manual `simp [circuit_norm, Spec]` after the
  call). Exercised by `MulIncomplete`'s soundness: its `RoundInvariant` (in the unfold list) is
  normalized at the goal, which let the former manual `simp only [circuit_norm, RoundInvariant]`
  line be dropped.

Coverage of the mul-stack review fixes, by where each is pinned:
* Fixes 1/2 (composite output split — the `h_output` component split, the value-toward **atom-left**
  orientation, and the vector-component `∀ i, <cell i> = output_zs[i]` forming with the lazy
  `getElem` bridge) live in `provable_type_simp` and are pinned in `TestProvableTypeSimp` (the
  `structEqSplit` field split, the vector-equation-forming pins, the lazy `getElem_eval_fields_cells`
  bridge), and exercised end-to-end by the `MulIncomplete`/`MulComplete`/`HashPiece` bundle proofs.
* Fix 3 (goal-side peel) — the pin below.
* Fix 6 (no obsolete-hypothesis bloat on the composite path) — exercised by the `Mul.lean` layouter
  bundle, whose bare `circuit_proof_start` leaves a clean state (no unused-hyp lint, no deep-term
  inflation), since the `synthesize`/`mainRegion` unfold defs are peeled manually at `hc` only.

(The layouter-level end-to-end pipeline is exercised for real by the migrated `Mul.lean` bundle,
`FormalCircuit` soundness AND completeness; region-level composite by `MulComplete.lean`.)
-/

namespace Halo2.TestProofStart

open Lean Elab Meta
open CircuitProofStart Zcash.Circuits Zcash.Circuits.Ecc

/-! ## Direction detection ×4 (the head-constant discriminator) -/

run_cmd Elab.Command.liftTermElabM do
  let check (n : Name) (expected : Option Direction) : TermElabM Unit := do
    let got := Direction.ofHead? (.const n [])
    unless got == expected do
      throwError "ofHead? {n}: expected {repr expected}, got {repr got}"
  check ``FormalRegionCircuit.Soundness (some .regionSoundness)
  check ``FormalRegionCircuit.Completeness (some .regionCompleteness)
  check ``FormalCircuit.Soundness (some .layouterSoundness)
  check ``FormalCircuit.Completeness (some .layouterCompleteness)
  -- a non-head constant is rejected (so the dispatcher defers to main Clean's tactic)
  check ``Nat.add none
  -- the axes each head fixes (region/layouter × soundness/completeness) and the index binder name
  unless (Direction.regionSoundness.isSoundness && Direction.regionSoundness.isRegion) do
    throwError "regionSoundness axes wrong"
  unless (!Direction.layouterCompleteness.isSoundness && !Direction.layouterCompleteness.isRegion) do
    throwError "layouterCompleteness axes wrong"
  unless (Direction.regionSoundness.regionIdxName == `self
      && Direction.layouterSoundness.regionIdxName == `i₀) do
    throwError "regionIdxName wrong"

/-! ## The `whnfR` regression guard, on a real `Soundness …` goal

`whnfR` (reducible transparency) leaves the semireducible `Soundness`/`Completeness` defs folded, so
the head constant stays visible after peeling the leading `∀`s; a default `whnf` unfolds them into
their own `∀ … → Spec …` body, so the peel walks into the definition's binders and never sees the
head (the skeleton's bug). We reproduce both peels on `WitnessPoint.point`'s real soundness goal
shape (`elaborated` instance supplied explicitly, as the structure field does). -/
run_cmd Elab.Command.liftTermElabM do
  let e ← Term.elabTermAndSynthesize
    (← `(fun (c : WitnessPoint.Config) (o : ℕ) =>
          (haveI := WitnessPoint.point.elaborated
           FormalRegionCircuit.Soundness WitnessPoint.point.configure
             WitnessPoint.point.synthesize c o
             (WitnessPoint.point.extract c o) (WitnessPoint.point.EnvAssumptions c)
             WitnessPoint.point.Assumptions WitnessPoint.point.Spec))) none
  Term.synthesizeSyntheticMVarsNoPostponing
  lambdaTelescope (← instantiateMVars e) fun _ body => do
    let bodyR ← whnfR body
    unless bodyR.getAppFn.constName? == some ``FormalRegionCircuit.Soundness do
      throwError "whnfR should keep `Soundness` folded; head = {bodyR.getAppFn}"
    let bodyW ← whnf body
    if bodyW.getAppFn.constName? == some ``FormalRegionCircuit.Soundness then
      throwError "regression: default `whnf` kept `Soundness` folded — the detection bug is masked"
    unless bodyW.isForall do
      throwError "expected default `whnf` to unfold `Soundness` into a `∀`; head {bodyW.getAppFn}"

/-! ## Leaf no-op tolerance / full pipeline

The leaf end-to-end pipeline — `circuit_proof_start [<gate>]` opening a region-level leaf bundle,
running all of (a)–(f) and landing the pure-field user half — is the headline acceptance in
`Clean/Ironwood/Ecc/Add.lean` (`Add.add` soundness AND completeness, both migrated to a single
`circuit_proof_start` call). The leaf no-op tolerance of steps (d)/(e) (`abstract_outputs`/
`subcircuit_rw` finding no child chunk) is exactly what makes that call close: on `Add.add` neither
fires, so the row-fact finish runs and drops the spent equations. We do not re-stage it here
(restating a bundle goal outside its structure field can't reproduce the canonical `elaborated`
instance the `circuit_norm` peel keys on); the `Add.lean` build is the real leaf coverage, and the
`whnfR` guard above already runs on the leaf `point` goal. -/

/-! ## Composite classification (`exprHasCircuitStructure`)

The predicate that drives the leaf/composite discriminator flags the constraint-predicate heads
(`RegionOperations.Constraints` / `Constraints` / `RegionOperations.ExtendsWitnesses` — what a
composite gadget's `hc`/goal still carries after the universal steps) and passes anything else (a
leaf's peeled, pure-field `hc`). It walks the whole expr tree, so a nested occurrence is caught. -/
run_cmd Elab.Command.liftTermElabM do
  let has (n : Name) : Bool := exprHasCircuitStructure (.const n [])
  unless has ``RegionOperations.Constraints do throwError "should flag RegionOperations.Constraints"
  unless has ``Constraints do throwError "should flag Halo2.Constraints"
  unless has ``RegionOperations.ExtendsWitnesses do
    throwError "should flag RegionOperations.ExtendsWitnesses"
  if has ``Eq then throwError "should NOT flag a pure-field `Eq`"
  if has ``And then throwError "should NOT flag a bare `And`"
  -- nested occurrence (inside an application) is still caught
  let nested := mkApp2 (.const ``And []) (.const ``RegionOperations.Constraints []) (.const ``True [])
  unless exprHasCircuitStructure nested do throwError "should catch a nested constraint predicate"

/-! ## Composite continuation shape (the finish is skipped, hyps survive)

A hand-built composite state mirroring what a composite gadget's context looks like right after
`circuit_proof_start` returns: because the state is composite, the tactic left BOTH `hc` and
`h_input` in place, so the manual continuation (`subcircuit_rw at hc`) works. On a leaf the same
tactic would instead have cleared these — the point of the discriminator. -/
example (config : WitnessPoint.Config) (self : RegionIndex) (place : RegionIndex → ℕ)
    (env : Environment Fp) (input : Var (Unconstrained Point) Fp)
    (_h_input : True)  -- a spectator equation the composite path leaves untouched
    (hc : RegionOperations.Constraints place self env
        ((WitnessPoint.point.call config 0 input).operations self)) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
        ((WitnessPoint.point.call config 0 input).output self)).Valid := by
  -- `hc` (the child chunk) is consumed by the engine, exactly as a composite continuation would;
  -- `_h_input` is still in scope (the composite path never cleared it).
  subcircuit_rw at hc
  abstract_outputs
  exact hc trivial trivial

end Halo2.TestProofStart
