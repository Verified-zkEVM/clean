import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Ironwood.Ecc.WitnessPoint

/-!
# Test: parent circuits composing subcircuits via the `subcircuit_rw` engine

The full engine coverage for `TestSubcircuit` + `TestLayouterSubcircuit`'s fixtures: every
consumption pattern, proven through the `subcircuit_rw` engine. These are the acceptance gate for
the engine AND the migration templates the composition consumers follow.

Patterns covered, each with both directions:
- **region parent, bare call** (`regionParent`);
- **region parent, own op + call** (`regionParentWithOp`);
- **layouter parent** composing a native layouter child and a `toFormal`-lifted region child
  (`layouterParent`) — covers the layouter level AND the `toFormal` bridge in one;
- **chained children**, second input = first output (`chainedParent`) — the completeness
  direction here *consumes* the derived statement `h_spec_0` for output bookkeeping;
- **bare-`place`/`env` loop-lemma context** — the tactic's own `isDefEq` unification, no
  discrimination tree (the loop-lemma scenario the engine handles natively).

## The two engine idioms

Soundness: `simp only [circuit_norm] at hc; subcircuit_rw at hc` weakens the folded chunk to
`hc : EnvA → A → Spec` (no marker/conjunct leftover); feed the preconditions to expose the child
`Spec`.

Completeness: `subcircuit_rw` strengthens every positive goal chunk **in place** to its
`EnvA ∧ A ∧ PA` precondition bundle (a single goal — the AND of the bundles when there are
several chunks) and introduces, up front, a **premised** derived statement per chunk
`h_spec_i : EnvA → A → PA → Spec ∧ ProverSpec`. Since both the goal's own bundle position and
each `h_spec_i`'s premises need the same `EnvA`/`A`/`PA` facts, the house-style dedup idiom is to
prove the bundle once (`have pre₀ := ⟨…⟩`) and feed its components to both places — see
`chainedParent` below.
-/

namespace Halo2.Ironwood.Ecc.TestSubcircuitRw

open Halo2 Halo2.Ironwood.Ecc

/-! ## Region parent, bare call -/

/-- Region parent running `witness_point` as a subcircuit. -/
def regionParent :
    FormalRegionCircuit Fp (Column .advice × Column .advice) WitnessPoint.Config
      (Unconstrained Point) Point where
  configure := fun cols => WitnessPoint.configure cols.1 cols.2
  synthesize config offset input := WitnessPoint.point.call config offset input
  Spec _ output _ := output.Valid
  ProverAssumptions input _ := input.Valid

  soundness := by
    intro config offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output _hE _hA hc
    -- normalize the chunk's element type, then the engine rewrites it to the child's contract
    simp only [circuit_norm] at hc
    subcircuit_rw at hc
    -- `hc : EnvA → A → Spec`; feed the (trivial) preconditions to expose `output.Valid`
    exact h_output ▸ hc trivial trivial

  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    -- the goal chunk strengthens in place to `EnvA ∧ A ∧ PA`; `h_spec_0` (premised
    -- `EnvA → A → PA → Spec ∧ ProverSpec`) enters the context up front.
    simp only [circuit_norm] at h_input hpa ⊢
    subcircuit_rw
    -- one goal: `EnvA ∧ A ∧ PA` (default `True`s + the parent's `ProverAssumptions`)
    exact ⟨trivial, trivial, by simpa only [circuit_norm, h_input] using hpa⟩

/-! ## Region parent with its OWN op + subcircuit call -/

/-- Region parent with an `assignAdvice` of its own followed by the subcircuit call. The real
scaling test: `circuit_norm` splits the parent's `++` and isolates the folded call chunk. -/
def regionParentWithOp :
    FormalRegionCircuit Fp (Column .advice × Column .advice) WitnessPoint.Config
      (Unconstrained Point) Point where
  configure := fun cols => WitnessPoint.configure cols.1 cols.2
  synthesize config offset input := do
    let _ ← assignAdvice config.x (offset + 1) (.ofFExpr input.x)
    WitnessPoint.point.call config offset input
  Spec _ output _ := output.Valid
  ProverAssumptions input _ := input.Valid

  soundness := by
    intro config offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output _hE _hA hc
    -- the assignAdvice's constraint is `True`; the engine walks the `True ∧ chunk` shape and
    -- rewrites the folded call chunk. The child is never unfolded.
    simp only [circuit_norm] at hc
    subcircuit_rw at hc
    exact h_output ▸ hc trivial trivial

  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    simp only [circuit_norm] at hwit h_input hpa ⊢
    subcircuit_rw
    exact ⟨trivial, trivial, by simpa only [circuit_norm, h_input] using hpa⟩

/-! ## Layouter parent: native child + `toFormal`-lifted region child -/

/-- Native layouter child (its body creates its own region). -/
def witnessPointL :
    FormalCircuit Fp (Column .advice × Column .advice) WitnessPoint.Config
      (Unconstrained Point) Point :=
  WitnessPoint.point.toFormal "witness_point (layouter)"

/-- Region child lifted to the layouter level via `toFormal`. -/
def witnessPointR :
    FormalCircuit Fp (Column .advice × Column .advice) WitnessPoint.Config
      (Unconstrained Point) Point :=
  WitnessPoint.point.toFormal "witness_point (via toFormal)"

/-- Layouter parent composing both children, returning the second output. Exercises the layouter
level AND the `toFormal` bridge. -/
def layouterParent :
    FormalCircuit Fp (Column .advice × Column .advice) WitnessPoint.Config
      (Unconstrained Point) Point where
  configure := fun cols => WitnessPoint.configure cols.1 cols.2
  synthesize config input := do
    let _ ← witnessPointL.call config input
    witnessPointR.call config input
  Spec _ output _ := output.Valid
  ProverAssumptions input _ := input.Valid

  soundness := by
    intro config
    rw [FormalCircuit.soundness_iff]
    intro i₀ env input_var input output h_input h_output _hE _hA hc
    -- circuit_norm isolates the two folded call chunks; the engine rewrites BOTH in one pass
    simp only [circuit_norm] at hc h_output
    obtain ⟨hcL, hcR⟩ := hc
    subcircuit_rw at hcR
    -- hcR : EnvA → A → Spec (second child); the parent output is the second child's output
    exact h_output ▸ hcR trivial trivial

  completeness := by
    intro config
    rw [FormalCircuit.completeness_iff]
    intro i₀ env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    simp only [circuit_norm] at hwit h_input hpa ⊢
    -- both goal chunks strengthen in place to their `EnvA ∧ A ∧ PA` bundles (one goal, the AND
    -- of the two); `h_spec_0`/`h_spec_1` (premised) enter the context up front.
    subcircuit_rw
    exact ⟨⟨trivial, trivial, by simpa only [circuit_norm, h_input] using hpa⟩,
      trivial, trivial, by simpa only [circuit_norm, h_input] using hpa⟩

/-! ## Chained children (second input = first output), consuming the derived statement

A minimal passthrough region child `passthrough : Point → Point` (emits no operations, `output =
input`, `Spec := output.Valid ↔ input.Valid` via `output = input`) lets us chain two calls with
type-compatible I/O (`witness_point`'s `Unconstrained Point` input can't take a `Point` output).
The parent chains it twice — the SECOND call's input is literally the first's output variable —
so the engine's leaf matching must read the (structurally different) `input` argument off each
chunk, and completeness must locate the right `ExtendsWitnesses` conjunct per chunk.

The completeness direction demonstrates **hwit co-processing with output bookkeeping**: the
engine introduces `h_spec_0`/`h_spec_1` (each child's `EnvA → A → PA → Spec ∧ ProverSpec`); the
first's `ProverSpec` (`output = input`) is *consumed* to prove the second child's chained
`ProverAssumptions` (its `input.Valid`, where its input is the first's output). -/

/-- Passthrough region child: no ops, output = input, prover spec `output = input`,
prover-assumption `input.Valid`. Trivially sound + complete (no constraints). -/
def passthrough :
    FormalRegionCircuit Fp Unit Unit Point Point where
  configure := fun _ => pure ()
  synthesize _ _ input := pure input
  Spec input output _ := input.Valid → output.Valid
  ProverAssumptions input _ := input.Valid
  ProverSpec input output _ := output = input
  soundness := by
    intro config offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output _hE _hA _hc
    -- no constraints; output = input (pure), so `input.Valid → output.Valid` is immediate
    simp only [circuit_norm] at h_output
    intro hv; rw [← h_output, h_input]; exact hv
  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output _hwit _hE _hA _hpa
    -- no ops: the `Constraints` conjunct is `True` (dropped by simp); goal is `output = input`
    simp only [circuit_norm] at h_input h_output ⊢
    rw [← h_output, h_input]

/-- Region parent chaining `passthrough` twice: the second call's input is the first's output. -/
def chainedParent :
    FormalRegionCircuit Fp Unit Unit Point Point where
  configure := fun _ => pure ()
  synthesize config offset input := do
    let mid ← passthrough.call config offset input
    passthrough.call config offset mid
  Spec input output _ := input.Valid → output.Valid
  ProverAssumptions input _ := input.Valid

  soundness := by
    intro config offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output _hE _hA hc
    simp only [circuit_norm] at hc h_input h_output
    obtain ⟨hc1, hc2⟩ := hc
    -- rewrite BOTH chained chunks to their `input.Valid → output.Valid` specs; compose them.
    -- hc1's `output` = mid = hc2's `input` (same term), so they chain by defeq — no unfolding.
    subcircuit_rw at hc1
    subcircuit_rw at hc2
    intro hv
    rw [← h_output]
    exact hc2 trivial trivial (hc1 trivial trivial (h_input ▸ hv))

  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    simp only [circuit_norm] at hwit h_input h_output hpa ⊢
    -- engine strengthens both goal chunks in place to `EnvA ∧ A ∧ PA`, and introduces the
    -- premised `h_spec_0`/`h_spec_1 : EnvA → A → PA → Spec ∧ ProverSpec` up front.
    subcircuit_rw
    -- the dedup idiom: prove the FIRST child's precondition bundle once as `pre₀`, then feed its
    -- components to both the goal's own bundle position and `h_spec_0` (instead of writing the
    -- `EnvA ∧ A ∧ PA` facts twice by hand).
    have pre₀ := (⟨trivial, trivial, h_input ▸ hpa⟩ : True ∧ True ∧ _)
    refine ⟨pre₀, trivial, trivial, ?_⟩
    -- the second child's chained ProverAssumption (its input IS the first's output) is
    -- discharged from `h_spec_0`'s ProverSpec (`first_output = first_input`), fed by `pre₀`.
    have hps0 := (h_spec_0 pre₀.1 pre₀.2.1 pre₀.2.2).2
    have hout : (passthrough.call config offset input_var).output self
        = passthrough.output config offset input_var self := rfl
    rw [hout] at *
    rw [hps0]; exact h_input ▸ hpa

/-! ## Bare-`place`/`env` loop-lemma context

A lemma phrased over bare `place : RegionIndex → ℕ` / `env : Environment Fp` — the shape a loop
lemma has. The `Placed`-projection-keyed iffs never fire here; the engine's own `isDefEq`
matching (no discrimination tree) rewrites the chunk regardless. -/

/-- Region bare context: firing must expose the child's `Spec` (`Point.Valid` of the output). -/
example (config : WitnessPoint.Config) (self : RegionIndex) (place : RegionIndex → ℕ)
    (env : Environment Fp) (input : Point (FExpr Fp))
    (h : RegionOperations.Constraints place self env
        ((WitnessPoint.point.call config 0 input).operations self)) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
        (WitnessPoint.point.output config 0 input self)).Valid := by
  subcircuit_rw at h
  exact h trivial trivial

/-- Layouter bare context, same scenario at the layouter level. -/
example (config : WitnessPoint.Config) (i₀ : RegionIndex) (place : RegionIndex → ℕ)
    (env : Environment Fp) (input : Point (FExpr Fp))
    (h : Halo2.Constraints place env ((witnessPointR.call config input).operations i₀) i₀) :
    (eval (⟨place, env⟩ : Placed Environment Fp)
        (witnessPointR.output config input i₀)).Valid := by
  subcircuit_rw at h
  exact h trivial trivial

-- Negative-position chunk is left untouched (weakening there would be unsound): the tactic is a
-- silent no-op, so the hypothesis survives verbatim and closes the goal directly. The `does
-- nothing` linter is expected here — the no-op is exactly what this case asserts.
set_option linter.unusedTactic false in
example (config : WitnessPoint.Config) (self : RegionIndex) (place : RegionIndex → ℕ)
    (env : Environment Fp) (input : Point (FExpr Fp))
    (h : (RegionOperations.Constraints place self env
        ((WitnessPoint.point.call config 0 input).operations self) → False) → False) :
    (RegionOperations.Constraints place self env
        ((WitnessPoint.point.call config 0 input).operations self) → False) → False := by
  subcircuit_rw at h  -- chunk sits under one `→`-left (net negative in `h`'s prop): untouched
  exact h

/-! ## Deep-argument generalization pin (the depth fix)

`subcircuit_rw` abstracts a chunk `input` to a fresh `x_gen_*` local (+ `h_gen_*` equation) exactly
when the input's structural depth passes `generalizeThreshold` — the chained-composed-output inputs
of Mul's complete/final-add chunks (whose `.output` *reduction* would otherwise explode the unifier)
clear it; small-gadget inputs stay inline. These pins fix that decision so it can't silently drift.

**Deep case gets named / shallow case does not.** The behavioral end-to-end evidence is the two
existing consumers: every gadget in *this* file has a shallow input (a record of a handful of cells,
depth ≤ ~15 — e.g. `chainedParent`'s second call whose input is a lone passthrough output), and none
of their proofs mention an `x_gen`/`h_gen` local — the tactic left them inline. Mul's `mul`
(`Clean/Ironwood/Ecc/Mul.lean`), by contrast, has the complete chunk (hi→lo chained input, depth
≈ 39) and the final-add chunk (carries the complete output, depth ≈ 44) named — its soundness proof
consumes `h_gen_hComp_0`/`h_gen_hFin_0` — and builds with ZERO `set_option maxRecDepth`.

The decision-function pins below fix the boundary directly (no heavy elaboration): -/

section GeneralizationThresholdPin
open Halo2.SubcircuitRw

/-- A right-nested application `f (f (f … a))` of structural depth `n` (each `.app` adds one level),
for exercising `boundedDepth`/`inputIsDeep` at and around the threshold. -/
private def nestedApp (n : Nat) : Lean.Expr :=
  let base := Lean.Expr.const `Nat.zero []
  let f := Lean.Expr.const `Nat.succ []
  Nat.rec base (fun _ acc => Lean.Expr.app f acc) n

-- the threshold is what separates "abstract" (Mul's chained chunks) from "inline" (small gadgets)
#guard generalizeThreshold == 38

-- `boundedDepth` is capped: it never reports more than `cap`, so it is safe on deep terms …
#guard boundedDepth (nestedApp 100) 40 == 40
-- … and it reports the true depth below the cap.
#guard boundedDepth (nestedApp 10) 100 == 11   -- 10 `succ` apps + the `zero` leaf

-- a SHALLOW input (below threshold) is left inline; a DEEP input (past threshold) is abstracted.
#guard inputIsDeep (nestedApp 10) == false
#guard inputIsDeep (nestedApp 200) == true

end GeneralizationThresholdPin

end Halo2.Ironwood.Ecc.TestSubcircuitRw
