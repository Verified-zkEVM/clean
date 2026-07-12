import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Ironwood.Ecc.WitnessPoint

/-!
# Test: parent circuits composing subcircuits via the `subcircuit_rw` engine

The marker-free redo of `TestSubcircuit` + `TestLayouterSubcircuit`: every consumption pattern
those files prove through the absorption iffs, reproven here through the `subcircuit_rw` engine.
These are the acceptance gate for the engine AND the migration templates the C1 refactor pass
copies from.

Patterns covered, each with both directions:
- **region parent, bare call** (`regionParent`);
- **region parent, own op + call** (`regionParentWithOp`);
- **layouter parent** composing a native layouter child and a `toFormal`-lifted region child
  (`layouterParent`) — covers the layouter level AND the `toFormal` bridge in one;
- **chained children**, second input = first output (`chainedParent`) — the completeness
  direction here *consumes* the derived statement `h_spec_0` for output bookkeeping;
- **bare-`place`/`env` loop-lemma context** (`loopLemmaSoundness`) — the tactic's own
  unification, no discrimination tree (the scenario the `Placed`-keyed iffs miss).

## iff → engine, side by side

Soundness. iff:
```
simp only [circuit_norm, subcircuit_constraints_iff_soundness'] at hc
obtain ⟨_, hspec⟩ := hc          -- discard the leftover SubcircuitConstraints marker
have hvalid := hspec trivial trivial
```
engine:
```
simp only [circuit_norm] at hc
subcircuit_rw at hc              -- hc : EnvA → A → Spec, no marker conjunct
have hvalid := hc trivial trivial
```

Completeness. iff:
```
simp only [circuit_norm, subcircuit_constraints_iff_completeness'] at hwit ⊢
exact Or.inr ⟨hwit_call, trivial, trivial, h_input ▸ hpa⟩   -- pick the OR side
```
engine:
```
simp only [circuit_norm] at h_input ⊢
subcircuit_rw                    -- goal chunk → EnvA ∧ A ∧ PA (no ∨); h_spec_0 introduced
exact ⟨trivial, trivial, …⟩
```
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
    -- the goal chunk becomes a precondition subgoal `pre_0 : EnvA ∧ A ∧ PA`; `h_spec_0` (bare
    -- `Spec ∧ ProverSpec`) enters the residual context. The chunk itself is discharged.
    simp only [circuit_norm] at h_input hpa ⊢
    subcircuit_rw
    -- pre_0: `EnvA ∧ A ∧ PA` (default `True`s + the parent's `ProverAssumptions`)
    · exact ⟨trivial, trivial, by simpa only [circuit_norm, h_input] using hpa⟩
    -- residual: the chunk is discharged, only `True` remains
    · trivial

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
    · exact ⟨trivial, trivial, by simpa only [circuit_norm, h_input] using hpa⟩
    · trivial

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
    -- both goal chunks become precondition subgoals pre_0, pre_1 (op order); h_spec_0, h_spec_1
    -- enter the later contexts. The chunks are discharged; residual is `True ∧ True`.
    subcircuit_rw
    · exact ⟨trivial, trivial, by simpa only [circuit_norm, h_input] using hpa⟩
    · exact ⟨trivial, trivial, by simpa only [circuit_norm, h_input] using hpa⟩
    · exact ⟨trivial, trivial⟩

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
    -- engine introduces h_spec_0 (first child) and h_spec_1 (second child) from hwit's conjuncts,
    -- and strengthens both goal chunks to `EnvA ∧ A ∧ PA`
    subcircuit_rw
    -- pre_0: the first child's `EnvA ∧ A ∧ PA` (writes the precondition exactly ONCE — the
    -- finding #3 fix: no separate feeding of a premised h_spec_0).
    · exact ⟨trivial, trivial, h_input ▸ hpa⟩
    -- pre_1: the second child's `EnvA ∧ A ∧ PA`. Its chained ProverAssumption (its input IS the
    -- first's output) is discharged from `h_spec_0` (now a BARE `Spec ∧ ProverSpec` in context):
    -- `h_spec_0.2` is the first child's ProverSpec (`first_output = first_input`).
    · refine ⟨trivial, trivial, ?_⟩
      have hps0 := h_spec_0.2
      have hout : (passthrough.call config offset input_var).output self
          = passthrough.output config offset input_var self := rfl
      rw [hout] at *
      rw [hps0]; exact h_input ▸ hpa
    -- residual: both chunks discharged
    · trivial

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

end Halo2.Ironwood.Ecc.TestSubcircuitRw
