import Clean.Halo2.Subcircuit
import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Ironwood.Ecc.WitnessPoint

/-!
# Test: parent circuits composing a subcircuit via the `subcircuit_rw` engine

Two PARENT `FormalRegionCircuit`s call the real child `Halo2.Ironwood.Ecc.WitnessPoint.point`
and are proven sound + complete by consuming the child's constraint chunk with the
`subcircuit_rw` engine (the mechanism that replaced the historical absorption iffs):

- `parent` — the bare call. The chunk `Constraints ((point.call …).operations self)` is the
  engine's leaf target directly.
- `parentWithOp` — a parent with its OWN op (an `assignAdvice`) *and* the call. The real
  scaling test: `circuit_norm` decomposes the parent's binds via `operations_bind` → `++` and
  `RegionOperations.constraints_append`, dropping the `assignAdvice`'s `True` constraint and
  isolating the *folded* `(point.call …).operations self` chunk. The child is never unfolded —
  the engine keys on the opaque `call` boundary (its own `isDefEq` matching), not the child's
  `synthesize` ops.

Both parents, both directions, go through the engine:
`subcircuit_rw at hc` (soundness) weakens the folded chunk to the child's `EnvA → A → Spec`;
`subcircuit_rw` (completeness) strengthens the goal chunk in place to `EnvA ∧ A ∧ PA` and
introduces the premised derived statement `h_spec_0 : EnvA → A → PA → Spec ∧ ProverSpec` — no
marker/OR leftovers to discard.
-/

namespace Halo2.Ironwood.Ecc.TestSubcircuit

/-! ## Bare-call parent -/

/-- Parent circuit: run `witness_point` as a subcircuit, return its output point. Same
config/IO as the child, so the parent's contract is inherited. -/
def parent :
    FormalRegionCircuit Fp (Column .advice × Column .advice) WitnessPoint.Config
      (Unconstrained Point) Point where
  configure := fun cols => WitnessPoint.configure cols.1 cols.2
  synthesize config offset input := WitnessPoint.point.call config offset input
  Spec _ output _ := output.Valid
  Witness := Point
  extract := fun config offset _ self env =>
    eval env ({ x := AssignedCell.of self offset config.x,
                y := AssignedCell.of self offset config.y } : Var Point Fp)
  ProverAssumptions input _ _ := input.Valid

  soundness := by
    intro config offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output _hE _hA hc
    -- `circuit_norm` normalizes the chunk's element type to concrete `Point (AssignedCell Fp)`;
    -- the engine then weakens the folded chunk to the child's `EnvA → A → Spec`.
    simp only [circuit_norm] at hc
    subcircuit_rw at hc
    exact h_output ▸ hc trivial trivial

  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    -- the goal chunk strengthens in place to its precondition bundle `EnvA ∧ A ∧ PA` (the
    -- premised `h_spec_0` enters the context, unused here).
    simp only [circuit_norm] at h_input hpa ⊢
    subcircuit_rw
    refine ⟨trivial, trivial, ?_⟩
    change (eval env input_var).Valid
    convert hpa using 2
    with_unfolding_all exact h_input

/-! ## Realistic parent: own op + subcircuit call -/

/-- Parent with its OWN operation (an `assignAdvice` at row `offset+1`) followed by the
`witness_point` subcircuit call. -/
def parentWithOp :
    FormalRegionCircuit Fp (Column .advice × Column .advice) WitnessPoint.Config
      (Unconstrained Point) Point where
  configure := fun cols => WitnessPoint.configure cols.1 cols.2
  synthesize config offset input := do
    let _ ← assignAdvice config.x (offset + 1) (Witgen.MOver.toIRScalar (Point.x <$> input))
    WitnessPoint.point.call config offset input
  Spec _ output _ := output.Valid
  Witness := Point
  extract := fun config offset _ self env =>
    eval env ({ x := AssignedCell.of self offset config.x,
                y := AssignedCell.of self offset config.y } : Var Point Fp)
  ProverAssumptions input _ _ := input.Valid

  soundness := by
    intro config offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output _hE _hA hc
    -- circuit_norm decomposes the parent's `++` (the assignAdvice conjunct is `True`) and isolates
    -- the folded call chunk; the engine walks the `True ∧ chunk` shape and weakens it. The child is
    -- never unfolded.
    simp only [circuit_norm] at hc
    subcircuit_rw at hc
    exact h_output ▸ hc trivial trivial

  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    -- decompose the parent's own `ExtendsWitness`/`Constraints`; the call chunk stays folded and
    -- the engine strengthens the goal chunk in place (locating the witness from `hwit`).
    simp only [circuit_norm] at hwit h_input hpa ⊢
    subcircuit_rw
    refine ⟨trivial, trivial, ?_⟩
    change (eval env input_var).Valid
    convert hpa using 2
    with_unfolding_all exact h_input

end Halo2.Ironwood.Ecc.TestSubcircuit
