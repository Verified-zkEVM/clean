import Clean.Halo2.Subcircuit
import Clean.Ironwood.Ecc.WitnessPoint

/-!
# Test: parent circuits composing a subcircuit via the absorption-iff mechanism

Two PARENT `FormalRegionCircuit`s call the real child `Halo2.Ironwood.Ecc.WitnessPoint.point`
and are proven sound + complete by rewriting the child's constraint chunk to its contract:

- `parent` — the bare call. The chunk `Constraints ((point.call …).operations self)` is
  already the iff's LHS.
- `parentWithOp` — a parent with its OWN op (an `assignAdvice`) *and* the call. The real
  scaling test: `circuit_norm` decomposes the parent's binds via `operations_bind` → `++`
  and `RegionOperations.constraints_append`, dropping the `assignAdvice`'s `True` constraint
  and isolating the *folded* `(point.call …).operations self` chunk. The child is never
  unfolded — the iff keys on the opaque `call` boundary, not the child's `synthesize` ops.

Both parents, both directions, fire the iff **as part of `simp`**:
`simp only [circuit_norm, subcircuit_constraints_iff_soundness'/…_completeness']`.
`circuit_norm` normalizes the folded chunk's element type to the concrete
`Point (AssignedCell Fp)` (via `var_of_provableType`); the *primed* concrete-`α` iffs (in
`Subcircuit.lean`) are stated over exactly that spelling, so their discrimination-tree key
matches and the iff fires in the same `simp` pass. (The generic `Var`-`α` iffs miss the
post-`circuit_norm` chunk under simp — only `rw`'s full `isDefEq` catches them.)

The iff's surviving RHS chunk is wrapped in the opaque `SubcircuitConstraints` marker so the
rewrite happens exactly once (without it the iff re-fires on its own output). (This whole
hypothesis-rewriting step is what the eventual custom one-directional engine will subsume,
dropping the leftover marker/OR terms.)
-/

namespace Halo2.Ironwood.Ecc.TestSubcircuit

open Halo2 Halo2.Ironwood.Ecc

/-! ## Bare-call parent -/

/-- Parent circuit: run `witness_point` as a subcircuit, return its output point. Same
config/IO as the child, so the parent's contract is inherited. -/
def parent :
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
    -- `circuit_norm` normalizes the chunk's element type to concrete `Point (AssignedCell Fp)`;
    -- the concrete-`α` iff then fires *as part of the same simp* to expose the child's contract
    simp only [circuit_norm, FormalRegionCircuit.subcircuit_constraints_iff_soundness'] at hc
    obtain ⟨_, hspec⟩ := hc
    have hvalid := hspec trivial trivial
    rw [← h_output]; exact hvalid

  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    simp only [circuit_norm, FormalRegionCircuit.subcircuit_constraints_iff_completeness']
    -- simp normalized the eval spelling on both the goal and h_input to `Witgen.eval …`
    simp only [circuit_norm] at h_input
    exact Or.inr ⟨hwit, trivial, trivial, h_input ▸ hpa⟩

/-! ## Realistic parent: own op + subcircuit call -/

/-- Parent with its OWN operation (an `assignAdvice` at row `offset+1`) followed by the
`witness_point` subcircuit call. -/
def parentWithOp :
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
    -- circuit_norm decomposes the parent's `++` (the assignAdvice conjunct is `True`), isolates
    -- the folded call chunk, normalizes its element type, and — in the SAME simp — the concrete-`α`
    -- iff fires on it to expose the child's contract. The child is never unfolded.
    simp only [circuit_norm, FormalRegionCircuit.subcircuit_constraints_iff_soundness'] at hc
    obtain ⟨_, hspec⟩ := hc
    have hvalid := hspec trivial trivial
    rw [← h_output]; exact hvalid

  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    -- decompose the parent's own `ExtendsWitness`/`Constraints`; the call chunks stay folded,
    -- and the concrete-`α` iff fires on the goal chunk as part of the same simp
    simp only [circuit_norm, FormalRegionCircuit.subcircuit_constraints_iff_completeness'] at hwit ⊢
    simp only [circuit_norm] at h_input
    obtain ⟨_, hwit_call⟩ := hwit
    exact Or.inr ⟨hwit_call, trivial, trivial, h_input ▸ hpa⟩

end Halo2.Ironwood.Ecc.TestSubcircuit
