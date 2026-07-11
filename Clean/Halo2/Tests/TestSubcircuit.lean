import Clean.Halo2.Subcircuit
import Clean.Ironwood.Ecc.WitnessPoint

/-!
# Test: parent circuits composing a subcircuit via the absorption-iff mechanism

Two PARENT `FormalRegionCircuit`s call the real child `Halo2.Ironwood.Ecc.WitnessPoint.point`
and are proven sound + complete by rewriting the child's constraint chunk to its contract:

- `parent` — the bare call. The chunk `Constraints ((point.call …).operations self)` is
  already the iff's LHS, so `rw [iff]` fires directly.
- `parentWithOp` — a parent with its OWN op (an `assignAdvice`) *and* the call. The real
  scaling test: `circuit_norm` decomposes the parent's binds via `operations_bind` → `++`
  and `RegionOperations.constraints_append`, dropping the `assignAdvice`'s `True` constraint
  and isolating the *folded* `(point.call …).operations self` chunk; then `rw [iff]` fires on
  it. The child is never unfolded — the iff keys on the opaque `call` boundary, not the
  child's `synthesize` ops.

The iff's surviving RHS chunk is wrapped in the opaque `SubcircuitConstraints` marker so the
rewrite happens exactly once (without it the iff re-fires on its own output). We use `rw`,
not `simp`, for the iff step — `simp` is finicky firing an `↔` whose LHS it also indexes as a
subterm; `rw` matches it directly. (This whole hypothesis-rewriting step is what the eventual
custom one-directional engine will subsume, dropping the leftover marker/OR terms.)
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
    -- the chunk is already the iff's LHS; rewrite it to the child's contract
    rw [FormalRegionCircuit.subcircuit_constraints_iff_soundness] at hc
    obtain ⟨_, hspec⟩ := hc
    have hvalid := hspec trivial trivial
    rw [← h_output]; exact hvalid

  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    rw [FormalRegionCircuit.subcircuit_constraints_iff_completeness]
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
    -- circuit_norm decomposes the parent's `++` (the assignAdvice conjunct is `True`) and
    -- isolates the folded call chunk; then the iff rewrites it to the child's contract
    simp only [circuit_norm] at hc
    rw [FormalRegionCircuit.subcircuit_constraints_iff_soundness] at hc
    obtain ⟨_, hspec⟩ := hc
    have hvalid := hspec trivial trivial
    rw [← h_output]; exact hvalid

  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    -- decompose the parent's own `ExtendsWitness`/`Constraints`; the call chunks stay folded
    simp only [circuit_norm] at hwit ⊢
    rw [FormalRegionCircuit.subcircuit_constraints_iff_completeness]
    obtain ⟨_, hwit_call⟩ := hwit
    exact Or.inr ⟨hwit_call, trivial, trivial, h_input ▸ hpa⟩

end Halo2.Ironwood.Ecc.TestSubcircuit
