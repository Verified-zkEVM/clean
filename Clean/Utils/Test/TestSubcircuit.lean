import Clean.Halo2.Subcircuit
import Clean.Ironwood.Ecc.WitnessPoint

/-!
# Test: parent circuits composing a subcircuit via the absorption-iff mechanism

We prove soundness + completeness for two PARENT `FormalRegionCircuit`s that call the real
child `Halo2.Ironwood.Ecc.WitnessPoint.point`:

- `parent` — the bare call.
- `parentWithOp` — a parent with its OWN op (an `assignAdvice`) *and* the subcircuit call.
  This is the real scaling test: the parent's binds decompose via `operations_bind` → `++`,
  `RegionOperations.constraints_append` (`@[circuit_norm]`) splits the parent conjunction
  around the *folded* `(child.call …).operations self` term, and the absorption iff matches
  it — all in ONE plain `simp only [circuit_norm, …iff]` with no hand-scoped simp set.

The iffs key on the opaque `(child.call …).operations self` boundary (not the child's
`synthesize` ops), so `circuit_norm` never unfolds the child. No `SubcircuitConstraints`
marker is needed — simp does not loop.
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
    -- PLAIN circuit_norm + the iff — one shot, no scoped set
    simp only [circuit_norm, FormalRegionCircuit.subcircuit_constraints_iff_soundness] at hc
    obtain ⟨_, hspec⟩ := hc
    have hvalid := hspec trivial trivial
    rw [← h_output]; exact hvalid

  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    simp only [circuit_norm, FormalRegionCircuit.subcircuit_constraints_iff_completeness]
    exact Or.inr ⟨hwit, trivial, trivial, h_input ▸ hpa⟩

/-! ## Realistic parent: own op + subcircuit call -/

/-- Parent with its OWN operation (an `assignAdvice` at row `offset+1`) followed by the
`witness_point` subcircuit call. -/
def parentWithOp :
    FormalRegionCircuit Fp (Column .advice × Column .advice) WitnessPoint.Config
      (Unconstrained Point) Point where
  configure := fun cols => WitnessPoint.configure cols.1 cols.2
  synthesize config offset input := do
    -- the parent's own op: assign something into its column (adds a `True` constraint)
    let _ ← assignAdvice config.x (offset + 1) (.ofFExpr input.x)
    -- the subcircuit call
    WitnessPoint.point.call config offset input
  Spec _ output _ := output.Valid
  ProverAssumptions input _ := input.Valid

  soundness := by
    intro config offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output _hE _hA hc
    -- circuit_norm decomposes the parent's `++` (the assignAdvice conjunct is `True`),
    -- isolates the folded call chunk, and the iff rewrites it — one shot, plain set.
    simp only [circuit_norm, FormalRegionCircuit.subcircuit_constraints_iff_soundness] at hc
    obtain ⟨_, hspec⟩ := hc
    have hvalid := hspec trivial trivial
    rw [← h_output]; exact hvalid

  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE _hA hpa
    refine ⟨?_, trivial⟩
    -- the parent's own `ExtendsWitness` (the assignAdvice) is exposed in `hwit`; the call's
    -- witness chunk stays folded. Split the goal's `++`, discharge each conjunct.
    simp only [circuit_norm, FormalRegionCircuit.subcircuit_constraints_iff_completeness] at hwit ⊢
    obtain ⟨hwit_assign, hwit_call⟩ := hwit
    refine ⟨hwit_assign, Or.inr ⟨hwit_call, trivial, trivial, h_input ▸ hpa⟩⟩

end Halo2.Ironwood.Ecc.TestSubcircuit
