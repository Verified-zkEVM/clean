import Clean.Ironwood.Action.PublicInput
import Clean.Ironwood.Action.RealBases

/-!
# Reduced compilation input for the Orchard Action circuit

This module names the closed Action circuit and the compact synthesis data consumed
by the top-level compiler.  It deliberately stops below `TopLevelCircuit`, so the
planner and shape proofs can justify the literal top-level package without circularly
reasoning through that package.
-/

namespace Zcash.Circuits.Action

open Halo2
open Circuit

/-- The formal Orchard Action circuit before top-level packaging. -/
def actionFormalCircuit : FormalCircuit Fp Unit Config unit unit :=
  circuit Specs.Sinsemilla.orchardGenerators orchardBases

/-- The closed configure output used throughout Action compilation. -/
def actionConfig : Config :=
  (Circuit.configure Specs.Sinsemilla.orchardGenerators {}).1

/-- The closed Action operation stream supplied to the V1 floor planner. -/
def actionOperations : Operations Fp :=
  TopLevelCompilation.operations actionFormalCircuit

/-- The already-reduced, compositional synthesis summary published by Action. -/
def actionSynthesisSummary : FloorPlanner.SynthesisSummary :=
  Circuit.mainPostSynthesisSummary actionConfig

/-- The closed Action circuit borrows no key-generation resources from a caller. -/
def actionNoCallerRequirements :
    actionFormalCircuit.keygenRequirements.EmptyAt () := by
  exact ⟨(), rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- Action's closed configure run borrows no queryable columns from a caller. -/
theorem actionQueryRequirements :
    actionFormalCircuit.queryRequirements () {} := by
  dsimp only [actionFormalCircuit, FormalCircuit.queryRequirements,
    Circuit.circuit, Circuit.elaboratedPost, Circuit.configureElaborated]
  trivial

/-- The published Action summary is exactly the summary of its operation stream. -/
theorem actionSynthesisSummary_eq_operations :
    actionSynthesisSummary = FloorPlanner.synthesisSummary actionOperations := by
  unfold actionSynthesisSummary actionOperations actionConfig actionFormalCircuit
  exact (Circuit.circuit_synthesisSummary_eq
    Specs.Sinsemilla.orchardGenerators orchardBases
    (TopLevelCompilation.config
      (circuit Specs.Sinsemilla.orchardGenerators orchardBases)) () 0).trans
    ((circuit Specs.Sinsemilla.orchardGenerators orchardBases).elaborated.synthesisSummary_eq
        (TopLevelCompilation.config
          (circuit Specs.Sinsemilla.orchardGenerators orchardBases)) () 0)

/-- Every copied cell in the closed Action operation stream is assigned. -/
theorem actionOperations_copyCellsAssigned :
    actionOperations.CopyCellsAssigned 0 [] := by
  exact actionFormalCircuit.operationsCopyCellsAssigned
    () () actionNoCallerRequirements

/-- Action's public instance layout occupies exactly ten rows. -/
theorem actionPublicInputLayout_usedRows_eq :
    PublicInputs.layout.usedRows = 10 := rfl

/-- Action's configured query depth requires exactly five blinding rows. -/
theorem actionConstraintSystem_blindingFactors_eq :
    (TopLevelCompilation.constraintSystem actionFormalCircuit).blindingFactors = 5 := by
  unfold actionFormalCircuit TopLevelCompilation.constraintSystem
  simp only [Circuit.circuit]
  set_option maxRecDepth 10000 in
    configure_norm

/-- Action's reduced configure summary records exact Halo 2 constraint degree nine. -/
theorem actionConstraintDegree_eq :
    TopLevelCompilation.constraintDegree actionFormalCircuit = 9 := by
  unfold TopLevelCompilation.constraintDegree actionFormalCircuit
  simp only [Circuit.circuit]
  configure_norm

/-- Action's closed configure run allocates exactly 56 selectors. -/
theorem actionNumSelectors_eq :
    (TopLevelCompilation.constraintSystem
      actionFormalCircuit).numSelectors = 56 := by
  simpa only [actionFormalCircuit, TopLevelCompilation.constraintSystem,
    Circuit.circuit] using
      Circuit.configure_finalCounts_numSelectors
        Specs.Sinsemilla.orchardGenerators

/-- The exact per-selector maximal gate degrees emitted by Action configuration. -/
def actionSelectorDegrees : Array ℕ :=
  #[3, 2, 0, 0, 3, 5, 4, 4, 6, 4, 4, 4, 4, 4, 4, 3, 5, 3,
    9, 9, 3, 5, 6, 6, 2, 0, 4, 3, 2, 0, 4, 3, 2, 3, 3, 3,
    2, 3, 3, 3, 3, 2, 3, 3, 3, 3, 3, 2, 3, 3, 3, 3, 2, 3, 3, 3]

set_option maxRecDepth 10000 in
/-- Selector-degree extraction agrees with Action's reduced literal summary. -/
theorem actionSelectorMaxDegrees_eq :
    selectorMaxDegrees
      (TopLevelCompilation.constraintSystem actionFormalCircuit) =
      actionSelectorDegrees := by
  unfold TopLevelCompilation.constraintSystem actionFormalCircuit
    actionSelectorDegrees
  simp only [Circuit.circuit]
  configure_norm

end Zcash.Circuits.Action
