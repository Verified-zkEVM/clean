import Clean.Ironwood.Action.TopLevel

/-!
# Reduced compilation input for the Orchard Action circuit

This module names the concrete compilation data used to prove the optional Action
shape. The lightweight top-level circuit does not import this shape machinery.
-/

namespace Zcash.Circuits.Action

open Halo2
open Circuit

/-- The formal Orchard Action circuit before top-level packaging. -/
def actionFormalCircuit : FormalCircuit Fp Unit Config unit unit :=
  circuit Specs.Sinsemilla.orchardGenerators orchardBases

/-- The concrete formal circuit used by the shape proof is the formal circuit
packaged by the opaque Action top-level circuit. -/
theorem actionCircuit_formalCircuit_eq :
    actionCircuit.formalCircuit = actionFormalCircuit := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

/-- The closed configure output used throughout Action compilation. -/
def actionConfig : Config :=
  (Circuit.configure Specs.Sinsemilla.orchardGenerators {}).1

/-- The closed Action operation stream supplied to the V1 floor planner. -/
def actionOperations : Operations Fp :=
  TopLevelCompilation.operations actionFormalCircuit

/-- The already-reduced, compositional synthesis summary published by Action. -/
def actionSynthesisSummary : FloorPlanner.SynthesisSummary :=
  Circuit.mainPostSynthesisSummary actionConfig

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
  simpa only [actionOperations, TopLevelCircuit.operations,
    actionCircuit_formalCircuit_eq] using actionCircuit.operationsCopyCellsAssigned

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
