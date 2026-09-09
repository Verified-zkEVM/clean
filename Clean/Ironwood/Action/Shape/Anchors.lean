import Clean.Ironwood.Action.Shape.Planner
import Clean.Ironwood.Action.TopLevel

/-!
# Lookup-selector anchors for the top-level Orchard Action circuit

These synthesis-placement facts are kept separate from the lightweight top-level
circuit package.
-/

namespace Zcash.Circuits.Action

open Halo2
open Circuit

/-- Action's reduced lookup-selector anchor equations are exactly those of its
top-level range-check configuration. -/
theorem actionCircuit_lookupSelectorAnchorRequirements_eq :
    actionCircuit.lookupSelectorAnchorRequirements =
      LookupRangeCheck.lookupSelectorAnchorRequirements
        actionConfig.lookupConfig := by
  rw [Internal.actionCircuit_eq_impl]
  rfl

/-- The concrete Action anchor satisfies the requirements published by the
opaque top-level circuit. -/
theorem actionCircuit_lookupSelectorAnchorRequirements_satisfied :
    SelectorAnchorRequirementsSatisfied
      actionCircuit.lookupSelectorAnchorRequirements
      (selectorAnchor actionConfig) := by
  rw [actionCircuit_lookupSelectorAnchorRequirements_eq]
  exact actionLookupSelectorAnchorRequirements_satisfied

end Zcash.Circuits.Action
