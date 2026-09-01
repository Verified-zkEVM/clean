import Clean.Ironwood.Action.Shape
import Clean.Ironwood.Action.TopLevel

/-!
# The published Orchard Action circuit shape

This module attaches the expensive, fully reduced shape certificate to the otherwise
lightweight top-level Action circuit. Consumers that only need the circuit semantics
do not need to import the planner and selector-packing proofs behind this instance.
-/

namespace Zcash.Circuits.Action

open Halo2

instance : TopLevelShape actionCircuit where
  shape := actionShape
  shape_eq := by
    rw [Internal.actionCircuit_eq_impl]
    exact actionShape_eq_compiled

/-- The opaque Action package publishes the fully reduced circuit shape. -/
@[simp] theorem actionCircuit_shape_eq :
    actionCircuit.shape = actionShape := rfl

/-- Action's closed configure run equality-enables fifteen distinct columns. -/
theorem actionCircuit_permutationColumnCount_eq :
    actionCircuit.permutationColumnCount = 15 := by
  rw [TopLevelCircuit.permutationColumnCount, actionCircuit_shape_eq]
  rfl

end Zcash.Circuits.Action
