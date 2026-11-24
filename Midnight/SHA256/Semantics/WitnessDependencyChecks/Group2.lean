import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group1
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem prepare12PlanChecked : CompactPlan.observe (prepare12Operations 0) = prepare12Plan := by
  decide +kernel

theorem prepare13PlanChecked : CompactPlan.observe (prepare13Operations 0) = prepare13Plan := by
  decide +kernel

theorem prepare14PlanChecked : CompactPlan.observe (prepare14Operations 0) = prepare14Plan := by
  decide +kernel

theorem prepare15PlanChecked : CompactPlan.observe (prepare15Operations 0) = prepare15Plan := by
  decide +kernel

theorem expand16PlanChecked : CompactPlan.observe (expand16Operations 0) = expand16Plan := by
  sha256_witness_unfold expand16
  decide +kernel

theorem expand17PlanChecked : CompactPlan.observe (expand17Operations 0) = expand17Plan := by
  sha256_witness_unfold expand17
  decide +kernel

theorem expand18PlanChecked : CompactPlan.observe (expand18Operations 0) = expand18Plan := by
  sha256_witness_unfold expand18
  decide +kernel

theorem expand19PlanChecked : CompactPlan.observe (expand19Operations 0) = expand19Plan := by
  sha256_witness_unfold expand19
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
