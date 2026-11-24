import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group9
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem round12PlanChecked : CompactPlan.observe (round12Operations 0) = round12Plan := by
  sha256_witness_unfold round12
  decide +kernel

theorem round13PlanChecked : CompactPlan.observe (round13Operations 0) = round13Plan := by
  sha256_witness_unfold round13
  decide +kernel

theorem round14PlanChecked : CompactPlan.observe (round14Operations 0) = round14Plan := by
  sha256_witness_unfold round14
  decide +kernel

theorem round15PlanChecked : CompactPlan.observe (round15Operations 0) = round15Plan := by
  sha256_witness_unfold round15
  decide +kernel

theorem round16PlanChecked : CompactPlan.observe (round16Operations 0) = round16Plan := by
  sha256_witness_unfold round16
  decide +kernel

theorem round17PlanChecked : CompactPlan.observe (round17Operations 0) = round17Plan := by
  sha256_witness_unfold round17
  decide +kernel

theorem round18PlanChecked : CompactPlan.observe (round18Operations 0) = round18Plan := by
  sha256_witness_unfold round18
  decide +kernel

theorem round19PlanChecked : CompactPlan.observe (round19Operations 0) = round19Plan := by
  sha256_witness_unfold round19
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
