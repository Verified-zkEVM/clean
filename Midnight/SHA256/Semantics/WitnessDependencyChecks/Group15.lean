import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group14
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem round52PlanChecked : CompactPlan.observe (round52Operations 0) = round52Plan := by
  sha256_witness_unfold round52
  decide +kernel

theorem round53PlanChecked : CompactPlan.observe (round53Operations 0) = round53Plan := by
  sha256_witness_unfold round53
  decide +kernel

theorem round54PlanChecked : CompactPlan.observe (round54Operations 0) = round54Plan := by
  sha256_witness_unfold round54
  decide +kernel

theorem round55PlanChecked : CompactPlan.observe (round55Operations 0) = round55Plan := by
  sha256_witness_unfold round55
  decide +kernel

theorem round56PlanChecked : CompactPlan.observe (round56Operations 0) = round56Plan := by
  sha256_witness_unfold round56
  decide +kernel

theorem round57PlanChecked : CompactPlan.observe (round57Operations 0) = round57Plan := by
  sha256_witness_unfold round57
  decide +kernel

theorem round58PlanChecked : CompactPlan.observe (round58Operations 0) = round58Plan := by
  sha256_witness_unfold round58
  decide +kernel

theorem round59PlanChecked : CompactPlan.observe (round59Operations 0) = round59Plan := by
  sha256_witness_unfold round59
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
