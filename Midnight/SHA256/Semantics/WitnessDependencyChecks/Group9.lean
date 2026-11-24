import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group8
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem round4PlanChecked : CompactPlan.observe (round4Operations 0) = round4Plan := by
  sha256_witness_unfold round4
  decide +kernel

theorem round5PlanChecked : CompactPlan.observe (round5Operations 0) = round5Plan := by
  sha256_witness_unfold round5
  decide +kernel

theorem round6PlanChecked : CompactPlan.observe (round6Operations 0) = round6Plan := by
  sha256_witness_unfold round6
  decide +kernel

theorem round7PlanChecked : CompactPlan.observe (round7Operations 0) = round7Plan := by
  sha256_witness_unfold round7
  decide +kernel

theorem round8PlanChecked : CompactPlan.observe (round8Operations 0) = round8Plan := by
  sha256_witness_unfold round8
  decide +kernel

theorem round9PlanChecked : CompactPlan.observe (round9Operations 0) = round9Plan := by
  sha256_witness_unfold round9
  decide +kernel

theorem round10PlanChecked : CompactPlan.observe (round10Operations 0) = round10Plan := by
  sha256_witness_unfold round10
  decide +kernel

theorem round11PlanChecked : CompactPlan.observe (round11Operations 0) = round11Plan := by
  sha256_witness_unfold round11
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
