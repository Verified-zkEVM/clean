import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group15
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem round60PlanChecked : CompactPlan.observe (round60Operations 0) = round60Plan := by
  sha256_witness_unfold round60
  decide +kernel

theorem round61PlanChecked : CompactPlan.observe (round61Operations 0) = round61Plan := by
  sha256_witness_unfold round61
  decide +kernel

theorem round62PlanChecked : CompactPlan.observe (round62Operations 0) = round62Plan := by
  sha256_witness_unfold round62
  decide +kernel

theorem round63PlanChecked : CompactPlan.observe (round63Operations 0) = round63Plan := by
  sha256_witness_unfold round63
  decide +kernel

theorem feedforwardPlanChecked : CompactPlan.observe (feedforwardOperations 0) = feedforwardPlan := by
  decide +kernel

theorem serialize0PlanChecked : CompactPlan.observe (serialize0Operations 0) = serialize0Plan := by
  decide +kernel

theorem serialize1PlanChecked : CompactPlan.observe (serialize1Operations 0) = serialize1Plan := by
  decide +kernel

theorem serialize2PlanChecked : CompactPlan.observe (serialize2Operations 0) = serialize2Plan := by
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
