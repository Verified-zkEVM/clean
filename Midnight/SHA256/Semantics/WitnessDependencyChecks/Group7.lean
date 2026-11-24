import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group6
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem expand52PlanChecked : CompactPlan.observe (expand52Operations 0) = expand52Plan := by
  sha256_witness_unfold expand52
  decide +kernel

theorem expand53PlanChecked : CompactPlan.observe (expand53Operations 0) = expand53Plan := by
  sha256_witness_unfold expand53
  decide +kernel

theorem expand54PlanChecked : CompactPlan.observe (expand54Operations 0) = expand54Plan := by
  sha256_witness_unfold expand54
  decide +kernel

theorem expand55PlanChecked : CompactPlan.observe (expand55Operations 0) = expand55Plan := by
  sha256_witness_unfold expand55
  decide +kernel

theorem expand56PlanChecked : CompactPlan.observe (expand56Operations 0) = expand56Plan := by
  sha256_witness_unfold expand56
  decide +kernel

theorem expand57PlanChecked : CompactPlan.observe (expand57Operations 0) = expand57Plan := by
  sha256_witness_unfold expand57
  decide +kernel

theorem expand58PlanChecked : CompactPlan.observe (expand58Operations 0) = expand58Plan := by
  sha256_witness_unfold expand58
  decide +kernel

theorem expand59PlanChecked : CompactPlan.observe (expand59Operations 0) = expand59Plan := by
  sha256_witness_unfold expand59
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
