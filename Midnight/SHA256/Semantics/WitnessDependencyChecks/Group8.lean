import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group7
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem expand60PlanChecked : CompactPlan.observe (expand60Operations 0) = expand60Plan := by
  sha256_witness_unfold expand60
  decide +kernel

theorem expand61PlanChecked : CompactPlan.observe (expand61Operations 0) = expand61Plan := by
  sha256_witness_unfold expand61
  decide +kernel

theorem expand62PlanChecked : CompactPlan.observe (expand62Operations 0) = expand62Plan := by
  sha256_witness_unfold expand62
  decide +kernel

theorem expand63PlanChecked : CompactPlan.observe (expand63Operations 0) = expand63Plan := by
  sha256_witness_unfold expand63
  decide +kernel

theorem round0PlanChecked : CompactPlan.observe (round0Operations 0) = round0Plan := by
  sha256_witness_unfold round0
  decide +kernel

theorem round1PlanChecked : CompactPlan.observe (round1Operations 0) = round1Plan := by
  sha256_witness_unfold round1
  decide +kernel

theorem round2PlanChecked : CompactPlan.observe (round2Operations 0) = round2Plan := by
  sha256_witness_unfold round2
  decide +kernel

theorem round3PlanChecked : CompactPlan.observe (round3Operations 0) = round3Plan := by
  sha256_witness_unfold round3
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
