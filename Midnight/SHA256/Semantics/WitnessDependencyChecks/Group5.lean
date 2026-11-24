import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group4
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem expand36PlanChecked : CompactPlan.observe (expand36Operations 0) = expand36Plan := by
  sha256_witness_unfold expand36
  decide +kernel

theorem expand37PlanChecked : CompactPlan.observe (expand37Operations 0) = expand37Plan := by
  sha256_witness_unfold expand37
  decide +kernel

theorem expand38PlanChecked : CompactPlan.observe (expand38Operations 0) = expand38Plan := by
  sha256_witness_unfold expand38
  decide +kernel

theorem expand39PlanChecked : CompactPlan.observe (expand39Operations 0) = expand39Plan := by
  sha256_witness_unfold expand39
  decide +kernel

theorem expand40PlanChecked : CompactPlan.observe (expand40Operations 0) = expand40Plan := by
  sha256_witness_unfold expand40
  decide +kernel

theorem expand41PlanChecked : CompactPlan.observe (expand41Operations 0) = expand41Plan := by
  sha256_witness_unfold expand41
  decide +kernel

theorem expand42PlanChecked : CompactPlan.observe (expand42Operations 0) = expand42Plan := by
  sha256_witness_unfold expand42
  decide +kernel

theorem expand43PlanChecked : CompactPlan.observe (expand43Operations 0) = expand43Plan := by
  sha256_witness_unfold expand43
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
