import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group12
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem round36PlanChecked : CompactPlan.observe (round36Operations 0) = round36Plan := by
  sha256_witness_unfold round36
  decide +kernel

theorem round37PlanChecked : CompactPlan.observe (round37Operations 0) = round37Plan := by
  sha256_witness_unfold round37
  decide +kernel

theorem round38PlanChecked : CompactPlan.observe (round38Operations 0) = round38Plan := by
  sha256_witness_unfold round38
  decide +kernel

theorem round39PlanChecked : CompactPlan.observe (round39Operations 0) = round39Plan := by
  sha256_witness_unfold round39
  decide +kernel

theorem round40PlanChecked : CompactPlan.observe (round40Operations 0) = round40Plan := by
  sha256_witness_unfold round40
  decide +kernel

theorem round41PlanChecked : CompactPlan.observe (round41Operations 0) = round41Plan := by
  sha256_witness_unfold round41
  decide +kernel

theorem round42PlanChecked : CompactPlan.observe (round42Operations 0) = round42Plan := by
  sha256_witness_unfold round42
  decide +kernel

theorem round43PlanChecked : CompactPlan.observe (round43Operations 0) = round43Plan := by
  sha256_witness_unfold round43
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
