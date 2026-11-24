import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group13
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem round44PlanChecked : CompactPlan.observe (round44Operations 0) = round44Plan := by
  sha256_witness_unfold round44
  decide +kernel

theorem round45PlanChecked : CompactPlan.observe (round45Operations 0) = round45Plan := by
  sha256_witness_unfold round45
  decide +kernel

theorem round46PlanChecked : CompactPlan.observe (round46Operations 0) = round46Plan := by
  sha256_witness_unfold round46
  decide +kernel

theorem round47PlanChecked : CompactPlan.observe (round47Operations 0) = round47Plan := by
  sha256_witness_unfold round47
  decide +kernel

theorem round48PlanChecked : CompactPlan.observe (round48Operations 0) = round48Plan := by
  sha256_witness_unfold round48
  decide +kernel

theorem round49PlanChecked : CompactPlan.observe (round49Operations 0) = round49Plan := by
  sha256_witness_unfold round49
  decide +kernel

theorem round50PlanChecked : CompactPlan.observe (round50Operations 0) = round50Plan := by
  sha256_witness_unfold round50
  decide +kernel

theorem round51PlanChecked : CompactPlan.observe (round51Operations 0) = round51Plan := by
  sha256_witness_unfold round51
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
