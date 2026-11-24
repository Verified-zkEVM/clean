import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group5
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem expand44PlanChecked : CompactPlan.observe (expand44Operations 0) = expand44Plan := by
  sha256_witness_unfold expand44
  decide +kernel

theorem expand45PlanChecked : CompactPlan.observe (expand45Operations 0) = expand45Plan := by
  sha256_witness_unfold expand45
  decide +kernel

theorem expand46PlanChecked : CompactPlan.observe (expand46Operations 0) = expand46Plan := by
  sha256_witness_unfold expand46
  decide +kernel

theorem expand47PlanChecked : CompactPlan.observe (expand47Operations 0) = expand47Plan := by
  sha256_witness_unfold expand47
  decide +kernel

theorem expand48PlanChecked : CompactPlan.observe (expand48Operations 0) = expand48Plan := by
  sha256_witness_unfold expand48
  decide +kernel

theorem expand49PlanChecked : CompactPlan.observe (expand49Operations 0) = expand49Plan := by
  sha256_witness_unfold expand49
  decide +kernel

theorem expand50PlanChecked : CompactPlan.observe (expand50Operations 0) = expand50Plan := by
  sha256_witness_unfold expand50
  decide +kernel

theorem expand51PlanChecked : CompactPlan.observe (expand51Operations 0) = expand51Plan := by
  sha256_witness_unfold expand51
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
