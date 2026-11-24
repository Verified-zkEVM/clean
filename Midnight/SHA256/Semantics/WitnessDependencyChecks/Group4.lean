import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group3
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem expand28PlanChecked : CompactPlan.observe (expand28Operations 0) = expand28Plan := by
  sha256_witness_unfold expand28
  decide +kernel

theorem expand29PlanChecked : CompactPlan.observe (expand29Operations 0) = expand29Plan := by
  sha256_witness_unfold expand29
  decide +kernel

theorem expand30PlanChecked : CompactPlan.observe (expand30Operations 0) = expand30Plan := by
  sha256_witness_unfold expand30
  decide +kernel

theorem expand31PlanChecked : CompactPlan.observe (expand31Operations 0) = expand31Plan := by
  sha256_witness_unfold expand31
  decide +kernel

theorem expand32PlanChecked : CompactPlan.observe (expand32Operations 0) = expand32Plan := by
  sha256_witness_unfold expand32
  decide +kernel

theorem expand33PlanChecked : CompactPlan.observe (expand33Operations 0) = expand33Plan := by
  sha256_witness_unfold expand33
  decide +kernel

theorem expand34PlanChecked : CompactPlan.observe (expand34Operations 0) = expand34Plan := by
  sha256_witness_unfold expand34
  decide +kernel

theorem expand35PlanChecked : CompactPlan.observe (expand35Operations 0) = expand35Plan := by
  sha256_witness_unfold expand35
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
