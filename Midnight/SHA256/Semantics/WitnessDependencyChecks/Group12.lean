import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group11
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem round28PlanChecked : CompactPlan.observe (round28Operations 0) = round28Plan := by
  sha256_witness_unfold round28
  decide +kernel

theorem round29PlanChecked : CompactPlan.observe (round29Operations 0) = round29Plan := by
  sha256_witness_unfold round29
  decide +kernel

theorem round30PlanChecked : CompactPlan.observe (round30Operations 0) = round30Plan := by
  sha256_witness_unfold round30
  decide +kernel

theorem round31PlanChecked : CompactPlan.observe (round31Operations 0) = round31Plan := by
  sha256_witness_unfold round31
  decide +kernel

theorem round32PlanChecked : CompactPlan.observe (round32Operations 0) = round32Plan := by
  sha256_witness_unfold round32
  decide +kernel

theorem round33PlanChecked : CompactPlan.observe (round33Operations 0) = round33Plan := by
  sha256_witness_unfold round33
  decide +kernel

theorem round34PlanChecked : CompactPlan.observe (round34Operations 0) = round34Plan := by
  sha256_witness_unfold round34
  decide +kernel

theorem round35PlanChecked : CompactPlan.observe (round35Operations 0) = round35Plan := by
  sha256_witness_unfold round35
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
