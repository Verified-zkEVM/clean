import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group10
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem round20PlanChecked : CompactPlan.observe (round20Operations 0) = round20Plan := by
  sha256_witness_unfold round20
  decide +kernel

theorem round21PlanChecked : CompactPlan.observe (round21Operations 0) = round21Plan := by
  sha256_witness_unfold round21
  decide +kernel

theorem round22PlanChecked : CompactPlan.observe (round22Operations 0) = round22Plan := by
  sha256_witness_unfold round22
  decide +kernel

theorem round23PlanChecked : CompactPlan.observe (round23Operations 0) = round23Plan := by
  sha256_witness_unfold round23
  decide +kernel

theorem round24PlanChecked : CompactPlan.observe (round24Operations 0) = round24Plan := by
  sha256_witness_unfold round24
  decide +kernel

theorem round25PlanChecked : CompactPlan.observe (round25Operations 0) = round25Plan := by
  sha256_witness_unfold round25
  decide +kernel

theorem round26PlanChecked : CompactPlan.observe (round26Operations 0) = round26Plan := by
  sha256_witness_unfold round26
  decide +kernel

theorem round27PlanChecked : CompactPlan.observe (round27Operations 0) = round27Plan := by
  sha256_witness_unfold round27
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
