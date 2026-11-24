import Midnight.SHA256.Semantics.WitnessDependencyChecks.Group2
import Midnight.SHA256.Semantics.WitnessDependencyData
import Midnight.Math.Witness.PlanDecidableEquality

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 Midnight.Math.Witness

set_option Elab.async false
set_option maxRecDepth 10000
attribute [local instance] PlanDecidableEquality.assignedCell
  PlanDecidableEquality.relativeAssignment

theorem expand20PlanChecked : CompactPlan.observe (expand20Operations 0) = expand20Plan := by
  sha256_witness_unfold expand20
  decide +kernel

theorem expand21PlanChecked : CompactPlan.observe (expand21Operations 0) = expand21Plan := by
  sha256_witness_unfold expand21
  decide +kernel

theorem expand22PlanChecked : CompactPlan.observe (expand22Operations 0) = expand22Plan := by
  sha256_witness_unfold expand22
  decide +kernel

theorem expand23PlanChecked : CompactPlan.observe (expand23Operations 0) = expand23Plan := by
  sha256_witness_unfold expand23
  decide +kernel

theorem expand24PlanChecked : CompactPlan.observe (expand24Operations 0) = expand24Plan := by
  sha256_witness_unfold expand24
  decide +kernel

theorem expand25PlanChecked : CompactPlan.observe (expand25Operations 0) = expand25Plan := by
  sha256_witness_unfold expand25
  decide +kernel

theorem expand26PlanChecked : CompactPlan.observe (expand26Operations 0) = expand26Plan := by
  sha256_witness_unfold expand26
  decide +kernel

theorem expand27PlanChecked : CompactPlan.observe (expand27Operations 0) = expand27Plan := by
  sha256_witness_unfold expand27
  decide +kernel

end Midnight.SHA256.Semantics.WitnessCheckpoints
