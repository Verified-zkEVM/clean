import Midnight.Math.Witness.RegionPlan

/-! Proof-side exact equality for dependency plans. These named decisions compare
all coordinates and list structure without comparing the phantom field type.
They are activated only as local instances by certificate proof modules. -/
namespace Midnight.Math.Witness.PlanDecidableEquality
open Halo2

@[instance_reducible] def assignedCell {F : Type} : DecidableEq (AssignedCell F) := by
  intro left right
  cases left with | mk left =>
    cases right with | mk right =>
      exact decidable_of_iff (left = right) (by simp)

attribute [local instance] assignedCell

@[instance_reducible] def relativeAssignment {F : Type} : DecidableEq (RegionPlan.RelativeAssignment F) := by
  intro left right
  cases left with | mk lc lr ls =>
    cases right with | mk rc rr rs =>
      exact decidable_of_iff (lc = rc ∧ lr = rr ∧ ls = rs) (by simp)

end Midnight.Math.Witness.PlanDecidableEquality
