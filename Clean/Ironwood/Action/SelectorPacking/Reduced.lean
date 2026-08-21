import Clean.Ironwood.Action.SelectorPacking.Rows5

/-!
# Exact reduced selector conflicts for Orchard Action

The row-run summary is much smaller than the placed activation stream. The generic
selector-packing congruence theorem lets key generation consume this representation
without changing the algorithm it models.
-/

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

/-- Pairwise selector conflict computed from Action's exact row-run summary. -/
def actionReducedSelectorConflict (left right : ℕ) : Bool :=
  (expandSelectorRowRuns (actionSelectorRowRuns left)).any fun row =>
    row ∈ expandSelectorRowRuns (actionSelectorRowRuns right)

private theorem actionSelectorActivationRows_eq_of_nonzeroDegree
    (selector : ℕ) (hselector : selector < 56)
    (hdegree : actionSelectorDegrees[selector]! ≠ 0) :
    selectorActivationRows actionReducedSelectorActivations selector =
      expandSelectorRowRuns (actionSelectorRowRuns selector) := by
  interval_cases selector <;>
    simp_all only [actionSelectorDegrees, action_selector_rows_norm]
  all_goals simp at hdegree

/-- On selectors participating in greedy packing, dense activation conflicts agree
with the exact reduced row-run computation. -/
theorem actionSelectorConflict_eq_of_nonzeroDegrees
    (left right : ℕ) (hleft : left < 56) (hright : right < 56)
    (hleftDegree : actionSelectorDegrees[left]! ≠ 0)
    (hrightDegree : actionSelectorDegrees[right]! ≠ 0) :
    selectorActivationsConflict actionReducedSelectorActivations left right =
      actionReducedSelectorConflict left right := by
  rw [selectorActivationsConflict_eq_any_rows,
    actionSelectorActivationRows_eq_of_nonzeroDegree left hleft hleftDegree,
    actionSelectorActivationRows_eq_of_nonzeroDegree right hright hrightDegree]
  rfl

end Zcash.Circuits.Action
