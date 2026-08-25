import Clean.Halo2.Keygen.FloorPlanner.Allocations
import Clean.Halo2.Keygen.Pdqsort

namespace Halo2.FloorPlanner

open Halo2

variable {F : Type}

/-! # V1 floor-planner implementation -/

namespace V1

/-- Restore region-index order after largest-region-first slotting. -/
def sortPairsByIndex (pairs : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  pairs.insertionSort fun left right => left.1 ≤ right.1
/-- `slot_in_biggest_advice_first` (`strategy.rs:198-242`) then un-sort: sort the shapes by
`key` (legacy pdqsort), reverse (biggest advice area first), slot them in, and re-order the
resulting starts back to region-index order. Returns `(starts, finalAllocations)`. -/
def planCandidate (shapes : List RegionShape) : List ℕ × CircuitAllocations :=
  let sortedDesc := (Pdqsort.quicksort shapes.toArray (fun a b => a.key < b.key)).reverse
  let (pairs, colAllocs) := slotIn sortedDesc.toList
  let byIndex := sortPairsByIndex pairs
  (byIndex.map (·.2), colAllocs)
/-- Apply the proven-safe V1 planner to the regions measured from an operation stream.
Keep the planner opaque to type-class inference and expose its behavior propositionally. -/
irreducible_def planOperations
    (operations : Operations F) : List ℕ × CircuitAllocations :=
  planCandidate (measureRegions operations)

theorem planOperations_eq
    (operations : Operations F) :
    planOperations operations = planCandidate (measureRegions operations) := by
  rw [planOperations]

/-- The V1 region starts, per `assignRegion` index, from the operation stream. -/
def starts (ops : Operations F) : List ℕ := (planOperations ops).1

end V1
end Halo2.FloorPlanner
