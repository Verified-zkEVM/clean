import Clean.Halo2.Keygen.FloorPlanner.ConstantAllocation
import Clean.Halo2.Keygen.FloorPlanner.V1SortCorrectness

/-! Midnight's V1 placement order on Clean's first-fit allocator. Midnight's `v1/strategy.rs`
sorts with stable `sort_by_cached_key(advice_columns * row_count)` and reverses; Clean's
upstream V1 uses unstable pdqsort, so here the source region index breaks equal-area ties.
Deferred constants are placed in `Planner.lean`. -/

namespace Midnight.Chips.V1
open Halo2 Halo2.FloorPlanner

variable {F : Type}

/-- The original region index is the stable tie-breaker used by cached-key sorting. -/
def before (left right : RegionShape) : Bool :=
  decide (left.key < right.key ∨ left.key = right.key ∧ left.index ≤ right.index)

/-- Exact native ordering: descending advice area, then descending source index. -/
def sortedShapes (ops : Operations F) : List RegionShape :=
  ((measureRegions ops).mergeSort before).reverse

def plan (ops : Operations F) : List Nat × CircuitAllocations :=
  let (pairs, allocations) := slotIn (sortedShapes ops)
  ((Halo2.FloorPlanner.V1.sortPairsByIndex pairs).map Prod.snd, allocations)

def starts (ops : Operations F) : List Nat := (plan ops).1

end Midnight.Chips.V1
