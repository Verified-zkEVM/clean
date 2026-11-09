import Clean.Halo2.Keygen.SelectorBitsets
import Clean.Ironwood.Action.Shape.PlannerTrace

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner SelectorBitsets

/-- The existing greedy selector packer uses exactly fifteen columns. The masks are
computed from the reduced region summaries and the proved V1 starts; generic bitset
correctness connects this computation to the original activation-list semantics. -/
theorem actionSelectorColumnCount_eq :
    selectorColumnCountWith (List.range 56) 9
      (fun selector => actionSelectorDegrees[selector]!)
      (selectorActivationsConflict actionReducedSelectorActivations) = 15 := by
  let masks := placedRowMasks actionReducedRegionStarts 0
    actionSynthesisSummary.regionSelectorActivations 56
  trans selectorColumnCountWith (List.range 56) 9
    (fun selector => actionSelectorDegrees[selector]!)
    (fun left right => masks[left]! &&& masks[right]! != 0)
  · apply selectorColumnCountWith_congr_on
    · intro _ _; rfl
    · intro left hLeft right hRight
      have hLeftLt := List.mem_range.mp (List.mem_of_mem_filter hLeft)
      have hRightLt := List.mem_range.mp (List.mem_of_mem_filter hRight)
      rw [getElem!_placedRowMasks _ _ _ _ _ hLeftLt,
        getElem!_placedRowMasks _ _ _ _ _ hRightLt,
        selectorActivationsConflict_eq, actionReducedSelectorActivations]
  · decide +kernel

end Zcash.Circuits.Action
