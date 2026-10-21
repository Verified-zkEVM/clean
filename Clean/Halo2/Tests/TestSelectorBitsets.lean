import Clean.Halo2.Keygen.SelectorBitsets

namespace Halo2.Tests.TestSelectorBitsets

open SelectorBitsets

-- Duplicate activations set a bit once; distinct selectors keep separate masks.
example : rowMask [(0, 2), (0, 2), (1, 3), (0, 5)] 0 = 36 := by
  decide +kernel

-- Regions can overlap in rows. Only equal selectors share a mask; empty regions
-- still consume a start index. Missing start entries retain getD's zero default.
example : placedRowMasks [4, 10, 5] 0
    [[(0, 1), (1, 0)], [], [(1, 0)], [(0, 7)]] 3 = #[160, 48, 0] := by
  decide +kernel

example : placedRowMasks [4, 10, 5] 1 [[(0, 1)], [(0, 0)]] 1 = #[2080] := by
  decide +kernel

example : selectorActivationsConflict [(0, 2), (1, 2)] 0 1 = true := by
  rw [selectorActivationsConflict_eq]
  decide +kernel

example : selectorActivationsConflict [(0, 2), (1, 3)] 0 1 = false := by
  rw [selectorActivationsConflict_eq]
  decide +kernel

-- Same-row selectors need separate columns; disjoint ones can be packed together.
example : selectorColumnCountWith [0, 1, 2] 3 (fun _ => 1)
    (fun a b => (#[4, 4, 8] : Array Nat)[a]! &&& (#[4, 4, 8] : Array Nat)[b]! != 0) = 2 := by
  decide +kernel

end Halo2.Tests.TestSelectorBitsets
