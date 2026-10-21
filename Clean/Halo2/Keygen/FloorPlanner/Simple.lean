import Clean.Halo2.Keygen.FloorPlanner.RegionShape

namespace Halo2.FloorPlanner

open Halo2

variable {F : Type}

namespace SimpleFloorPlanner

/-- `SingleChipLayouter::assign_region` placement (`single_pass.rs:86-106`): for each region
in stream order, `region_start = max` over the region's columns of that column's first-empty
row, then bump each column's first-empty row to `region_start + row_count`. Returns starts per
`assignRegion` index. -/
def starts (ops : Operations F) : List ℕ := Id.run do
  let mut cols : Std.HashMap RegionColumn ℕ := ∅
  let mut out : List ℕ := []
  for (idx, body) in (indexedRegions ops 0).1 do
    let shape := measureRegion idx body
    let mut rstart := 0
    for c in shape.columns do rstart := max rstart (cols.getD c 0)
    out := out ++ [rstart]
    for c in shape.columns do cols := cols.insert c (rstart + shape.rowCount)
  return out

end SimpleFloorPlanner

end Halo2.FloorPlanner
