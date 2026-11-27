module

public import Clean.Halo2.Keygen.FloorPlanner.RegionShape

@[expose] public section

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

/-- The Simple planner's state with a constants column: first-empty rows, region starts and
the constants placed so far as `(value, column, row)`. -/
structure Plan (F : Type) where
  columns : Std.HashMap RegionColumn ℕ := ∅
  starts : List ℕ := []
  constants : List (F × ℕ × ℕ) := []

/-- One `assign_region` with Rust's constants pass (`single_pass.rs:176-235`): place the
region as `starts` does, then put its queued constants on consecutive rows of the constants
column from that column's first-empty row, which region placement shares. -/
def planStep (constant : ℕ) (state : Plan F) (region : ℕ × RegionOperations F) : Plan F :=
  let shape := measureRegion region.1 region.2
  let start := shape.columns.foldl (fun row c => max row (state.columns.getD c 0)) 0
  let columns := shape.columns.foldl (fun cols c => cols.insert c (start + shape.rowCount))
    state.columns
  let key := RegionColumn.column .fixed constant
  let next := columns.getD key 0
  let values := regionConstantValues region.2
  { columns := columns.insert key (next + values.length)
    starts := state.starts ++ [start]
    constants := state.constants ++ values.zipIdx.map fun (value, j) => (value, constant, next + j) }

/-- Placement and constants when `constants[0]` is fixed column `constant`. Rust uses no other
constants column. -/
def plan (constant : ℕ) (ops : Operations F) : Plan F :=
  (indexedRegions ops 0).1.foldl (planStep constant) {}

end SimpleFloorPlanner

end Halo2.FloorPlanner
