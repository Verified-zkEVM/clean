import Clean.Halo2.Keygen.FloorPlanner.V1Correctness

namespace Halo2.FloorPlanner

open Halo2

variable {F : Type}

/-! # Constant allocation under the V1 floor planner -/

namespace V1

def rowOccupiedIn (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn) (row : ℕ) : Bool :=
  match shapes with
  | [] => false
  | shape :: rest =>
      (shape.columns.contains column &&
        decide (regionStarts.getD shape.index 0 ≤ row) &&
        decide (row < regionStarts.getD shape.index 0 + shape.rowCount)) ||
      rowOccupiedIn rest regionStarts column row

theorem rowOccupiedIn_eq_true_iff_mem_occupiedRowsIn
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (column : RegionColumn) (row : ℕ) :
    rowOccupiedIn shapes regionStarts column row = true ↔
      row ∈ occupiedRowsIn shapes regionStarts column := by
  induction shapes with
  | nil => simp [rowOccupiedIn, occupiedRowsIn]
  | cons shape rest inductionHypothesis =>
      by_cases hcolumn : column ∈ shape.columns
      · simp [rowOccupiedIn, occupiedRowsIn, hcolumn,
          inductionHypothesis]
      · simp [rowOccupiedIn, occupiedRowsIn, hcolumn,
          inductionHypothesis]

/-- Whether a placed region occupies `row` in `column`. -/
def rowOccupied (ops : Operations F) (column : RegionColumn) (row : ℕ) : Bool :=
  rowOccupiedIn (measureRegions ops) (starts ops) column row

def constantFreeRowsFrom (shapes : List RegionShape) (regionStarts : List ℕ)
    (endRow column : ℕ) : List ℕ :=
  (List.range endRow).filter fun row =>
    !rowOccupiedIn shapes regionStarts (.column .fixed column) row

private theorem filter_not_length_add_filter_length
    (values : List ℕ) (predicate : ℕ → Bool) :
    (values.filter fun value => !predicate value).length +
      (values.filter predicate).length = values.length := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      cases hpredicate : predicate value <;>
        simp [hpredicate] <;> omega

theorem constantFreeRowsFrom_length_lowerBound
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (endRow column : ℕ) :
    endRow - columnOccupiedLength shapes (.column .fixed column) ≤
      (constantFreeRowsFrom shapes regionStarts endRow column).length := by
  let occupied :=
    (List.range endRow).filter fun row =>
      rowOccupiedIn shapes regionStarts (.column .fixed column) row
  have hoccupiedNodup : occupied.Nodup :=
    List.Nodup.filter _ List.nodup_range
  have hsubset : occupied.toFinset ⊆
      occupiedRowsIn shapes regionStarts (.column .fixed column) := by
    intro row hrow
    rw [List.mem_toFinset, List.mem_filter] at hrow
    exact (rowOccupiedIn_eq_true_iff_mem_occupiedRowsIn
      shapes regionStarts (.column .fixed column) row).mp hrow.2
  have hoccupied : occupied.length ≤
      columnOccupiedLength shapes (.column .fixed column) := by
    rw [← List.toFinset_card_of_nodup hoccupiedNodup]
    exact (Finset.card_le_card hsubset).trans
      (occupiedRowsIn_card_le_columnOccupiedLength
        shapes regionStarts (.column .fixed column))
  have hpartition :
      (constantFreeRowsFrom shapes regionStarts endRow column).length +
        occupied.length = endRow := by
    simpa only [constantFreeRowsFrom, occupied, List.length_range] using
      filter_not_length_add_filter_length (List.range endRow)
        (fun row => rowOccupiedIn shapes regionStarts
          (.column .fixed column) row)
  omega

/-- Compositional lower bound on the total deferred-constant capacity.  The placement
end is bounded below by every column's exact occupied length; subtracting a constant
column's exact occupied length therefore counts slots guaranteed free in that column. -/
def constantCapacityLowerBound (ops : Operations F)
    (constantColumns : List ℕ) : ℕ :=
  let shapes := measureRegions ops
  let regionStarts := starts ops
  let endRow := placementEndFrom shapes regionStarts
  (constantColumns.map fun column =>
    endRow - columnOccupiedLength shapes (.column .fixed column)).sum

theorem mem_constantFreeRowsFrom_lt
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (endRow column row : ℕ)
    (hrow : row ∈ constantFreeRowsFrom shapes regionStarts endRow column) :
    row < endRow := by
  rw [constantFreeRowsFrom, List.mem_filter] at hrow
  exact List.mem_range.mp hrow.1

/-- Free rows of a concrete fixed column below V1's final region end, in ascending
order.  This is the extensional content of `Allocations.free_intervals` used by Halo 2
for deferred constants. -/
def constantFreeRows (ops : Operations F) (column : ℕ) : List ℕ :=
  let shapes := measureRegions ops
  let regionStarts := starts ops
  constantFreeRowsFrom shapes regionStarts
    (placementEndFrom shapes regionStarts) column

theorem constantCapacityLowerBound_le_positions_length
    (ops : Operations F) (constantColumns : List ℕ) :
    constantCapacityLowerBound ops constantColumns ≤
      (constantColumns.flatMap fun column =>
        (constantFreeRows ops column).map fun row => (column, row)).length := by
  rw [List.length_flatMap]
  apply List.sum_le_sum
  intro column hcolumn
  simp only [List.length_map, constantFreeRows]
  exact constantFreeRowsFrom_length_lowerBound
    (measureRegions ops) (starts ops)
    (placementEndFrom (measureRegions ops) (starts ops)) column

/--
V1 placement makes regions sharing any measured column row-disjoint by construction,
independently of the legacy candidate's sorting implementation.
-/
theorem starts_sharedColumnIntervalsDisjoint
    (ops : Operations F) :
    SharedColumnIntervalsDisjoint
      (measureRegions ops) (starts ops) := by
  rw [starts, planOperations_eq]
  exact planCandidate_measureRegions_sharedColumnIntervalsDisjoint ops

/-- Every column's exact compositional occupancy fits below V1's placement end. -/
theorem columnOccupiedLength_le_placementEnd
    (ops : Operations F) (column : RegionColumn) :
    columnOccupiedLength (measureRegions ops) column ≤
      V1.placementEnd ops := by
  exact columnOccupiedLength_le_placementEndFrom
    (measureRegions ops) (V1.starts ops) column
    (measureRegions_indices_nodup ops)
    (V1.starts_sharedColumnIntervalsDisjoint ops)

theorem synthesisSummary_maxColumnOccupancy_le_placementEnd
    (ops : Operations F) :
    (synthesisSummary ops).maxColumnOccupancy ≤ V1.placementEnd ops := by
  apply SynthesisSummary.maxColumnOccupancy_le
  intro column hcolumn
  rw [synthesisSummary_columnOccupancy_eq]
  exact V1.columnOccupiedLength_le_placementEnd ops column

theorem synthesisSummary_constantCapacityLowerBound_le
    (ops : Operations F) (constantColumns : List (Column .fixed)) :
    (synthesisSummary ops).constantCapacityLowerBound constantColumns ≤
      V1.constantCapacityLowerBound ops (constantColumns.map (·.index)) := by
  unfold SynthesisSummary.constantCapacityLowerBound
  unfold V1.constantCapacityLowerBound
  simp only [List.map_map]
  apply List.sum_le_sum
  intro column hcolumn
  rw [SynthesisSummary.fixedColumnOccupancy,
    synthesisSummary_columnOccupancy_eq]
  exact Nat.sub_le_sub_right
    (synthesisSummary_maxColumnOccupancy_le_placementEnd ops)
    (columnOccupiedLength (measureRegions ops) (.column .fixed column.index))

/-- The full V1 shared-column invariant implies its virtual-selector projection. -/
theorem starts_sharedSelectorIntervalsDisjoint
    (ops : Operations F) :
    SharedSelectorIntervalsDisjoint
      (measureRegions ops) (starts ops) := by
  intro left right hleft hright hindices selector
    hleftSelector hrightSelector
  exact starts_sharedColumnIntervalsDisjoint ops
    hleft hright hindices hleftSelector hrightSelector

/-! ### Constants allocation (`v1.rs:79-136`)

After planning, V1 assigns the collected `constrain_constant` values into the constants
fixed columns: `first_unassigned_row = max column unbounded_interval_start`
(`v1.rs:83-87`); `constant_positions` enumerates, per constants column in order, the FREE
rows in `[0, first_unassigned_row)` of that column's allocations (`v1.rs:102-108`); these are
zipped with `plan.constants` — the `constrain_constant` `(value, cell)` list collected in
region-then-body order during the assignment pass (`v1.rs:122`). -/

/-- `plan.constants` values in collection order (`assign_advice_from_constant` /
`constrain_constant` push `(constant, cell)`; we keep the constant), region-index order then
body order (`v1.rs` `AssignmentPass` runs regions in order). -/
def regionConstantValues (body : RegionOperations F) : List F :=
  match body with
  | [] => []
  | .constrainConstant _ value :: rest =>
      value :: regionConstantValues rest
  | _ :: rest => regionConstantValues rest

def constantValues (ops : Operations F) : List F :=
  (indexedRegions ops 0).1.flatMap fun (_, body) =>
    regionConstantValues body

theorem regionConstantValues_length
    (body : RegionOperations F) :
    (regionConstantValues body).length =
      (regionSynthesisSummary body).constantSiteCount := by
  induction body with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      cases operation <;>
        simp [regionConstantValues, regionSynthesisSummary,
          RegionSynthesisSummary.combine,
          RegionSynthesisSummary.ofOperation,
          regionOperationConstantSiteCount, inductionHypothesis,
          Nat.add_comm]

theorem constantValues_length
    (ops : Operations F) :
    (constantValues ops).length =
      (synthesisSummary ops).constantSiteCount := by
  have general : ∀ (operations : Operations F) (initial : ℕ),
      ((indexedRegions operations initial).1.flatMap fun (_, body) =>
        regionConstantValues body).length =
        (synthesisSummary operations).constantSiteCount := by
    intro operations
    induction operations with
    | nil => intro initial; rfl
    | cons operation rest inductionHypothesis =>
        intro initial
        cases operation with
        | region name body =>
            simp only [indexedRegions, List.flatMap_cons, List.length_append,
              synthesisSummary, SynthesisSummary.combine,
              SynthesisSummary.ofRegion, regionConstantValues_length]
            rw [inductionHypothesis]
        | constrainInstance cell column row =>
            simpa only [indexedRegions, synthesisSummary, SynthesisSummary.combine,
              SynthesisSummary.ofInstanceRow, Nat.zero_add] using
              inductionHypothesis initial
        | loadTable table values =>
            simpa only [indexedRegions, synthesisSummary, SynthesisSummary.combine,
              SynthesisSummary.ofTableValues, Nat.zero_add] using
              inductionHypothesis initial
  exact general ops 0

/-- `first_unassigned_row` (`v1.rs:83-87`): the max `unbounded_interval_start` over all
allocated columns. -/
def firstUnassignedRow (colAllocs : CircuitAllocations) : ℕ :=
  colAllocs.toList.foldl (fun m (_, a) => max m a.unboundedStart) 0

/-- Free rows of a fixed column's allocations within `[0, endRow)` (`constant_positions`'
`free_intervals(0, Some(first_unassigned_row))` expanded to individual rows). -/
def freeRows (colAllocs : CircuitAllocations) (colIdx endRow : ℕ) : List ℕ :=
  (colAllocs.getD (.column .fixed colIdx) #[]).freeIntervals 0 (some endRow)
    |>.flatMap fun (s, e?) => match e? with
      | some e => (List.range (e - s)).map (· + s)
      | none => []

/-- Every bounded constant-allocation position lies below its requested end row. -/
theorem mem_freeRows_lt
    (colAllocs : CircuitAllocations) (colIdx endRow row : ℕ)
    (hrow : row ∈ freeRows colAllocs colIdx endRow) :
    row < endRow := by
  rw [freeRows, List.mem_flatMap] at hrow
  obtain ⟨⟨intervalStart, intervalEnd⟩, hinterval, hrow⟩ := hrow
  cases intervalEnd with
  | none => simp at hrow
  | some intervalEnd =>
      rw [List.mem_map] at hrow
      obtain ⟨offset, hoffset, rfl⟩ := hrow
      have hoffsetBound := List.mem_range.mp hoffset
      have hintervalBound :=
        Allocations.freeIntervals_end_le
          (colAllocs.getD (.column .fixed colIdx) #[])
          0 endRow hinterval
      omega

/--
The V1 constants allocation `(value, constantsColIdx, row)`, retaining field values.

`constCols` is the list of constants fixed-column indices (`cs.constants`, from
`enable_constant`; Orchard uses a single column). This is the semantic compiler view:
field values stay in the field instead of making a round trip through a backend-specific
natural-number encoding.
-/
def constantAssignments (ops : Operations F) (constCols : List ℕ) :
    List (F × ℕ × ℕ) :=
  let shapes := measureRegions ops
  let regionStarts := starts ops
  let endRow := placementEndFrom shapes regionStarts
  let positions : List (ℕ × ℕ) := constCols.flatMap fun c =>
    (constantFreeRowsFrom shapes regionStarts endRow c).map fun row => (c, row)
  (positions.zip (constantValues ops)).map fun ((c, row), v) => (v, c, row)

private theorem constantFreeRowsFrom_nodup
    (shapes : List RegionShape) (regionStarts : List ℕ)
    (endRow column : ℕ) :
    (constantFreeRowsFrom shapes regionStarts endRow column).Nodup := by
  exact List.Nodup.filter _ List.nodup_range

private theorem constantPositions_nodup
    (ops : Operations F) (constCols : List ℕ)
    (hcolumns : constCols.Nodup) :
    (constCols.flatMap fun column =>
      (constantFreeRows ops column).map fun row => (column, row)).Nodup := by
  induction constCols with
  | nil => exact List.nodup_nil
  | cons column columns inductionHypothesis =>
      rw [List.nodup_cons] at hcolumns
      simp only [List.flatMap_cons]
      apply List.Nodup.append
      · apply List.Nodup.map
        · intro left right hequal
          exact congrArg Prod.snd hequal
        · exact constantFreeRowsFrom_nodup _ _ _ _
      · exact inductionHypothesis hcolumns.2
      · rw [List.disjoint_left]
        intro entry hcurrent hrest
        rw [List.mem_map] at hcurrent
        obtain ⟨row, _, rfl⟩ := hcurrent
        rw [List.mem_flatMap] at hrest
        obtain ⟨otherColumn, hotherColumn, hother⟩ := hrest
        rw [List.mem_map] at hother
        obtain ⟨otherRow, _, hentry⟩ := hother
        have hcolumn : column = otherColumn := by
          injection hentry.symm
        exact hcolumns.1 (hcolumn ▸ hotherColumn)

private theorem map_fst_zip_nodup
    {α β : Type}
    (left : List α) (right : List β)
    (hleft : left.Nodup) :
    ((left.zip right).map Prod.fst).Nodup := by
  induction left generalizing right with
  | nil => simp
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => simp
      | cons value rest =>
          rw [List.nodup_cons] at hleft
          simp only [List.zip_cons_cons, List.map_cons, List.nodup_cons]
          constructor
          · intro hhead
            rw [List.mem_map] at hhead
            obtain ⟨entry, hentry, hequal⟩ := hhead
            exact hleft.1 (hequal ▸ (List.of_mem_zip hentry).1)
          · exact inductionHypothesis rest hleft.2

/-- V1 never allocates two deferred constants at the same fixed cell when its configured
constants columns are unique. -/
theorem constantAssignments_cells_nodup
    (ops : Operations F) (constCols : List ℕ)
    (hcolumns : constCols.Nodup) :
    ((constantAssignments ops constCols).map fun assignment =>
      (assignment.2.1, assignment.2.2)).Nodup := by
  let shapes := measureRegions ops
  let regionStarts := starts ops
  let endRow := placementEndFrom shapes regionStarts
  let positions : List (ℕ × ℕ) := constCols.flatMap fun column =>
    (constantFreeRowsFrom shapes regionStarts endRow column).map fun row =>
      (column, row)
  have hpositions : positions.Nodup := by
    exact constantPositions_nodup ops constCols hcolumns
  simp only [constantAssignments, List.map_map]
  exact map_fst_zip_nodup positions (constantValues ops) hpositions

/-- The compositional capacity law is sufficient for V1 to allocate every deferred
constant site; `zip` therefore does not truncate the constant-value stream. -/
theorem constantValues_length_le_constantAssignments_length
    (ops : Operations F) (constantColumns : List ℕ)
    (hcapacity :
      (constantValues ops).length ≤
        constantCapacityLowerBound ops constantColumns) :
    (constantValues ops).length ≤
      (constantAssignments ops constantColumns).length := by
  let shapes := measureRegions ops
  let regionStarts := starts ops
  let endRow := placementEndFrom shapes regionStarts
  let positions : List (ℕ × ℕ) := constantColumns.flatMap fun column =>
    (constantFreeRowsFrom shapes regionStarts endRow column).map fun row =>
      (column, row)
  have hlower : constantCapacityLowerBound ops constantColumns ≤
      positions.length := by
    dsimp only [positions]
    rw [List.length_flatMap]
    apply List.sum_le_sum
    intro column hcolumn
    simp only [List.length_map]
    exact constantFreeRowsFrom_length_lowerBound
      shapes regionStarts endRow column
  have hpositions : (constantValues ops).length ≤ positions.length :=
    hcapacity.trans hlower
  have hlength :
      (constantAssignments ops constantColumns).length =
        min positions.length (constantValues ops).length := by
    simp [constantAssignments, positions, shapes, regionStarts, endRow]
  rw [hlength]
  omega

/-- A complete V1 allocation preserves the constant-value stream in order. -/
theorem constantAssignments_map_fst
    (ops : Operations F) (constantColumns : List ℕ)
    (hfull :
      (constantValues ops).length ≤
        (constantAssignments ops constantColumns).length) :
    (constantAssignments ops constantColumns).map Prod.fst =
      constantValues ops := by
  let shapes := measureRegions ops
  let regionStarts := starts ops
  let endRow := placementEndFrom shapes regionStarts
  let positions : List (ℕ × ℕ) := constantColumns.flatMap fun column =>
    (constantFreeRowsFrom shapes regionStarts endRow column).map fun row =>
      (column, row)
  have hpositions : (constantValues ops).length ≤ positions.length := by
    have hlength :
        (constantValues ops).length ≤
          min positions.length (constantValues ops).length := by
      simpa only [constantAssignments, positions, shapes, regionStarts,
        endRow, List.length_map, List.length_zip] using hfull
    omega
  simp only [constantAssignments, List.map_map]
  simpa only [Function.comp_apply] using
    List.map_snd_zip hpositions

/-- Every V1 constant allocation uses one of the configured constants columns. -/
theorem constantAssignments_column_mem
    (ops : Operations F) (constCols : List ℕ)
    {value : F} {column row : ℕ}
    (hassignment :
      (value, column, row) ∈ constantAssignments ops constCols) :
    column ∈ constCols := by
  let positions : List (ℕ × ℕ) := constCols.flatMap fun currentColumn =>
    (constantFreeRows ops currentColumn).map fun currentRow =>
      (currentColumn, currentRow)
  rw [constantAssignments, List.mem_map] at hassignment
  obtain ⟨⟨⟨foundColumn, foundRow⟩, foundValue⟩,
    hzipped, hequal⟩ := hassignment
  have hposition : (foundColumn, foundRow) ∈ positions :=
    (List.of_mem_zip hzipped).1
  dsimp only [positions] at hposition
  rw [List.mem_flatMap] at hposition
  obtain ⟨currentColumn, hcolumn, hposition⟩ := hposition
  rw [List.mem_map] at hposition
  obtain ⟨currentRow, _, hposition⟩ := hposition
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hposition
  obtain ⟨rfl, rfl, rfl⟩ := hequal
  exact hcolumn

/-- V1 allocates deferred constants only in cells left unoccupied by placed regions. -/
theorem constantAssignments_row_not_occupied
    (ops : Operations F) (constCols : List ℕ)
    {value : F} {column row : ℕ}
    (hassignment :
      (value, column, row) ∈ constantAssignments ops constCols) :
    rowOccupied ops (.column .fixed column) row = false := by
  let positions : List (ℕ × ℕ) := constCols.flatMap fun currentColumn =>
    (constantFreeRows ops currentColumn).map fun currentRow =>
      (currentColumn, currentRow)
  rw [constantAssignments, List.mem_map] at hassignment
  obtain ⟨⟨⟨foundColumn, foundRow⟩, foundValue⟩,
    hzipped, hequal⟩ := hassignment
  have hposition : (foundColumn, foundRow) ∈ positions :=
    (List.of_mem_zip hzipped).1
  dsimp only [positions] at hposition
  rw [List.mem_flatMap] at hposition
  obtain ⟨currentColumn, _, hposition⟩ := hposition
  rw [List.mem_map] at hposition
  obtain ⟨currentRow, hfree, hposition⟩ := hposition
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hposition
  obtain ⟨rfl, rfl, rfl⟩ := hequal
  rw [constantFreeRows, constantFreeRowsFrom,
    List.mem_filter] at hfree
  simpa [rowOccupied] using hfree.2

/-- Every V1 constant allocation lies below the final placed-region end. -/
theorem constantAssignments_row_lt_placementEnd
    (ops : Operations F) (constCols : List ℕ)
    {value : F} {column row : ℕ}
    (hassignment :
      (value, column, row) ∈ constantAssignments ops constCols) :
    row < placementEnd ops := by
  let positions : List (ℕ × ℕ) := constCols.flatMap fun currentColumn =>
    (constantFreeRows ops currentColumn).map fun currentRow =>
      (currentColumn, currentRow)
  rw [constantAssignments, List.mem_map] at hassignment
  obtain ⟨⟨⟨foundColumn, foundRow⟩, foundValue⟩,
    hzipped, hequal⟩ := hassignment
  have hposition : (foundColumn, foundRow) ∈ positions :=
    (List.of_mem_zip hzipped).1
  have hrow : foundRow < placementEnd ops := by
    dsimp only [positions] at hposition
    rw [List.mem_flatMap] at hposition
    obtain ⟨currentColumn, hcolumn, hposition⟩ := hposition
    rw [List.mem_map] at hposition
    obtain ⟨currentRow, hcurrentRow, hposition⟩ := hposition
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hposition
    exact mem_constantFreeRowsFrom_lt
      (measureRegions ops) (starts ops)
      (placementEndFrom (measureRegions ops) (starts ops))
      currentColumn currentRow hcurrentRow
  obtain ⟨rfl, rfl, rfl⟩ := hequal
  exact hrow


end V1
end Halo2.FloorPlanner
