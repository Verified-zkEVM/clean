import Clean.Halo2.Keygen.FloorPlanner.Allocations

namespace Halo2.FloorPlanner

open Halo2

variable {F : Type}

/-! ## Selector-free V1 placement -/

namespace V1

open Halo2 FloorPlanner

theorem selector_mem_selectorColumns_iff
    (selector : ℕ) (columns : List RegionColumn) :
    RegionColumn.selector selector ∈ selectorColumns columns ↔
      RegionColumn.selector selector ∈ columns := by
  simp [selectorColumns]

theorem column_mem_physicalColumns_iff
    (kind : ColumnKind) (index : ℕ) (columns : List RegionColumn) :
    RegionColumn.column kind index ∈ physicalColumns columns ↔
      RegionColumn.column kind index ∈ columns := by
  simp [physicalColumns]

theorem exists_selector_of_mem_selectorColumns
    {column : RegionColumn} {columns : List RegionColumn}
    (hcolumn : column ∈ selectorColumns columns) :
    ∃ selector, column = .selector selector := by
  rw [selectorColumns, List.mem_filter] at hcolumn
  rcases column with ⟨kind, index⟩ | selector
  · simp at hcolumn
  · exact ⟨selector, rfl⟩

theorem exists_column_of_mem_physicalColumns
    {column : RegionColumn} {columns : List RegionColumn}
    (hcolumn : column ∈ physicalColumns columns) :
    ∃ kind index, column = .column kind index := by
  rw [physicalColumns, List.mem_filter] at hcolumn
  rcases column with ⟨kind, index⟩ | selector
  · exact ⟨kind, index, rfl⟩
  · simp at hcolumn

/-- Every interval allocated to `dominated` is also allocated to `dominant`. -/
def ColumnAllocationsDominate (allocations : CircuitAllocations)
    (dominant dominated : RegionColumn) : Prop :=
  ∀ interval,
    interval ∈ (allocations.getD dominated #[]).toList →
      interval ∈ (allocations.getD dominant #[]).toList

theorem ColumnAllocationsDominate.fits
    {allocations : CircuitAllocations} {dominant dominated : RegionColumn}
    (hdominate : ColumnAllocationsDominate allocations dominant dominated)
    {start length : ℕ}
    (hfits : (allocations.getD dominant #[]).Fits start length) :
    (allocations.getD dominated #[]).Fits start length := by
  intro interval hinterval
  exact hfits interval (hdominate interval hinterval)

/-- A fixed physical anchor column participates whenever one summary uses a
selector. -/
def SummarySelectorsAnchoredBy
    (summary : RegionShapeSummary) (anchor : ℕ → RegionColumn) : Prop :=
  ∀ selector,
    RegionColumn.selector selector ∈ summary.columns →
      anchor selector ∈ physicalColumns summary.columns

/-- Every summary in a reduced synthesis footprint satisfies the selector-anchor
law. -/
def SelectorAnchoredBy (summaries : List RegionShapeSummary)
    (anchor : ℕ → RegionColumn) : Prop :=
  summaries.Forall (fun summary => SummarySelectorsAnchoredBy summary anchor)

theorem SummarySelectorsAnchoredBy.ofColumns
    {columns : List RegionColumn}
    {rowCount constantSiteCount instanceRowExtent lookupActivationCount : ℕ}
    {anchor : ℕ → RegionColumn}
    (hanchor : ∀ selector, .selector selector ∈ columns →
      anchor selector ∈ physicalColumns columns) :
    SummarySelectorsAnchoredBy
      (RegionSynthesisSummary.ofColumns columns rowCount constantSiteCount
        instanceRowExtent lookupActivationCount
        |>.toRegionShapeSummary)
      anchor := by
  intro selector hselector
  rw [RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.ofColumns_columns]
  rw [RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.ofColumns_columns,
    mem_unionColumns_iff] at hselector
  have hsource := hanchor selector (by simpa using hselector)
  obtain ⟨kind, index, heq⟩ := exists_column_of_mem_physicalColumns hsource
  have hphysical : .column kind index ∈ physicalColumns columns := by
    simpa only [← heq] using hsource
  rw [heq, column_mem_physicalColumns_iff, mem_unionColumns_iff]
  exact Or.inr ((column_mem_physicalColumns_iff kind index columns).mp hphysical)

theorem SummarySelectorsAnchoredBy.combine
    {left right : RegionSynthesisSummary} {anchor : ℕ → RegionColumn}
    (hleft : SummarySelectorsAnchoredBy left.toRegionShapeSummary anchor)
    (hright : SummarySelectorsAnchoredBy right.toRegionShapeSummary anchor) :
    SummarySelectorsAnchoredBy (left.combine right).toRegionShapeSummary anchor := by
  intro selector hselector
  rw [RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.combine_columns, mem_unionColumns_iff] at hselector
  rcases hselector with hselector | hselector
  · have hanchor := hleft selector (by simpa using hselector)
    have hanchor' : anchor selector ∈ physicalColumns left.columns := by
      simpa only [RegionSynthesisSummary.toRegionShapeSummary_columns] using hanchor
    obtain ⟨kind, index, heq⟩ := exists_column_of_mem_physicalColumns hanchor
    have hphysical : .column kind index ∈ physicalColumns left.columns := by
      simpa only [← heq] using hanchor'
    rw [heq, RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns, column_mem_physicalColumns_iff,
      mem_unionColumns_iff]
    exact Or.inl
      ((column_mem_physicalColumns_iff kind index left.columns).mp hphysical)
  · have hanchor := hright selector (by simpa using hselector)
    have hanchor' : anchor selector ∈ physicalColumns right.columns := by
      simpa only [RegionSynthesisSummary.toRegionShapeSummary_columns] using hanchor
    obtain ⟨kind, index, heq⟩ := exists_column_of_mem_physicalColumns hanchor
    have hphysical : .column kind index ∈ physicalColumns right.columns := by
      simpa only [← heq] using hanchor'
    rw [heq, RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns, column_mem_physicalColumns_iff,
      mem_unionColumns_iff]
    exact Or.inr
      ((column_mem_physicalColumns_iff kind index right.columns).mp hphysical)

theorem SummarySelectorsAnchoredBy.empty (anchor : ℕ → RegionColumn) :
    SummarySelectorsAnchoredBy
      ({} : RegionSynthesisSummary).toRegionShapeSummary anchor := by
  intro selector hselector
  simp only [RegionSynthesisSummary.toRegionShapeSummary_columns] at hselector
  simp at hselector

theorem SummarySelectorsAnchoredBy.foldr_combine
    {summaries : List RegionSynthesisSummary} {anchor : ℕ → RegionColumn}
    (hsummaries : summaries.Forall fun summary =>
      SummarySelectorsAnchoredBy summary.toRegionShapeSummary anchor) :
    SummarySelectorsAnchoredBy
      (summaries.foldr RegionSynthesisSummary.combine {}
        |>.toRegionShapeSummary)
      anchor := by
  induction summaries with
  | nil => exact SummarySelectorsAnchoredBy.empty anchor
  | cons summary rest inductionHypothesis =>
      rw [List.forall_cons] at hsummaries
      exact hsummaries.1.combine (inductionHypothesis hsummaries.2)

theorem SelectorAnchoredBy.ofRegion
    {summary : RegionSynthesisSummary} {anchor : ℕ → RegionColumn}
    (hsummary : SummarySelectorsAnchoredBy summary.toRegionShapeSummary anchor) :
    SelectorAnchoredBy (SynthesisSummary.ofRegion summary).regionShapes anchor := by
  simpa [SelectorAnchoredBy] using hsummary

theorem SelectorAnchoredBy.combine
    {left right : SynthesisSummary} {anchor : ℕ → RegionColumn}
    (hleft : SelectorAnchoredBy left.regionShapes anchor)
    (hright : SelectorAnchoredBy right.regionShapes anchor) :
    SelectorAnchoredBy (left.combine right).regionShapes anchor := by
  simpa only [SelectorAnchoredBy, SynthesisSummary.combine_regionShapes,
    List.forall_append] using And.intro hleft hright

theorem SelectorAnchoredBy.replicate
    {summary : SynthesisSummary} {anchor : ℕ → RegionColumn}
    (hsummary : SelectorAnchoredBy summary.regionShapes anchor)
    (count : ℕ) :
    SelectorAnchoredBy (SynthesisSummary.replicate count summary).regionShapes
      anchor := by
  rw [SelectorAnchoredBy, SynthesisSummary.replicate_regionShapes,
    List.forall_iff_forall_mem]
  intro shape hshape
  rw [List.mem_flatten] at hshape
  obtain ⟨shapes, hshapes, hshape⟩ := hshape
  have : shapes = summary.regionShapes := List.eq_of_mem_replicate hshapes
  subst shapes
  exact List.forall_iff_forall_mem.mp hsummary shape hshape

/-- Current selector allocations are covered by the corresponding physical
anchor allocation. -/
def SelectorAllocationsDominatedBy (allocations : CircuitAllocations)
    (anchor : ℕ → RegionColumn) : Prop :=
  ∀ selector, ColumnAllocationsDominate allocations
    (anchor selector) (.selector selector)

theorem SelectorAllocationsDominatedBy.empty
    (anchor : ℕ → RegionColumn) :
    SelectorAllocationsDominatedBy (∅ : CircuitAllocations) anchor := by
  intro selector interval hinterval
  simp at hinterval

theorem ColumnsDominate.of_selectorAnchors
    {allocations : CircuitAllocations} {columns : List RegionColumn}
    {length : ℕ} {anchor : ℕ → RegionColumn}
    (hallocations : SelectorAllocationsDominatedBy allocations anchor)
    (hanchors : ∀ selector,
      RegionColumn.selector selector ∈ columns →
        anchor selector ∈ physicalColumns columns) :
    ColumnsDominate allocations (physicalColumns columns)
      (selectorColumns columns) length := by
  intro row hphysical column hcolumn
  obtain ⟨selector, rfl⟩ := exists_selector_of_mem_selectorColumns hcolumn
  have hsource := selector_mem_selectorColumns_iff selector columns |>.mp
    hcolumn
  exact (hallocations selector).fits
    (hphysical (anchor selector) (hanchors selector hsource))

theorem PlacementEffect.selectorAllocationsDominatedBy
    {before : CircuitAllocations} {columns : List RegionColumn}
    {length : ℕ} {result : Option ℕ × CircuitAllocations}
    {anchor : ℕ → RegionColumn}
    (heffect : PlacementEffect before columns length result)
    (hbefore : SelectorAllocationsDominatedBy before anchor)
    (hanchors : ∀ selector,
      RegionColumn.selector selector ∈ columns →
        anchor selector ∈ columns) :
    SelectorAllocationsDominatedBy result.2 anchor := by
  cases hrow : result.1 with
  | none =>
      intro selector interval hinterval
      rw [heffect (.selector selector), hrow] at hinterval
      rw [heffect (anchor selector), hrow]
      exact hbefore selector interval hinterval
  | some row =>
      intro selector interval hinterval
      rw [heffect (.selector selector), hrow] at hinterval
      rw [heffect (anchor selector), hrow]
      dsimp only at hinterval ⊢
      by_cases hselector : RegionColumn.selector selector ∈ columns
      · have hanchor := hanchors selector hselector
        rw [if_pos hselector, Allocations.mem_insert_iff] at hinterval
        rw [if_pos hanchor, Allocations.mem_insert_iff]
        exact hinterval.imp_right (hbefore selector interval)
      · rw [if_neg hselector] at hinterval
        by_cases hanchor : anchor selector ∈ columns
        · rw [if_pos hanchor, Allocations.mem_insert_iff]
          exact Or.inr (hbefore selector interval hinterval)
        · rw [if_neg hanchor]
          exact hbefore selector interval hinterval

end V1

/-- Remove the virtual selector portion of one reduced footprint. -/
def RegionShapeSummary.withoutSelectors
    (summary : RegionShapeSummary) : RegionShapeSummary where
  columns := physicalColumns summary.columns
  rowCount := summary.rowCount

@[simp] theorem RegionShapeSummary.withoutSelectors_key
    (summary : RegionShapeSummary) :
    summary.withoutSelectors.key = summary.key := by
  unfold RegionShapeSummary.key RegionShapeSummary.adviceCols
  simp only [RegionShapeSummary.withoutSelectors]
  have hfilter :
      (physicalColumns summary.columns).filter RegionColumn.isAdvice =
        summary.columns.filter RegionColumn.isAdvice := by
    rw [physicalColumns, List.filter_filter]
    apply List.filter_congr
    intro column _
    cases column with
    | selector => simp [RegionColumn.isAdvice]
    | column kind index => cases kind <;> simp [RegionColumn.isAdvice]
  rw [hfilter]

/-- The exact selector-free region stream consumed by physical V1 placement. -/
def SynthesisSummary.physicalRegionShapes
    (summary : SynthesisSummary) : List RegionShapeSummary :=
  summary.regionShapes.map RegionShapeSummary.withoutSelectors

theorem SynthesisSummary.combine_physicalRegionShapes
    (left right : SynthesisSummary) :
    (left.combine right).physicalRegionShapes =
      left.physicalRegionShapes ++ right.physicalRegionShapes := by
  unfold SynthesisSummary.physicalRegionShapes
  rw [SynthesisSummary.combine_regionShapes, List.map_append]

theorem SynthesisSummary.ofRegion_physicalRegionShapes
    (summary : RegionSynthesisSummary) :
    (SynthesisSummary.ofRegion summary).physicalRegionShapes =
      [summary.toRegionShapeSummary.withoutSelectors] := by
  unfold SynthesisSummary.physicalRegionShapes
  rw [SynthesisSummary.ofRegion_regionShapes]
  rfl

theorem SynthesisSummary.ofInstanceRow_physicalRegionShapes (row : ℕ) :
    (SynthesisSummary.ofInstanceRow row).physicalRegionShapes = [] := by
  rfl

theorem SynthesisSummary.replicate_physicalRegionShapes
    (count : ℕ) (summary : SynthesisSummary) :
    (SynthesisSummary.replicate count summary).physicalRegionShapes =
      (List.replicate count summary.physicalRegionShapes).flatten := by
  unfold SynthesisSummary.physicalRegionShapes
  rw [SynthesisSummary.replicate_regionShapes]
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.flatten_cons, List.map_append,
        List.replicate_succ, List.flatten_cons, inductionHypothesis]

theorem Multiset.coe_flatten_replicate {α : Type} (count : ℕ)
    (items : List α) :
    ((List.replicate count items).flatten : Multiset α) =
      count • (items : Multiset α) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [List.replicate_succ, List.flatten_cons, ← Multiset.coe_add,
        inductionHypothesis, add_nsmul, one_nsmul, add_comm]

theorem SynthesisSummary.foldr_combine_physicalRegionShapes
    (summaries : List SynthesisSummary) :
    (summaries.foldr SynthesisSummary.combine {}).physicalRegionShapes =
      summaries.flatMap SynthesisSummary.physicalRegionShapes := by
  induction summaries with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      rw [List.foldr_cons, SynthesisSummary.combine_physicalRegionShapes,
        List.flatMap_cons, inductionHypothesis]

namespace V1

open Halo2 FloorPlanner

/-- Selector columns do not influence the chosen row when their allocations are
covered by physical anchors in the same region. -/
theorem placeSummary_row_eq_withoutSelectors
    (summary : RegionShapeSummary) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (hnodup : summary.columns.Nodup)
    (hlength : 0 < summary.rowCount)
    {anchor : ℕ → RegionColumn}
    (hallocations : SelectorAllocationsDominatedBy allocations anchor)
    (hanchors : ∀ selector,
      RegionColumn.selector selector ∈ summary.columns →
        anchor selector ∈ physicalColumns summary.columns) :
    (placeSummary summary allocations).1 =
      (placeSummary summary.withoutSelectors allocations).1 := by
  let physical := sortRegionColumns (physicalColumns summary.columns)
  let selectors := sortRegionColumns (selectorColumns summary.columns)
  have hsplit : sortRegionColumns summary.columns = physical ++ selectors := by
    exact sortRegionColumns_eq_physical_append_selectors summary.columns
  have hsortedNodup : (physical ++ selectors).Nodup := by
    rw [← hsplit]
    exact (sortRegionColumns_perm summary.columns).nodup_iff.mpr hnodup
  have hdominate : ColumnsDominate allocations physical selectors
      summary.rowCount := by
    have hbase : ColumnsDominate allocations
        (physicalColumns summary.columns) (selectorColumns summary.columns)
        summary.rowCount :=
      ColumnsDominate.of_selectorAnchors hallocations hanchors
    intro row hphysical
    have hphysicalSource : FitsColumns allocations
        (physicalColumns summary.columns) row summary.rowCount :=
      hphysical.mono (fun column hcolumn =>
        (sortRegionColumns_perm
          (physicalColumns summary.columns)).mem_iff.mpr hcolumn)
    have hselectorsSource := hbase row hphysicalSource
    exact hselectorsSource.mono (fun column hcolumn =>
      (sortRegionColumns_perm
        (selectorColumns summary.columns)).mem_iff.mp hcolumn)
  have hdrop := firstFit_drop_dominated_suffix
    (physical ++ selectors).length allocations allocations [] physical
      selectors summary.rowCount 0 none hvalid hvalid
      (CircuitAllocations.Equivalent.refl allocations) hsortedNodup
      hlength le_rfl (by
        intro row hwithin column hcolumn
        simp at hcolumn) hdominate
  have hfuel := firstFit_eq_of_sufficient_fuel physical
    (physical ++ selectors).length physical.length allocations
      summary.rowCount 0 none (by simp) le_rfl
  simp only [placeSummary, RegionShapeSummary.withoutSelectors]
  rw [hsplit]
  exact hdrop.trans (congrArg Prod.fst hfuel)

/-- Allocation maps agree on every concrete planner column. -/
def CircuitAllocations.PhysicalEquivalent
    (left right : CircuitAllocations) : Prop :=
  ∀ kind index,
    left.getD (.column kind index) #[] =
      right.getD (.column kind index) #[]

theorem CircuitAllocations.PhysicalEquivalent.refl
    (allocations : CircuitAllocations) :
    CircuitAllocations.PhysicalEquivalent allocations allocations := by
  intro kind index
  rfl

theorem CircuitAllocations.PhysicalEquivalent.agreesOn
    {left right : CircuitAllocations}
    (hequivalent : CircuitAllocations.PhysicalEquivalent left right)
    (columns : List RegionColumn) :
    left.AgreesOn right (physicalColumns columns) := by
  intro column hcolumn
  rw [physicalColumns, List.mem_filter] at hcolumn
  rcases column with ⟨kind, index⟩ | selector
  · exact hequivalent kind index
  · simp at hcolumn

theorem placeSummary_effect
    (summary : RegionShapeSummary) (allocations : CircuitAllocations)
    (hvalid : allocations.Valid) (hnodup : summary.columns.Nodup)
    (hlength : 0 < summary.rowCount) :
    PlacementEffect allocations (sortRegionColumns summary.columns)
      summary.rowCount (placeSummary summary allocations) := by
  exact firstFit_effect (sortRegionColumns summary.columns).length
    allocations (sortRegionColumns summary.columns) summary.rowCount 0 none
    hvalid ((sortRegionColumns_perm summary.columns).nodup_iff.mpr hnodup)
    hlength

/-- A subinterval of a fitting interval also fits. -/
theorem Allocations.Fits.monoInterval
    {allocations : Allocations} {outerStart outerLength start length : ℕ}
    (hfits : allocations.Fits outerStart outerLength)
    (hstart : outerStart ≤ start)
    (hend : start + length ≤ outerStart + outerLength) :
    allocations.Fits start length := by
  intro allocated hallocated
  have hdisjoint := hfits allocated hallocated
  unfold RowIntervalsDisjoint at hdisjoint ⊢
  omega

/-- Fitting after an insertion means fitting before it and avoiding the newly
inserted interval. -/
theorem Allocations.fits_insert_iff
    {allocations : Allocations} {insertStart insertLength start length : ℕ} :
    (allocations.insert insertStart insertLength).Fits start length ↔
      allocations.Fits start length ∧
        RowIntervalsDisjoint start length insertStart insertLength := by
  constructor
  · intro hfits
    constructor
    · intro allocated hallocated
      exact hfits allocated
        (Allocations.mem_insert_of_mem allocations insertStart insertLength
          hallocated)
    · exact hfits (insertStart, insertLength)
        (Allocations.mem_insert allocations insertStart insertLength)
  · rintro ⟨hfits, hinserted⟩ allocated hallocated
    rw [Allocations.mem_insert_iff] at hallocated
    rcases hallocated with rfl | hallocated
    · exact hinserted
    · exact hfits allocated hallocated

/-! ## Extensional allocation views

Concrete planner traces should reason about per-column interval sequences, not the
implementation details of `Std.HashMap`. An `AllocationView` is that extensional
interface; the following transition theorem crosses the implementation boundary once.
-/

abbrev AllocationView := RegionColumn → Allocations

namespace AllocationView

def empty : AllocationView := fun _ => #[]

def Represents
    (allocations : CircuitAllocations) (view : AllocationView) : Prop :=
  ∀ column, allocations.getD column #[] = view column

theorem Represents.of_equivalent
    {left right : CircuitAllocations} {view : AllocationView}
    (hRepresents : view.Represents right)
    (hEquivalent : left.Equivalent right) :
    view.Represents left := by
  intro column
  rw [hEquivalent column]
  exact hRepresents column

def Valid (view : AllocationView) : Prop :=
  ∀ column, (view column).Valid

theorem empty_represents_empty :
    empty.Represents (∅ : CircuitAllocations) := by
  intro column
  simp [empty]

theorem empty_valid : empty.Valid := by
  intro column
  simp [empty, Allocations.Valid]

def FitsColumns (view : AllocationView) (columns : List RegionColumn)
    (start length : ℕ) : Prop :=
  ∀ column ∈ columns, (view column).Fits start length

theorem FitsColumns.monoInterval
    {view : AllocationView} {columns : List RegionColumn}
    {outerStart outerLength start length : ℕ}
    (hfits : view.FitsColumns columns outerStart outerLength)
    (hstart : outerStart ≤ start)
    (hend : start + length ≤ outerStart + outerLength) :
    view.FitsColumns columns start length := by
  intro column hcolumn
  exact Allocations.Fits.monoInterval (hfits column hcolumn) hstart hend

def LeastFit (view : AllocationView) (columns : List RegionColumn)
    (length row : ℕ) : Prop :=
  FitsColumns view columns row length ∧
    ∀ candidate, FitsColumns view columns candidate length → row ≤ candidate

def insert (view : AllocationView) (columns : List RegionColumn)
    (start length : ℕ) : AllocationView := fun column =>
  if column ∈ columns then
    (view column).insert start length
  else view column

theorem insert_comm_of_ne
    (view : AllocationView) (leftColumns rightColumns : List RegionColumn)
    {leftStart rightStart leftLength rightLength : ℕ}
    (hne : leftStart ≠ rightStart) :
    (view.insert leftColumns leftStart leftLength).insert
        rightColumns rightStart rightLength =
      (view.insert rightColumns rightStart rightLength).insert
        leftColumns leftStart leftLength := by
  funext column
  by_cases hleft : column ∈ leftColumns <;>
    by_cases hright : column ∈ rightColumns
  · simpa [insert, hleft, hright] using
      Allocations.insert_comm_of_ne (view column) hne
  · simp [insert, hleft, hright]
  · simp [insert, hleft, hright]
  · simp [insert, hleft, hright]

/-- Insert a consecutive run of equal-width intervals into the same columns.
The repetition count remains symbolic, so clients can compose compact planner
summaries without expanding `List.replicate`. -/
def insertRepeated (view : AllocationView) (columns : List RegionColumn)
    (start length : ℕ) : ℕ → AllocationView
  | 0 => view
  | count + 1 =>
      insertRepeated (view.insert columns start length) columns
        (start + length) length count

theorem insertRepeated_zero
    (view : AllocationView) (columns : List RegionColumn)
    (start length : ℕ) :
    view.insertRepeated columns start length 0 = view := rfl

theorem insertRepeated_one
    (view : AllocationView) (columns : List RegionColumn)
    (start length : ℕ) :
    view.insertRepeated columns start length 1 =
      view.insert columns start length := rfl

/-- A compact repeated run commutes with an insertion whose start differs from
every start in the run. -/
theorem insertRepeated_insert_comm
    (view : AllocationView) (columns otherColumns : List RegionColumn)
    (start length otherStart otherLength count : ℕ)
    (hne : ∀ index, index < count →
      start + index * length ≠ otherStart) :
    (view.insertRepeated columns start length count).insert
        otherColumns otherStart otherLength =
      (view.insert otherColumns otherStart otherLength).insertRepeated
        columns start length count := by
  induction count generalizing view start with
  | zero => rfl
  | succ count inductionHypothesis =>
      simp only [insertRepeated]
      rw [inductionHypothesis]
      · rw [insert_comm_of_ne]
        simpa using hne 0 (Nat.zero_lt_succ count)
      · intro index hindex
        have hnext := hne (index + 1) (by omega)
        simpa [Nat.add_mul, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hnext

theorem insertRepeated_add
    (view : AllocationView) (columns : List RegionColumn)
    (start length leftCount rightCount : ℕ) :
    (view.insertRepeated columns start length leftCount).insertRepeated
        columns (start + leftCount * length) length rightCount =
      view.insertRepeated columns start length (leftCount + rightCount) := by
  induction leftCount generalizing view start with
  | zero => simp [insertRepeated]
  | succ leftCount inductionHypothesis =>
      rw [show leftCount.succ + rightCount =
          (leftCount + rightCount).succ by omega]
      simp only [insertRepeated]
      rw [show start + leftCount.succ * length =
          start + length + leftCount * length by
            rw [Nat.succ_mul]
            omega]
      exact inductionHypothesis _ _

theorem insert_valid
    {view : AllocationView} {columns : List RegionColumn}
    {start length : ℕ} (hvalid : view.Valid)
    (hfits : view.FitsColumns columns start length)
    (hlength : 0 < length) :
    (view.insert columns start length).Valid := by
  intro column
  by_cases hcolumn : column ∈ columns
  · simp only [insert, hcolumn, ↓reduceIte]
    exact Allocations.Valid.insert (view column) start length
      (hvalid column) (hfits column hcolumn) hlength
  · simpa [insert, hcolumn] using hvalid column

theorem fitsColumns_insert_iff
    {view : AllocationView} {insertColumns columns : List RegionColumn}
    {insertStart insertLength start length : ℕ} :
    (view.insert insertColumns insertStart insertLength).FitsColumns
        columns start length ↔
      view.FitsColumns columns start length ∧
        ∀ column, column ∈ columns → column ∈ insertColumns →
          RowIntervalsDisjoint start length insertStart insertLength := by
  constructor
  · intro hfits
    constructor
    · intro column hcolumn
      by_cases hinsert : column ∈ insertColumns
      · exact Allocations.fits_insert_iff.mp
          (by simpa [insert, hinsert] using hfits column hcolumn) |>.1
      · simpa [insert, hinsert] using hfits column hcolumn
    · intro column hcolumn hinsert
      exact Allocations.fits_insert_iff.mp
        (by simpa [insert, hinsert] using hfits column hcolumn) |>.2
  · rintro ⟨hfits, hinserted⟩ column hcolumn
    by_cases hinsert : column ∈ insertColumns
    · simpa [insert, hinsert, Allocations.fits_insert_iff]
        using And.intro (hfits column hcolumn)
          (hinserted column hcolumn hinsert)
    · simpa [insert, hinsert] using hfits column hcolumn

private theorem rowIntervalsDisjoint_adjacent_iff
    (start length insertStart insertLength tailLength : ℕ)
    (hlength : 0 < length) :
    RowIntervalsDisjoint start length insertStart insertLength ∧
        RowIntervalsDisjoint start length (insertStart + insertLength)
          tailLength ↔
      RowIntervalsDisjoint start length insertStart
        (insertLength + tailLength) := by
  unfold RowIntervalsDisjoint
  omega

/-- For future placement, a nonempty repeated run behaves as its single
contiguous occupied interval. This keeps repetition counts symbolic while
checking later blocks. -/
theorem fitsColumns_insertRepeated_succ_iff
    {view : AllocationView} {insertColumns columns : List RegionColumn}
    {insertStart insertLength start length : ℕ} (count : ℕ)
    (hlength : 0 < length) :
    (view.insertRepeated insertColumns insertStart insertLength
        (count + 1)).FitsColumns columns start length ↔
      view.FitsColumns columns start length ∧
        ∀ column, column ∈ columns → column ∈ insertColumns →
          RowIntervalsDisjoint start length insertStart
            ((count + 1) * insertLength) := by
  induction count generalizing view insertStart with
  | zero =>
      simp only [insertRepeated, fitsColumns_insert_iff, Nat.zero_add,
        Nat.one_mul]
  | succ count inductionHypothesis =>
      change
        ((view.insert insertColumns insertStart insertLength).insertRepeated
          insertColumns (insertStart + insertLength) insertLength
            (count + 1)).FitsColumns columns start length ↔ _
      rw [inductionHypothesis, fitsColumns_insert_iff]
      constructor
      · rintro ⟨⟨hview, hfirst⟩, htail⟩
        refine ⟨hview, ?_⟩
        intro column hcolumn hinsert
        have hcombined :=
          (rowIntervalsDisjoint_adjacent_iff start length insertStart
            insertLength ((count + 1) * insertLength) hlength).mp
              ⟨hfirst column hcolumn hinsert,
                htail column hcolumn hinsert⟩
        simpa [Nat.add_mul, two_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc] using hcombined
      · rintro ⟨hview, hall⟩
        constructor
        · refine ⟨hview, ?_⟩
          intro column hcolumn hinsert
          have hwhole := hall column hcolumn hinsert
          have hcombined : RowIntervalsDisjoint start length insertStart
              (insertLength + (count + 1) * insertLength) := by
            simpa [Nat.add_mul, two_mul, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using hwhole
          exact (rowIntervalsDisjoint_adjacent_iff start length insertStart
            insertLength ((count + 1) * insertLength) hlength).mpr hcombined |>.1
        · intro column hcolumn hinsert
          have hwhole := hall column hcolumn hinsert
          have hcombined : RowIntervalsDisjoint start length insertStart
              (insertLength + (count + 1) * insertLength) := by
            simpa [Nat.add_mul, two_mul, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using hwhole
          exact (rowIntervalsDisjoint_adjacent_iff start length insertStart
            insertLength ((count + 1) * insertLength) hlength).mpr hcombined |>.2

theorem fitsColumns_insertRepeated_iff_of_pos
    {view : AllocationView} {insertColumns columns : List RegionColumn}
    {insertStart insertLength start length count : ℕ}
    (hcount : 0 < count) (hlength : 0 < length) :
    (view.insertRepeated insertColumns insertStart insertLength count).FitsColumns
        columns start length ↔
      view.FitsColumns columns start length ∧
        ∀ column, column ∈ columns → column ∈ insertColumns →
          RowIntervalsDisjoint start length insertStart
            (count * insertLength) := by
  obtain ⟨preceding, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt hcount)
  exact fitsColumns_insertRepeated_succ_iff preceding hlength

/-- Once a least fitting interval has been inserted, the adjacent interval is
the next least fit whenever the enclosing run was free beforehand. -/
theorem leastFit_insert_next
    {view : AllocationView} {columns : List RegionColumn}
    {start length remaining : ℕ}
    (hcolumns : columns ≠ []) (hlength : 0 < length)
    (hleast : view.LeastFit columns length start)
    (hfree : view.FitsColumns columns start ((remaining + 2) * length)) :
    (view.insert columns start length).LeastFit columns length
      (start + length) := by
  constructor
  · rw [fitsColumns_insert_iff]
    constructor
    · apply hfree.monoInterval
      · omega
      · simp only [Nat.add_mul]
        omega
    · intro column _ _
      unfold RowIntervalsDisjoint
      omega
  · intro candidate hcandidate
    rw [fitsColumns_insert_iff] at hcandidate
    have hstart : start ≤ candidate := hleast.2 candidate hcandidate.1
    obtain ⟨column, hcolumn⟩ := List.exists_mem_of_ne_nil columns hcolumns
    have hdisjoint := hcandidate.2 column hcolumn hcolumn
    unfold RowIntervalsDisjoint at hdisjoint
    omega

theorem fitsColumns_insert_tail
    {view : AllocationView} {columns : List RegionColumn}
    {start length remaining : ℕ}
    (hfree : view.FitsColumns columns start ((remaining + 2) * length)) :
    (view.insert columns start length).FitsColumns columns
      (start + length) ((remaining + 1) * length) := by
  rw [fitsColumns_insert_iff]
  constructor
  · apply hfree.monoInterval
    · omega
    · simp only [Nat.add_mul]
      omega
  · intro column _ _
    unfold RowIntervalsDisjoint
    omega

theorem insertRepeated_valid
    (count : ℕ) {view : AllocationView} {columns : List RegionColumn}
    {start length : ℕ} (hvalid : view.Valid)
    (hfits : view.FitsColumns columns start ((count + 1) * length))
    (hlength : 0 < length) :
    (view.insertRepeated columns start length (count + 1)).Valid := by
  induction count generalizing view start with
  | zero =>
      simp only [insertRepeated]
      exact AllocationView.insert_valid hvalid
        (hfits.monoInterval (by omega) (by omega)) hlength
  | succ count inductionHypothesis =>
      rw [show count.succ + 1 = (count + 1) + 1 by omega,
        insertRepeated]
      apply inductionHypothesis
      · exact AllocationView.insert_valid hvalid
          (hfits.monoInterval (by omega) (by
            simp only [Nat.add_mul] at hfits ⊢
            omega)) hlength
      · exact view.fitsColumns_insert_tail hfits

theorem Represents.valid
    {allocations : CircuitAllocations} {view : AllocationView}
    (hrepresents : Represents allocations view) (hvalid : view.Valid) :
    allocations.Valid := by
  intro column
  rw [hrepresents column]
  exact hvalid column

theorem Represents.leastFit
    {allocations : CircuitAllocations} {view : AllocationView}
    (hrepresents : Represents allocations view)
    {columns : List RegionColumn} {length row : ℕ}
    (hleast : view.LeastFit columns length row) :
    FloorPlanner.LeastFit allocations columns length row := by
  constructor
  · intro column hcolumn
    rw [hrepresents column]
    exact hleast.1 column hcolumn
  · intro candidate hfits
    apply hleast.2 candidate
    intro column hcolumn
    rw [← hrepresents column]
    exact hfits column hcolumn

/-- Place one summary using only an extensional allocation view. The returned view
is the old view with the chosen interval inserted in every participating column. -/
theorem placeSummary_eq_of_leastFit
    (summary : RegionShapeSummary) (allocations : CircuitAllocations)
    (view : AllocationView) (row : ℕ)
    (hrepresents : Represents allocations view) (hvalid : view.Valid)
    (hnodup : summary.columns.Nodup) (hlength : 0 < summary.rowCount)
    (hleast : view.LeastFit (sortRegionColumns summary.columns)
      summary.rowCount row) :
    ∃ updated,
      placeSummary summary allocations = (some row, updated) ∧
        Represents updated
          (view.insert (sortRegionColumns summary.columns)
            row summary.rowCount) := by
  have hactualValid := hrepresents.valid hvalid
  have hrow := placeSummary_row_eq_of_leastFit summary allocations row
    hactualValid hnodup hlength (hrepresents.leastFit hleast)
  generalize hplaced : placeSummary summary allocations = placed at hrow
  rcases placed with ⟨rowOption, updated⟩
  simp only at hrow
  have : rowOption = some row := hrow
  subst rowOption
  have heffect := placeSummary_effect summary allocations hactualValid
    hnodup hlength
  rw [hplaced] at heffect
  refine ⟨updated, rfl, ?_⟩
  intro column
  rw [heffect column]
  simp only [insert]
  split
  next => rw [hrepresents column]
  next => rw [hrepresents column]

end AllocationView

theorem physical_mem_sorted_full_iff
    (kind : ColumnKind) (index : ℕ) (columns : List RegionColumn) :
    RegionColumn.column kind index ∈ sortRegionColumns columns ↔
      RegionColumn.column kind index ∈
        sortRegionColumns (physicalColumns columns) := by
  rw [(sortRegionColumns_perm columns).mem_iff,
    (sortRegionColumns_perm (physicalColumns columns)).mem_iff,
    column_mem_physicalColumns_iff]

theorem placeSummary_physicalEquivalent
    (summary : RegionShapeSummary) (left right : CircuitAllocations)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    (hnodup : summary.columns.Nodup) (hlength : 0 < summary.rowCount)
    (hbefore : CircuitAllocations.PhysicalEquivalent left right)
    (hrow : (placeSummary summary left).1 =
      (placeSummary summary.withoutSelectors right).1) :
    CircuitAllocations.PhysicalEquivalent (placeSummary summary left).2
      (placeSummary summary.withoutSelectors right).2 := by
  have hfullEffect := placeSummary_effect summary left hvalidLeft hnodup
    hlength
  have hphysicalNodup :
      (physicalColumns summary.columns).Nodup := by
    exact List.Nodup.filter _ hnodup
  have hphysicalEffect := placeSummary_effect summary.withoutSelectors right
    hvalidRight hphysicalNodup hlength
  intro kind index
  rw [hfullEffect (.column kind index),
    hphysicalEffect (.column kind index), hrow]
  cases hresult : (placeSummary summary.withoutSelectors right).1 with
  | none =>
      simpa only [hresult, RegionShapeSummary.withoutSelectors] using
        hbefore kind index
  | some row =>
      simp only [RegionShapeSummary.withoutSelectors]
      have hmember := physical_mem_sorted_full_iff kind index
        summary.columns
      by_cases hcolumn : RegionColumn.column kind index ∈
          sortRegionColumns summary.columns
      · rw [if_pos hcolumn, if_pos (hmember.mp hcolumn),
          hbefore kind index]
      · rw [if_neg hcolumn, if_neg (mt hmember.mpr hcolumn),
          hbefore kind index]

theorem placeSummary_withoutSelectors_row_congruent
    (summary : RegionShapeSummary) (left right : CircuitAllocations)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    (hnodup : summary.columns.Nodup) (hlength : 0 < summary.rowCount)
    (hequivalent : CircuitAllocations.PhysicalEquivalent left right) :
    (placeSummary summary.withoutSelectors left).1 =
      (placeSummary summary.withoutSelectors right).1 := by
  let columns := sortRegionColumns (physicalColumns summary.columns)
  have hcolumnsNodup : columns.Nodup :=
    (sortRegionColumns_perm (physicalColumns summary.columns)).nodup_iff.mpr
      (List.Nodup.filter _ hnodup)
  have hagree : left.AgreesOn right columns := by
    intro column hcolumn
    have hsource := (sortRegionColumns_perm
      (physicalColumns summary.columns)).mem_iff.mp hcolumn
    obtain ⟨kind, index, rfl⟩ :=
      exists_column_of_mem_physicalColumns hsource
    exact hequivalent kind index
  have hcongruent := firstFit_congruent columns.length left columns
    summary.rowCount 0 none right hvalidLeft hvalidRight hcolumnsNodup
    hlength hagree
  exact hcongruent.1

theorem RegionShapeSummary.withoutSelectors_wellFormed
    {summary : RegionShapeSummary} (hwellFormed : summary.WellFormed) :
    summary.withoutSelectors.WellFormed := by
  constructor
  · exact List.Nodup.filter _ hwellFormed.1
  · intro hcolumns
    apply hwellFormed.2
    intro hsource
    apply hcolumns
    simp [RegionShapeSummary.withoutSelectors, physicalColumns, hsource]

/-- One full placement and one selector-free placement choose the same row and
preserve the physical-agreement and selector-domination invariants. -/
theorem placeSummary_withoutSelectors_law
    (summary : RegionShapeSummary) (left right : CircuitAllocations)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    (hwellFormed : summary.WellFormed)
    {anchor : ℕ → RegionColumn}
    (hbeforePhysical : CircuitAllocations.PhysicalEquivalent left right)
    (hbeforeSelectors : SelectorAllocationsDominatedBy left anchor)
    (hanchors : ∀ selector,
      RegionColumn.selector selector ∈ summary.columns →
        anchor selector ∈ physicalColumns summary.columns) :
    let full := placeSummary summary left
    let physical := placeSummary summary.withoutSelectors right
    full.1 = physical.1 ∧
      CircuitAllocations.PhysicalEquivalent full.2 physical.2 ∧
      SelectorAllocationsDominatedBy full.2 anchor := by
  by_cases hcolumns : summary.columns = []
  · simp [placeSummary, hcolumns, RegionShapeSummary.withoutSelectors,
      physicalColumns, sortRegionColumns, firstFit]
    exact ⟨hbeforePhysical, hbeforeSelectors⟩
  · have hlength := hwellFormed.2 hcolumns
    have hleftPhysical := placeSummary_row_eq_withoutSelectors summary left
      hvalidLeft hwellFormed.1 hlength hbeforeSelectors hanchors
    have hphysicalCongruent :=
      placeSummary_withoutSelectors_row_congruent summary left right
        hvalidLeft hvalidRight hwellFormed.1 hlength hbeforePhysical
    have hrow := hleftPhysical.trans hphysicalCongruent
    have hnextPhysical := placeSummary_physicalEquivalent summary left right
      hvalidLeft hvalidRight hwellFormed.1 hlength hbeforePhysical hrow
    have hfullEffect := placeSummary_effect summary left hvalidLeft
      hwellFormed.1 hlength
    have hnextSelectors :=
      PlacementEffect.selectorAllocationsDominatedBy hfullEffect
        hbeforeSelectors (by
        intro selector hselector
        have hsource := (sortRegionColumns_perm summary.columns).mem_iff.mp
          hselector
        have hanchor := hanchors selector hsource
        apply (sortRegionColumns_perm summary.columns).mem_iff.mpr
        rw [physicalColumns, List.mem_filter] at hanchor
        exact hanchor.1)
    exact ⟨hrow, hnextPhysical, hnextSelectors⟩

/-- Selector-free slotting computes exactly the same start rows as full V1 slotting
when selectors have physical anchors. -/
theorem slotShapeSummariesFrom_eq_withoutSelectors
    (summaries : List RegionShapeSummary)
    (left right : CircuitAllocations)
    (hwellFormed : summaries.Forall RegionShapeSummary.WellFormed)
    (hvalidLeft : left.Valid) (hvalidRight : right.Valid)
    {anchor : ℕ → RegionColumn}
    (hphysical : CircuitAllocations.PhysicalEquivalent left right)
    (hselectors : SelectorAllocationsDominatedBy left anchor)
    (hanchors : SelectorAnchoredBy summaries anchor) :
    let full := slotShapeSummariesFrom summaries left
    let physical := slotShapeSummariesFrom
      (summaries.map RegionShapeSummary.withoutSelectors) right
    full.1 = physical.1 ∧
      CircuitAllocations.PhysicalEquivalent full.2 physical.2 ∧
      SelectorAllocationsDominatedBy full.2 anchor := by
  induction summaries generalizing left right with
  | nil => exact ⟨rfl, hphysical, hselectors⟩
  | cons summary rest inductionHypothesis =>
      rw [List.forall_cons] at hwellFormed
      rw [SelectorAnchoredBy, List.forall_cons] at hanchors
      have hhead := placeSummary_withoutSelectors_law summary left right
        hvalidLeft hvalidRight hwellFormed.1 hphysical hselectors
        hanchors.1
      let fullHead := placeSummary summary left
      let physicalHead := placeSummary summary.withoutSelectors right
      have hfullValid := placeSummary_valid summary left hvalidLeft
        hwellFormed.1
      have hphysicalWellFormed :=
        RegionShapeSummary.withoutSelectors_wellFormed hwellFormed.1
      have hphysicalValid := placeSummary_valid summary.withoutSelectors right
        hvalidRight hphysicalWellFormed
      have htail := inductionHypothesis fullHead.2 physicalHead.2
        hwellFormed.2 hfullValid hphysicalValid hhead.2.1 hhead.2.2
        hanchors.2
      simp only [slotShapeSummariesFrom, List.map_cons]
      rw [hhead.1, htail.1]
      exact ⟨rfl, htail.2.1, htail.2.2⟩

end V1

end Halo2.FloorPlanner
