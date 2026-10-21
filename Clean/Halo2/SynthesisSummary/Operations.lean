import Clean.Halo2.SynthesisSummary.Region

namespace Halo2

variable {F : Type}

namespace FloorPlanner

/-- Exact summary of a layouter synthesis stream.  `columnOccupancy column` is the
sum of region heights allocated in `column`; placement can move those intervals but
cannot change their total occupied length. `regionShapes` retains the ordered,
already-reduced V1 measurement input without retaining any region operations. -/
@[ext] structure SynthesisSummary where
  columns : List RegionColumn := []
  columnOccupancy : RegionColumn → ℕ := fun _ => 0
  constantSiteCount : ℕ := 0
  regionShapes : List RegionShapeSummary := []
  tableRowExtent : ℕ := 0
  instanceRowExtent : ℕ := 0
  lookupActivationCount : ℕ := 0
  regionSelectorActivations : List (List (ℕ × ℕ)) := []

namespace SynthesisSummary

/-- The reduced layouter footprint contains neither regional fixed writes nor
nonempty table loads. -/
def HasNoFixedWrites (summary : SynthesisSummary) : Prop :=
  (∀ index, .column .fixed index ∉ summary.columns) ∧
    summary.tableRowExtent = 0

def combine (left right : SynthesisSummary) : SynthesisSummary where
  columns := unionColumns left.columns right.columns
  columnOccupancy := fun column =>
    left.columnOccupancy column + right.columnOccupancy column
  constantSiteCount := left.constantSiteCount + right.constantSiteCount
  lookupActivationCount := left.lookupActivationCount + right.lookupActivationCount
  regionShapes := left.regionShapes ++ right.regionShapes
  regionSelectorActivations :=
    left.regionSelectorActivations ++ right.regionSelectorActivations
  tableRowExtent := max left.tableRowExtent right.tableRowExtent
  instanceRowExtent := max left.instanceRowExtent right.instanceRowExtent

@[synthesis_summary_norm]
theorem hasNoFixedWrites_combine (left right : SynthesisSummary) :
    (left.combine right).HasNoFixedWrites ↔
      left.HasNoFixedWrites ∧ right.HasNoFixedWrites := by
  simp only [HasNoFixedWrites, combine, mem_unionColumns_iff,
    not_or, Nat.max_eq_zero_iff]
  aesop

theorem combine_assoc (left middle right : SynthesisSummary) :
    left.combine (middle.combine right) =
      (left.combine middle).combine right := by
  apply SynthesisSummary.ext
  · exact (unionColumns_assoc _ _ _).symm
  · funext column
    exact (Nat.add_assoc _ _ _).symm
  · exact (Nat.add_assoc _ _ _).symm
  · exact (List.append_assoc _ _ _).symm
  · exact (Nat.max_assoc _ _ _).symm
  · exact (Nat.max_assoc _ _ _).symm
  · exact (Nat.add_assoc _ _ _).symm
  · exact (List.append_assoc _ _ _).symm

/-- Fully reduced summary of `count` identical layouter fragments. -/
def replicate (count : ℕ) (summary : SynthesisSummary) : SynthesisSummary where
  columns := if count = 0 then [] else summary.columns
  columnOccupancy := fun column => count * summary.columnOccupancy column
  constantSiteCount := count * summary.constantSiteCount
  lookupActivationCount := count * summary.lookupActivationCount
  regionShapes := (List.replicate count summary.regionShapes).flatten
  regionSelectorActivations :=
    (List.replicate count summary.regionSelectorActivations).flatten
  tableRowExtent := if count = 0 then 0 else summary.tableRowExtent
  instanceRowExtent := if count = 0 then 0 else summary.instanceRowExtent

@[synthesis_summary_norm]
theorem hasNoFixedWrites_replicate (count : ℕ)
    (summary : SynthesisSummary) :
    (replicate count summary).HasNoFixedWrites ↔
      count = 0 ∨ summary.HasNoFixedWrites := by
  by_cases hcount : count = 0
  · subst count
    simp [HasNoFixedWrites, replicate]
  · simp [HasNoFixedWrites, replicate, hcount]

@[circuit_norm, synthesis_summary_norm]
theorem replicate_columns (count : ℕ) (summary : SynthesisSummary) :
    (replicate count summary).columns =
      if count = 0 then [] else summary.columns := rfl

@[circuit_norm, synthesis_summary_norm]
theorem replicate_columnOccupancy (count : ℕ) (summary : SynthesisSummary)
    (column : RegionColumn) :
    (replicate count summary).columnOccupancy column =
      count * summary.columnOccupancy column := rfl

@[circuit_norm, synthesis_summary_norm]
theorem replicate_constantSiteCount (count : ℕ) (summary : SynthesisSummary) :
    (replicate count summary).constantSiteCount =
      count * summary.constantSiteCount := rfl

@[circuit_norm, synthesis_summary_norm]
theorem replicate_lookupActivationCount (count : ℕ)
    (summary : SynthesisSummary) :
    (replicate count summary).lookupActivationCount =
      count * summary.lookupActivationCount := rfl

@[circuit_norm, synthesis_summary_norm]
theorem replicate_regionShapes (count : ℕ) (summary : SynthesisSummary) :
    (replicate count summary).regionShapes =
      (List.replicate count summary.regionShapes).flatten := rfl

@[circuit_norm, synthesis_summary_norm]
theorem replicate_regionSelectorActivations
    (count : ℕ) (summary : SynthesisSummary) :
    (replicate count summary).regionSelectorActivations =
      (List.replicate count summary.regionSelectorActivations).flatten := rfl

@[circuit_norm, synthesis_summary_norm]
theorem replicate_tableRowExtent (count : ℕ) (summary : SynthesisSummary) :
    (replicate count summary).tableRowExtent =
      if count = 0 then 0 else summary.tableRowExtent := rfl

@[circuit_norm, synthesis_summary_norm]
theorem replicate_instanceRowExtent (count : ℕ) (summary : SynthesisSummary) :
    (replicate count summary).instanceRowExtent =
      if count = 0 then 0 else summary.instanceRowExtent := rfl

theorem replicate_succ (count : ℕ) (summary : SynthesisSummary)
    (hcolumns : summary.columns.Nodup) :
    (replicate count summary).combine summary = replicate (count + 1) summary := by
  apply SynthesisSummary.ext
  · cases count with
    | zero =>
        change unionColumns [] summary.columns = summary.columns
        exact unionColumns_empty_left _ hcolumns
    | succ count =>
        change unionColumns summary.columns summary.columns = summary.columns
        exact unionColumns_self summary.columns
  · funext column
    change count * summary.columnOccupancy column +
      summary.columnOccupancy column =
        (count + 1) * summary.columnOccupancy column
    rw [Nat.add_mul, Nat.one_mul]
  · change count * summary.constantSiteCount + summary.constantSiteCount =
      (count + 1) * summary.constantSiteCount
    rw [Nat.add_mul, Nat.one_mul]
  · simp only [replicate_regionShapes, combine, List.replicate_succ,
      List.flatten_cons]
    induction count with
    | zero => simp
    | succ count inductionHypothesis =>
        rw [List.replicate_succ, List.flatten_cons, List.append_assoc,
          inductionHypothesis, ← List.append_assoc]
  · cases count <;> simp [replicate, combine]
  · cases count <;> simp [replicate, combine]
  · simp only [replicate_lookupActivationCount, combine, Nat.add_mul,
      Nat.one_mul]
  · simp only [replicate, combine, List.replicate_succ,
      List.flatten_cons]
    induction count with
    | zero => simp
    | succ count inductionHypothesis =>
        rw [List.replicate_succ, List.flatten_cons, List.append_assoc,
          inductionHypothesis, ← List.append_assoc]

@[circuit_norm, synthesis_summary_norm]
theorem combine_columns (left right : SynthesisSummary) :
    (left.combine right).columns =
      unionColumns left.columns right.columns := rfl

@[circuit_norm, synthesis_summary_norm] theorem combine_columnOccupancy
    (left right : SynthesisSummary) (column : RegionColumn) :
    (left.combine right).columnOccupancy column =
      left.columnOccupancy column + right.columnOccupancy column := rfl

@[circuit_norm, synthesis_summary_norm] theorem combine_constantSiteCount
    (left right : SynthesisSummary) :
    (left.combine right).constantSiteCount =
      left.constantSiteCount + right.constantSiteCount := rfl

@[circuit_norm, synthesis_summary_norm] theorem combine_lookupActivationCount
    (left right : SynthesisSummary) :
    (left.combine right).lookupActivationCount =
      left.lookupActivationCount + right.lookupActivationCount := rfl

@[circuit_norm, synthesis_summary_norm] theorem combine_regionShapes
    (left right : SynthesisSummary) :
    (left.combine right).regionShapes =
      left.regionShapes ++ right.regionShapes := rfl

@[circuit_norm, synthesis_summary_norm]
theorem combine_regionSelectorActivations (left right : SynthesisSummary) :
    (left.combine right).regionSelectorActivations =
      left.regionSelectorActivations ++ right.regionSelectorActivations := rfl

/-- Lookup activations of a reduced layouter-summary fold are the sum of the
component counts. -/
@[synthesis_summary_norm]
theorem foldr_combine_lookupActivationCount
    (summaries : List SynthesisSummary) :
    (summaries.foldr combine {}).lookupActivationCount =
      (summaries.map (fun summary => summary.lookupActivationCount)).sum := by
  induction summaries with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      simp only [List.foldr_cons, combine_lookupActivationCount,
        List.map_cons, List.sum_cons, inductionHypothesis]

@[circuit_norm, synthesis_summary_norm] theorem combine_tableRowExtent
    (left right : SynthesisSummary) :
    (left.combine right).tableRowExtent =
      max left.tableRowExtent right.tableRowExtent := rfl

@[circuit_norm, synthesis_summary_norm] theorem combine_instanceRowExtent
    (left right : SynthesisSummary) :
    (left.combine right).instanceRowExtent =
      max left.instanceRowExtent right.instanceRowExtent := rfl

@[circuit_norm, synthesis_summary_norm] theorem combine_empty
    (summary : SynthesisSummary) :
    summary.combine {} = summary := by
  apply SynthesisSummary.ext
  · simp [combine, unionColumns]
  · funext column
    simp [combine]
  · simp [combine]
  · simp [combine]
  · simp [combine]
  · simp [combine]
  · simp [combine]
  · simp [combine]

theorem empty_combine (summary : SynthesisSummary)
    (hcolumns : summary.columns.Nodup) :
    ({} : SynthesisSummary).combine summary = summary := by
  apply SynthesisSummary.ext
  · exact unionColumns_empty_left _ hcolumns
  · funext column
    simp [combine]
  · simp [combine]
  · simp [combine]
  · simp [combine]
  · simp [combine]
  · simp [combine]
  · simp [combine]

def ofRegion (summary : RegionSynthesisSummary) : SynthesisSummary where
  columns := summary.columns
  columnOccupancy := fun column =>
    if column ∈ summary.columns then summary.rowCount else 0
  constantSiteCount := summary.constantSiteCount
  lookupActivationCount := summary.lookupActivationCount
  regionShapes := [summary.toRegionShapeSummary]
  regionSelectorActivations := [summary.selectorActivations]
  tableRowExtent := 0
  instanceRowExtent := summary.instanceRowExtent

@[circuit_norm, synthesis_summary_norm]
theorem ofRegion_regionSelectorActivations (summary : RegionSynthesisSummary) :
    (ofRegion summary).regionSelectorActivations =
      [summary.selectorActivations] := rfl

/-- Reduced summary of one absolute instance-row reference. -/
def ofInstanceRow (row : ℕ) : SynthesisSummary where
  instanceRowExtent := row + 1

@[synthesis_summary_norm]
theorem hasNoFixedWrites_ofRegion (summary : RegionSynthesisSummary) :
    (ofRegion summary).HasNoFixedWrites ↔ summary.HasNoFixedColumns := by
  simp [HasNoFixedWrites, ofRegion, RegionSynthesisSummary.HasNoFixedColumns]

@[synthesis_summary_norm]
theorem hasNoFixedWrites_ofInstanceRow (row : ℕ) :
    (ofInstanceRow row).HasNoFixedWrites := by
  simp [HasNoFixedWrites, ofInstanceRow]

@[circuit_norm, synthesis_summary_norm]
theorem ofInstanceRow_columns (row : ℕ) :
    (ofInstanceRow row).columns = [] := rfl

@[circuit_norm, synthesis_summary_norm]
theorem ofInstanceRow_columnOccupancy (row : ℕ) (column : RegionColumn) :
    (ofInstanceRow row).columnOccupancy column = 0 := rfl

@[circuit_norm, synthesis_summary_norm]
theorem ofInstanceRow_constantSiteCount (row : ℕ) :
    (ofInstanceRow row).constantSiteCount = 0 := rfl

@[circuit_norm, synthesis_summary_norm]
theorem ofInstanceRow_lookupActivationCount (row : ℕ) :
    (ofInstanceRow row).lookupActivationCount = 0 := rfl

@[circuit_norm, synthesis_summary_norm]
theorem ofInstanceRow_regionShapes (row : ℕ) :
    (ofInstanceRow row).regionShapes = [] := rfl

@[circuit_norm, synthesis_summary_norm]
theorem ofInstanceRow_tableRowExtent (row : ℕ) :
    (ofInstanceRow row).tableRowExtent = 0 := rfl

@[circuit_norm, synthesis_summary_norm]
theorem ofInstanceRow_instanceRowExtent (row : ℕ) :
    (ofInstanceRow row).instanceRowExtent = row + 1 := rfl

/-- Reduced summary of one lookup-table load. -/
def ofTableValues (values : List F) : SynthesisSummary where
  tableRowExtent := if values = [] then 0 else values.length + 1

@[synthesis_summary_norm]
theorem hasNoFixedWrites_ofTableValues (values : List F) :
    (ofTableValues values).HasNoFixedWrites ↔ values = [] := by
  simp [HasNoFixedWrites, ofTableValues]

@[circuit_norm, synthesis_summary_norm]
theorem ofTableValues_columns (values : List F) :
    (ofTableValues values).columns = [] := rfl

@[circuit_norm, synthesis_summary_norm]
theorem ofTableValues_columnOccupancy (values : List F) (column : RegionColumn) :
    (ofTableValues values).columnOccupancy column = 0 := rfl

@[circuit_norm, synthesis_summary_norm]
theorem ofTableValues_constantSiteCount (values : List F) :
    (ofTableValues values).constantSiteCount = 0 := rfl

@[circuit_norm, synthesis_summary_norm]
theorem ofTableValues_lookupActivationCount (values : List F) :
    (ofTableValues values).lookupActivationCount = 0 := rfl

@[circuit_norm, synthesis_summary_norm]
theorem ofTableValues_regionShapes (values : List F) :
    (ofTableValues values).regionShapes = [] := rfl

@[circuit_norm, synthesis_summary_norm]
theorem ofTableValues_instanceRowExtent (values : List F) :
    (ofTableValues values).instanceRowExtent = 0 := rfl

@[circuit_norm, synthesis_summary_norm]
theorem ofRegion_columns (summary : RegionSynthesisSummary) :
    (ofRegion summary).columns = summary.columns := rfl

@[circuit_norm, synthesis_summary_norm] theorem ofRegion_columnOccupancy
    (summary : RegionSynthesisSummary) (column : RegionColumn) :
    (ofRegion summary).columnOccupancy column =
      if column ∈ summary.columns then summary.rowCount else 0 := rfl

@[circuit_norm, synthesis_summary_norm] theorem ofRegion_constantSiteCount
    (summary : RegionSynthesisSummary) :
    (ofRegion summary).constantSiteCount = summary.constantSiteCount := rfl

@[circuit_norm, synthesis_summary_norm] theorem ofRegion_lookupActivationCount
    (summary : RegionSynthesisSummary) :
    (ofRegion summary).lookupActivationCount = summary.lookupActivationCount := rfl

@[circuit_norm, synthesis_summary_norm] theorem ofRegion_regionShapes
    (summary : RegionSynthesisSummary) :
    (ofRegion summary).regionShapes = [summary.toRegionShapeSummary] := rfl

@[circuit_norm, synthesis_summary_norm] theorem ofRegion_tableRowExtent
    (summary : RegionSynthesisSummary) :
    (ofRegion summary).tableRowExtent = 0 := rfl

@[circuit_norm, synthesis_summary_norm] theorem ofRegion_instanceRowExtent
    (summary : RegionSynthesisSummary) :
    (ofRegion summary).instanceRowExtent = summary.instanceRowExtent := rfl

/-- The greatest exact occupied length among the columns named by the summary. -/
def maxColumnOccupancy (summary : SynthesisSummary) : ℕ :=
  (summary.columns.map summary.columnOccupancy).foldl max 0

theorem maxColumnOccupancy_le
    (summary : SynthesisSummary) (bound : ℕ)
    (hbound : ∀ column ∈ summary.columns,
      summary.columnOccupancy column ≤ bound) :
    summary.maxColumnOccupancy ≤ bound := by
  unfold maxColumnOccupancy
  have general : ∀ (values : List ℕ) (accumulator : ℕ),
      accumulator ≤ bound →
      (∀ value ∈ values, value ≤ bound) →
      values.foldl max accumulator ≤ bound := by
    intro values
    induction values with
    | nil =>
        intro accumulator haccumulator _
        exact haccumulator
    | cons value rest inductionHypothesis =>
        intro accumulator haccumulator hvalues
        rw [List.foldl_cons]
        apply inductionHypothesis (max accumulator value)
        · exact Nat.max_le.mpr ⟨haccumulator, hvalues value (by simp)⟩
        · intro candidate hcandidate
          exact hvalues candidate (by simp [hcandidate])
  apply general _ 0 (Nat.zero_le _)
  intro value hvalue
  obtain ⟨column, hcolumn, rfl⟩ := List.mem_map.mp hvalue
  exact hbound column hcolumn

/-- Exact occupied length of a fixed column. -/
def fixedColumnOccupancy (summary : SynthesisSummary)
    (column : Column .fixed) : ℕ :=
  summary.columnOccupancy (.column .fixed column.index)

/-- Guaranteed deferred-constant capacity from exact compositional occupancies. -/
def constantCapacityLowerBound (summary : SynthesisSummary)
    (constantColumns : List (Column .fixed)) : ℕ :=
  (constantColumns.map fun column =>
    summary.maxColumnOccupancy - summary.fixedColumnOccupancy column).sum

end SynthesisSummary

/-- Exact compositional summary of a complete layouter operation stream. -/
def synthesisSummary : Operations F → SynthesisSummary
  | [] => {}
  | .region _ body :: rest =>
      (SynthesisSummary.ofRegion (regionSynthesisSummary body)).combine
        (synthesisSummary rest)
  | .constrainInstance _ _ row :: rest =>
      (SynthesisSummary.ofInstanceRow row).combine (synthesisSummary rest)
  | .loadTable _ values :: rest =>
      (SynthesisSummary.ofTableValues values).combine (synthesisSummary rest)

@[circuit_norm, synthesis_summary_norm]
theorem synthesisSummary_nil :
    synthesisSummary ([] : Operations F) = {} := rfl

/-- A layouter region reduces to its region summary, composed with the already-reduced
summary of the remaining operation stream. -/
@[circuit_norm, synthesis_summary_norm]
theorem synthesisSummary_region_cons
    (name : String) (body : RegionOperations F) (rest : Operations F) :
    synthesisSummary (.region name body :: rest) =
      (SynthesisSummary.ofRegion (regionSynthesisSummary body)).combine
      (synthesisSummary rest) := rfl

/-- Instance constraints preserve the region allocation summary and record their
absolute instance-row endpoint. -/
@[circuit_norm, synthesis_summary_norm]
theorem synthesisSummary_constrainInstance_cons
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : Operations F) :
    synthesisSummary (.constrainInstance cell column row :: rest) =
      (SynthesisSummary.ofInstanceRow row).combine (synthesisSummary rest) := rfl

/-- Table loads record Halo 2's explicit-prefix plus fill-boundary endpoint. -/
@[circuit_norm, synthesis_summary_norm]
theorem synthesisSummary_loadTable_cons
    (column : TableColumn) (values : List F) (rest : Operations F) :
    synthesisSummary (.loadTable column values :: rest) =
      (SynthesisSummary.ofTableValues values).combine (synthesisSummary rest) := rfl

theorem synthesisSummary_columns_nodup (operations : Operations F) :
    (synthesisSummary operations).columns.Nodup := by
  induction operations with
  | nil => simp [synthesisSummary]
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region _ body =>
          exact unionColumns_nodup _ _
            (regionSynthesisSummary_columns_nodup body)
      | constrainInstance =>
          exact unionColumns_nodup [] _ (by simp)
      | loadTable =>
          exact unionColumns_nodup [] _ (by simp)

@[circuit_norm] theorem synthesisSummary_nil_columns :
    (synthesisSummary ([] : Operations F)).columns = [] := rfl

@[circuit_norm] theorem synthesisSummary_nil_columnOccupancy
    (column : RegionColumn) :
    (synthesisSummary ([] : Operations F)).columnOccupancy column = 0 := rfl

@[circuit_norm] theorem synthesisSummary_nil_constantSiteCount :
    (synthesisSummary ([] : Operations F)).constantSiteCount = 0 := rfl

@[circuit_norm] theorem synthesisSummary_nil_lookupActivationCount :
    (synthesisSummary ([] : Operations F)).lookupActivationCount = 0 := rfl

@[circuit_norm] theorem synthesisSummary_region_cons_columns
    (name : String) (body : RegionOperations F) (rest : Operations F) :
    (synthesisSummary (.region name body :: rest)).columns =
      unionColumns (regionSynthesisSummary body).columns
        (synthesisSummary rest).columns := rfl

@[circuit_norm] theorem synthesisSummary_region_cons_columnOccupancy
    (name : String) (body : RegionOperations F) (rest : Operations F)
    (column : RegionColumn) :
    (synthesisSummary (.region name body :: rest)).columnOccupancy column =
      (if column ∈ (regionSynthesisSummary body).columns then
        (regionSynthesisSummary body).rowCount else 0) +
      (synthesisSummary rest).columnOccupancy column := rfl

@[circuit_norm] theorem synthesisSummary_region_cons_constantSiteCount
    (name : String) (body : RegionOperations F) (rest : Operations F) :
    (synthesisSummary (.region name body :: rest)).constantSiteCount =
      (regionSynthesisSummary body).constantSiteCount +
        (synthesisSummary rest).constantSiteCount := rfl

@[circuit_norm] theorem synthesisSummary_region_cons_lookupActivationCount
    (name : String) (body : RegionOperations F) (rest : Operations F) :
    (synthesisSummary (.region name body :: rest)).lookupActivationCount =
      (regionSynthesisSummary body).lookupActivationCount +
        (synthesisSummary rest).lookupActivationCount := rfl

@[circuit_norm] theorem synthesisSummary_constrainInstance_cons_columns
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : Operations F) :
    (synthesisSummary (.constrainInstance cell column row :: rest)).columns =
      (synthesisSummary rest).columns := by
  exact unionColumns_empty_left _ (synthesisSummary_columns_nodup rest)

@[circuit_norm] theorem synthesisSummary_constrainInstance_cons_columnOccupancy
    (cell : Cell) (instanceColumn : Column .instance) (row : ℕ)
    (rest : Operations F) (column : RegionColumn) :
    (synthesisSummary
      (.constrainInstance cell instanceColumn row :: rest)).columnOccupancy column =
        (synthesisSummary rest).columnOccupancy column := by
  simp [synthesisSummary, SynthesisSummary.combine,
    SynthesisSummary.ofInstanceRow]

@[circuit_norm] theorem synthesisSummary_constrainInstance_cons_constantSiteCount
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : Operations F) :
    (synthesisSummary
      (.constrainInstance cell column row :: rest)).constantSiteCount =
        (synthesisSummary rest).constantSiteCount := by
  simp [synthesisSummary, SynthesisSummary.combine,
    SynthesisSummary.ofInstanceRow]

@[circuit_norm]
theorem synthesisSummary_constrainInstance_cons_lookupActivationCount
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : Operations F) :
    (synthesisSummary
      (.constrainInstance cell column row :: rest)).lookupActivationCount =
        (synthesisSummary rest).lookupActivationCount := by
  simp [synthesisSummary, SynthesisSummary.combine,
    SynthesisSummary.ofInstanceRow]

@[circuit_norm] theorem synthesisSummary_loadTable_cons_columns
    (column : TableColumn) (values : List F) (rest : Operations F) :
    (synthesisSummary (.loadTable column values :: rest)).columns =
      (synthesisSummary rest).columns := by
  exact unionColumns_empty_left _ (synthesisSummary_columns_nodup rest)

@[circuit_norm] theorem synthesisSummary_loadTable_cons_columnOccupancy
    (tableColumn : TableColumn) (values : List F) (rest : Operations F)
    (column : RegionColumn) :
    (synthesisSummary (.loadTable tableColumn values :: rest)).columnOccupancy column =
      (synthesisSummary rest).columnOccupancy column := by
  simp [synthesisSummary, SynthesisSummary.combine,
    SynthesisSummary.ofTableValues]

@[circuit_norm] theorem synthesisSummary_loadTable_cons_constantSiteCount
    (column : TableColumn) (values : List F) (rest : Operations F) :
    (synthesisSummary (.loadTable column values :: rest)).constantSiteCount =
      (synthesisSummary rest).constantSiteCount := by
  simp [synthesisSummary, SynthesisSummary.combine,
    SynthesisSummary.ofTableValues]

@[circuit_norm] theorem synthesisSummary_loadTable_cons_lookupActivationCount
    (column : TableColumn) (values : List F) (rest : Operations F) :
    (synthesisSummary (.loadTable column values :: rest)).lookupActivationCount =
      (synthesisSummary rest).lookupActivationCount := by
  simp [synthesisSummary, SynthesisSummary.combine,
    SynthesisSummary.ofTableValues]

@[circuit_norm] theorem regionSynthesisSummary_append
    (left right : RegionOperations F) :
    regionSynthesisSummary (left ++ right) =
      (regionSynthesisSummary left).combine (regionSynthesisSummary right) := by
  induction left with
  | nil =>
      simp only [List.nil_append, regionSynthesisSummary]
      apply RegionSynthesisSummary.ext
      · exact (unionColumns_empty_left _
          (regionSynthesisSummary_columns_nodup right)).symm
      · simp [RegionSynthesisSummary.combine]
      · simp [RegionSynthesisSummary.combine]
      · simp [RegionSynthesisSummary.combine]
      · simp [RegionSynthesisSummary.combine]
      · simp [RegionSynthesisSummary.combine]
  | cons operation rest inductionHypothesis =>
      simp only [List.cons_append, regionSynthesisSummary,
        inductionHypothesis]
      apply RegionSynthesisSummary.ext
      · simp [RegionSynthesisSummary.combine, unionColumns_assoc]
      · simp [RegionSynthesisSummary.combine, Nat.max_assoc]
      · simp [RegionSynthesisSummary.combine, Nat.add_assoc]
      · simp [RegionSynthesisSummary.combine, Nat.max_assoc]
      · simp [RegionSynthesisSummary.combine, Nat.add_assoc]
      · simp [RegionSynthesisSummary.combine, List.append_assoc]

/-- Columns of concatenated region fragments compose by unioning their reduced
column summaries. -/
@[synthesis_summary_norm]
theorem regionSynthesisSummary_flatten_columns
    (fragments : List (RegionOperations F)) :
    (regionSynthesisSummary fragments.flatten).columns =
      (fragments.map fun operations =>
        (regionSynthesisSummary operations).columns).foldr unionColumns [] := by
  induction fragments with
  | nil => simp only [List.flatten_nil, List.map_nil, List.foldr_nil,
      regionSynthesisSummary_nil_columns]
  | cons fragment rest inductionHypothesis =>
      rw [List.flatten_cons, regionSynthesisSummary_append,
        RegionSynthesisSummary.combine_columns, List.map_cons,
        List.foldr_cons, inductionHypothesis]

/-- The height of concatenated fragments is the maximum of their exact heights. -/
@[synthesis_summary_norm]
theorem regionSynthesisSummary_flatten_rowCount
    (fragments : List (RegionOperations F)) :
    (regionSynthesisSummary fragments.flatten).rowCount =
      (fragments.map fun operations =>
        (regionSynthesisSummary operations).rowCount).foldr max 0 := by
  induction fragments with
  | nil => simp only [List.flatten_nil, List.map_nil, List.foldr_nil,
      regionSynthesisSummary_nil_rowCount]
  | cons fragment rest inductionHypothesis =>
      rw [List.flatten_cons, regionSynthesisSummary_append,
        RegionSynthesisSummary.combine_rowCount, List.map_cons,
        List.foldr_cons, inductionHypothesis]

/-- Deferred-constant demand of concatenated fragments is the sum of their exact
demands. -/
@[synthesis_summary_norm]
theorem regionSynthesisSummary_flatten_constantSiteCount
    (fragments : List (RegionOperations F)) :
    (regionSynthesisSummary fragments.flatten).constantSiteCount =
      (fragments.map fun operations =>
        (regionSynthesisSummary operations).constantSiteCount).sum := by
  induction fragments with
  | nil => simp only [List.flatten_nil, List.map_nil, List.sum_nil,
      regionSynthesisSummary_nil_constantSiteCount]
  | cons fragment rest inductionHypothesis =>
      rw [List.flatten_cons, regionSynthesisSummary_append,
        RegionSynthesisSummary.combine_constantSiteCount, List.map_cons,
        List.sum_cons, inductionHypothesis]

/-- Lookup activations of concatenated fragments are the sum of their exact counts. -/
@[synthesis_summary_norm]
theorem regionSynthesisSummary_flatten_lookupActivationCount
    (fragments : List (RegionOperations F)) :
    (regionSynthesisSummary fragments.flatten).lookupActivationCount =
      (fragments.map fun operations =>
        (regionSynthesisSummary operations).lookupActivationCount).sum := by
  induction fragments with
  | nil => simp only [List.flatten_nil, List.map_nil, List.sum_nil,
      regionSynthesisSummary_nil_lookupActivationCount]
  | cons fragment rest inductionHypothesis =>
      rw [List.flatten_cons, regionSynthesisSummary_append,
        RegionSynthesisSummary.combine_lookupActivationCount, List.map_cons,
        List.sum_cons, inductionHypothesis]

/-- A flattened stream is summarized compositionally from the already-reduced
summary of each fragment. -/
@[synthesis_summary_norm]
theorem regionSynthesisSummary_flatten
    (fragments : List (RegionOperations F)) :
    regionSynthesisSummary fragments.flatten =
      (fragments.map regionSynthesisSummary).foldr
        RegionSynthesisSummary.combine {} := by
  induction fragments with
  | nil => rfl
  | cons fragment rest inductionHypothesis =>
      rw [List.flatten_cons, regionSynthesisSummary_append,
        List.map_cons, List.foldr_cons, inductionHypothesis]

@[circuit_norm, synthesis_summary_norm] theorem synthesisSummary_append
    (left right : Operations F) :
    synthesisSummary (left ++ right) =
      (synthesisSummary left).combine (synthesisSummary right) := by
  induction left with
  | nil =>
      simp only [List.nil_append, synthesisSummary]
      apply SynthesisSummary.ext
      · exact (unionColumns_empty_left _
          (synthesisSummary_columns_nodup right)).symm
      · funext column
        simp [SynthesisSummary.combine]
      · simp [SynthesisSummary.combine]
      · simp [SynthesisSummary.combine]
      · simp [SynthesisSummary.combine]
      · simp [SynthesisSummary.combine]
      · simp [SynthesisSummary.combine]
      · simp [SynthesisSummary.combine]
  | cons operation rest inductionHypothesis =>
      cases operation <;>
        simp only [List.cons_append, synthesisSummary,
          inductionHypothesis]
      all_goals exact SynthesisSummary.combine_assoc _ _ _

attribute [synthesis_summary_norm]
  foldGateSelector
  regionOperationRowExtent
  regionOperationShapeColumns
  regionOperationConstantSiteCount
  regionOperationLookupActivationCount
  regionOperationInstanceRowExtent
  RegionSynthesisSummary.combine_columns
  RegionSynthesisSummary.combine_rowCount
  RegionSynthesisSummary.combine_constantSiteCount
  RegionSynthesisSummary.combine_lookupActivationCount
  RegionSynthesisSummary.combine_instanceRowExtent
  RegionSynthesisSummary.ofOperation_columns
  RegionSynthesisSummary.ofOperation_rowCount
  RegionSynthesisSummary.ofOperation_constantSiteCount
  RegionSynthesisSummary.ofOperation_lookupActivationCount
  RegionSynthesisSummary.ofOperation_instanceRowExtent
  regionSynthesisSummary_nil_columns
  regionSynthesisSummary_nil_rowCount
  regionSynthesisSummary_nil_constantSiteCount
  regionSynthesisSummary_nil_lookupActivationCount
  regionSynthesisSummary_nil_instanceRowExtent
  SynthesisSummary.combine_columns
  SynthesisSummary.combine_columnOccupancy
  SynthesisSummary.combine_constantSiteCount
  SynthesisSummary.combine_lookupActivationCount
  SynthesisSummary.combine_tableRowExtent
  SynthesisSummary.combine_instanceRowExtent
  SynthesisSummary.ofRegion_columns
  SynthesisSummary.ofRegion_columnOccupancy
  SynthesisSummary.ofRegion_constantSiteCount
  SynthesisSummary.ofRegion_lookupActivationCount
  SynthesisSummary.ofRegion_tableRowExtent
  SynthesisSummary.ofRegion_instanceRowExtent
  synthesisSummary_nil_columns
  synthesisSummary_nil_columnOccupancy
  synthesisSummary_nil_constantSiteCount
  synthesisSummary_nil_lookupActivationCount
  synthesisSummary_region_cons_columns
  synthesisSummary_region_cons_columnOccupancy
  synthesisSummary_region_cons_constantSiteCount
  synthesisSummary_region_cons_lookupActivationCount
  synthesisSummary_constrainInstance_cons_columns
  synthesisSummary_constrainInstance_cons_columnOccupancy
  synthesisSummary_constrainInstance_cons_constantSiteCount
  synthesisSummary_constrainInstance_cons_lookupActivationCount
  synthesisSummary_loadTable_cons_columns
  synthesisSummary_loadTable_cons_columnOccupancy
  synthesisSummary_loadTable_cons_constantSiteCount
  synthesisSummary_loadTable_cons_lookupActivationCount
  regionSynthesisSummary_append
  synthesisSummary_append

end FloorPlanner

end Halo2
