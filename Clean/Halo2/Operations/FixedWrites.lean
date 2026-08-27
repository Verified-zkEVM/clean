import Clean.Halo2.Operations.Keygen

namespace Halo2

variable {F : Type}

/-- A region operation does not assign a fixed cell. -/
def RegionOperation.HasNoFixedAssignment : RegionOperation F → Prop
  | .assignFixed _ _ _ => False
  | _ => True

/-- A region stream contains no fixed-cell assignments. -/
def RegionOperations.HasNoFixedAssignments
    (operations : RegionOperations F) : Prop :=
  operations.Forall RegionOperation.HasNoFixedAssignment

/-- A reduced footprint without fixed columns certifies that the source program has
no fixed assignments. -/
theorem FloorPlanner.RegionSynthesisSummary.HasNoFixedColumns.hasNoFixedAssignments
    {operations : RegionOperations F}
    (hsummary :
      (FloorPlanner.regionSynthesisSummary operations).HasNoFixedColumns) :
    RegionOperations.HasNoFixedAssignments operations := by
  apply List.forall_iff_forall_mem.mpr
  intro operation hoperation
  cases operation with
  | assignFixed column row value =>
      exact False.elim (hsummary column.index
        (FloorPlanner.mem_regionSynthesisSummary_columns_of_mem operations
          (.assignFixed column row value) hoperation
          (.column .fixed column.index)
          (by simp [FloorPlanner.regionOperationShapeColumns])))
  | _ => trivial
/-! ## Fixed-write lawfulness -/

/-- Fixed columns written by one region body. -/
def RegionOperations.fixedColumns (operations : RegionOperations F) :
    List (Column .fixed) :=
  operations.filterMap fun operation =>
    match operation with
    | .assignFixed column _ _ => some column
    | _ => none

/-- Two writes to the same relative fixed cell in one region assign the same value. -/
def RegionOperations.FixedAssignmentsAgree
    (operations : RegionOperations F) : Prop :=
  ∀ column row left right,
    .assignFixed column row left ∈ operations →
      .assignFixed column row right ∈ operations →
        left = right

/-- A layouter operation's region-local fixed assignments are unambiguous. -/
def Operation.FixedAssignmentsAgree : Operation F → Prop
  | .region _ body => body.FixedAssignmentsAgree
  | _ => True

/-- A stream containing no fixed writes has unambiguous fixed assignments. -/
theorem RegionOperations.HasNoFixedAssignments.fixedAssignmentsAgree
    {operations : RegionOperations F}
    (hoperations : RegionOperations.HasNoFixedAssignments operations) :
    operations.FixedAssignmentsAgree := by
  intro column row left right hleft _
  have hoperation := List.forall_iff_forall_mem.mp hoperations _ hleft
  simp [RegionOperation.HasNoFixedAssignment] at hoperation

/-- Appending a fixed-write-free suffix preserves fixed-assignment agreement. -/
theorem RegionOperations.FixedAssignmentsAgree.append_right
    {left right : RegionOperations F}
    (hleft : left.FixedAssignmentsAgree)
    (hright : right.HasNoFixedAssignments) :
    (left ++ right).FixedAssignmentsAgree := by
  intro column row x y hx hy
  rw [List.mem_append] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hleft column row x y hx hy
  · have hoperation := List.forall_iff_forall_mem.mp hright _ hy
    simp [RegionOperation.HasNoFixedAssignment] at hoperation
  · have hoperation := List.forall_iff_forall_mem.mp hright _ hx
    simp [RegionOperation.HasNoFixedAssignment] at hoperation
  · have hoperation := List.forall_iff_forall_mem.mp hright _ hx
    simp [RegionOperation.HasNoFixedAssignment] at hoperation

/-- Prepending a fixed-write-free prefix preserves fixed-assignment agreement. -/
theorem RegionOperations.FixedAssignmentsAgree.append_left
    {left right : RegionOperations F}
    (hright : right.FixedAssignmentsAgree)
    (hleft : left.HasNoFixedAssignments) :
    (left ++ right).FixedAssignmentsAgree := by
  intro column row x y hx hy
  rw [List.mem_append] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have hoperation := List.forall_iff_forall_mem.mp hleft _ hx
    simp [RegionOperation.HasNoFixedAssignment] at hoperation
  · have hoperation := List.forall_iff_forall_mem.mp hleft _ hx
    simp [RegionOperation.HasNoFixedAssignment] at hoperation
  · have hoperation := List.forall_iff_forall_mem.mp hleft _ hy
    simp [RegionOperation.HasNoFixedAssignment] at hoperation
  · exact hright column row x y hx hy

/-- A coherent fixed-writing fragment remains coherent between fixed-write-free
prefix and suffix fragments. -/
theorem RegionOperations.FixedAssignmentsAgree.between
    {left middle right : RegionOperations F}
    (hmiddle : middle.FixedAssignmentsAgree)
    (hleft : left.HasNoFixedAssignments)
    (hright : right.HasNoFixedAssignments) :
    (left ++ middle ++ right).FixedAssignmentsAgree :=
  hmiddle.append_left hleft |>.append_right hright

/-- A region stream with no fixed-column writes has unambiguous fixed assignments. -/
theorem RegionOperations.fixedAssignmentsAgree_of_fixedColumns_eq_nil
    {operations : RegionOperations F}
    (hcolumns : operations.fixedColumns = []) :
    operations.FixedAssignmentsAgree := by
  intro column row left right hleft _
  have hcolumn : column ∈ operations.fixedColumns := by
    rw [RegionOperations.fixedColumns, List.mem_filterMap]
    exact ⟨.assignFixed column row left, hleft, rfl⟩
  rw [hcolumns] at hcolumn
  exact (List.not_mem_nil hcolumn).elim

/-- Fixed columns used by region-local assignments in a layouter stream. -/
def Operations.regionFixedColumns (operations : Operations F) :
    List (Column .fixed) :=
  operations.flatMap fun operation =>
    match operation with
    | .region _ body => body.fixedColumns
    | _ => []

theorem RegionOperations.mem_synthesisSummary_columns_of_mem_fixedColumns
    {operations : RegionOperations F} {column : Column .fixed}
    (hcolumn : column ∈ operations.fixedColumns) :
    .column .fixed column.index ∈
      (FloorPlanner.regionSynthesisSummary operations).columns := by
  rw [RegionOperations.fixedColumns, List.mem_filterMap] at hcolumn
  obtain ⟨operation, hoperation, hcolumn⟩ := hcolumn
  cases operation <;> simp_all
  exact FloorPlanner.mem_regionSynthesisSummary_columns_of_mem
    operations _ hoperation _ (by simp [FloorPlanner.regionOperationShapeColumns])

theorem RegionOperations.mem_fixedColumns_of_mem_synthesisSummary_column
    {operations : RegionOperations F} {index : ℕ}
    (hcolumn : .column .fixed index ∈
      (FloorPlanner.regionSynthesisSummary operations).columns) :
    (Column.mk index : Column .fixed) ∈ operations.fixedColumns := by
  rw [FloorPlanner.regionSynthesisSummary_columns_eq_unionColumns] at hcolumn
  have hflat : .column .fixed index ∈
      operations.flatMap FloorPlanner.regionOperationShapeColumns :=
    (FloorPlanner.mem_unionColumns_iff _ _ _).mp hcolumn |>.resolve_left (by simp)
  rw [List.mem_flatMap] at hflat
  obtain ⟨operation, hoperation, hshape⟩ := hflat
  cases operation with
  | assignFixed column row value =>
      simp only [FloorPlanner.regionOperationShapeColumns,
        List.mem_singleton] at hshape
      cases hshape
      rw [RegionOperations.fixedColumns, List.mem_filterMap]
      exact ⟨.assignFixed column row value, hoperation, rfl⟩
  | _ => simp [FloorPlanner.regionOperationShapeColumns] at hshape

theorem Operations.mem_regionFixedColumns_of_mem_synthesisSummary_column
    {operations : Operations F} {index : ℕ}
    (hcolumn : .column .fixed index ∈
      (FloorPlanner.synthesisSummary operations).columns) :
    (Column.mk index : Column .fixed) ∈ operations.regionFixedColumns := by
  induction operations with
  | nil =>
      rw [FloorPlanner.synthesisSummary_nil_columns] at hcolumn
      exact (List.not_mem_nil hcolumn).elim
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body =>
          rw [FloorPlanner.synthesisSummary_region_cons_columns] at hcolumn
          rcases (FloorPlanner.mem_unionColumns_iff _ _ _).mp hcolumn with
            hbody | hrest
          · simp only [Operations.regionFixedColumns, List.flatMap_cons,
              List.mem_append]
            exact Or.inl
              (RegionOperations.mem_fixedColumns_of_mem_synthesisSummary_column hbody)
          · simp only [Operations.regionFixedColumns, List.flatMap_cons,
              List.mem_append]
            exact Or.inr (inductionHypothesis hrest)
      | constrainInstance cell column row =>
          rw [FloorPlanner.synthesisSummary_constrainInstance_cons_columns] at hcolumn
          simpa [Operations.regionFixedColumns] using inductionHypothesis hcolumn
      | loadTable table values =>
          rw [FloorPlanner.synthesisSummary_loadTable_cons_columns] at hcolumn
          simpa [Operations.regionFixedColumns] using inductionHypothesis hcolumn

theorem Operations.KeygenRegistered.mem_fixedColumns_of_mem_regionFixedColumns
    {operations : Operations F} {gates : List (Gate F)}
    {lookups : List (LookupArgument F)}
    {fixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (hregistered : operations.KeygenRegistered gates lookups fixedColumns
      permutationColumns)
    {column : Column .fixed} (hcolumn : column ∈ operations.regionFixedColumns) :
    column ∈ fixedColumns := by
  rw [Operations.regionFixedColumns, List.mem_flatMap] at hcolumn
  obtain ⟨operation, hoperation, hcolumn⟩ := hcolumn
  cases operation with
  | region name body =>
      rw [Operations.KeygenRegistered,
        List.forall_iff_forall_mem] at hregistered
      have hbody := hregistered (.region name body) hoperation
      simp only [Operation.KeygenRegistered] at hbody
      simp only [RegionOperations.fixedColumns, List.mem_filterMap] at hcolumn
      obtain ⟨regionOperation, hregionOperation, hcolumn⟩ := hcolumn
      cases regionOperation with
      | assignFixed assignedColumn row value =>
          cases hcolumn
          exact List.forall_iff_forall_mem.mp hbody
            (.assignFixed column row value) hregionOperation
      | _ => simp at hcolumn
  | _ => simp at hcolumn

theorem FloorPlanner.mem_synthesisSummary_columns_of_mem_region
    (operations : Operations F) (name : String)
    (body : RegionOperations F) (hbody : .region name body ∈ operations)
    (column : RegionColumn)
    (hcolumn : column ∈ (regionSynthesisSummary body).columns) :
    column ∈ (synthesisSummary operations).columns := by
  induction operations with
  | nil => simp at hbody
  | cons operation rest inductionHypothesis =>
      rw [List.mem_cons] at hbody
      cases operation with
      | region headName headBody =>
          rw [synthesisSummary_region_cons_columns]
          apply (mem_unionColumns_iff _ _ _).2
          rcases hbody with hhead | hrest
          · cases hhead
            exact .inl hcolumn
          · exact .inr (inductionHypothesis hrest)
      | constrainInstance =>
          rw [synthesisSummary_constrainInstance_cons_columns]
          rcases hbody with hfalse | hrest
          · cases hfalse
          · exact inductionHypothesis hrest
      | loadTable =>
          rw [synthesisSummary_loadTable_cons_columns]
          rcases hbody with hfalse | hrest
          · cases hfalse
          · exact inductionHypothesis hrest

theorem Operations.mem_synthesisSummary_columns_of_mem_regionFixedColumns
    {operations : Operations F} {column : Column .fixed}
    (hcolumn : column ∈ operations.regionFixedColumns) :
    .column .fixed column.index ∈
      (FloorPlanner.synthesisSummary operations).columns := by
  rw [Operations.regionFixedColumns, List.mem_flatMap] at hcolumn
  obtain ⟨operation, hoperation, hcolumn⟩ := hcolumn
  cases operation with
  | region name body =>
      exact FloorPlanner.mem_synthesisSummary_columns_of_mem_region
        operations name body hoperation _
        (RegionOperations.mem_synthesisSummary_columns_of_mem_fixedColumns hcolumn)
  | constrainInstance => simp at hcolumn
  | loadTable => simp at hcolumn

theorem Operations.disjoint_regionFixedColumns_of_summary
    (operations : Operations F) (columns : List (Column .fixed))
    (hcolumns : ∀ column ∈ columns,
      .column .fixed column.index ∉
        (FloorPlanner.synthesisSummary operations).columns) :
    columns.Disjoint operations.regionFixedColumns := by
  rw [List.disjoint_left]
  intro column hcolumn hregion
  exact hcolumns column hcolumn
    (operations.mem_synthesisSummary_columns_of_mem_regionFixedColumns hregion)

/-- Nonempty lookup-table columns written by a layouter stream. -/
def Operations.loadedTableColumns (operations : Operations F) :
    List (Column .fixed) :=
  operations.filterMap fun operation =>
    match operation with
    | .loadTable table values =>
        if values = [] then none else some table.inner
    | _ => none

@[simp] theorem Operations.loadedTableColumns_nil :
    Operations.loadedTableColumns ([] : Operations F) = [] :=
  rfl

@[simp] theorem Operations.loadedTableColumns_region_cons
    (name : String) (body : RegionOperations F) (rest : Operations F) :
    Operations.loadedTableColumns (.region name body :: rest) =
      rest.loadedTableColumns :=
  rfl

@[simp] theorem Operations.loadedTableColumns_constrainInstance_cons
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : Operations F) :
    Operations.loadedTableColumns (.constrainInstance cell column row :: rest) =
      rest.loadedTableColumns :=
  rfl

@[simp] theorem Operations.loadedTableColumns_loadTable_cons
    (table : TableColumn) (values : List F) (rest : Operations F) :
    Operations.loadedTableColumns (.loadTable table values :: rest) =
      (if values = [] then [] else [table.inner]) ++ rest.loadedTableColumns := by
  by_cases hvalues : values = [] <;>
    simp [Operations.loadedTableColumns, hvalues]

@[simp] theorem Operations.regionFixedColumns_append
    (left right : Operations F) :
    (left ++ right).regionFixedColumns =
      left.regionFixedColumns ++ right.regionFixedColumns := by
  simp [Operations.regionFixedColumns]

@[simp] theorem Operations.loadedTableColumns_append
    (left right : Operations F) :
    (left ++ right).loadedTableColumns =
      left.loadedTableColumns ++ right.loadedTableColumns := by
  simp [Operations.loadedTableColumns]

theorem Operations.regionFixedColumns_eq_nil_of_summary
    {operations : Operations F}
    (hcolumns : ∀ index,
      .column .fixed index ∉
        (FloorPlanner.synthesisSummary operations).columns) :
    operations.regionFixedColumns = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro column hcolumn
  exact hcolumns column.index
    (operations.mem_synthesisSummary_columns_of_mem_regionFixedColumns hcolumn)

theorem Operations.regionAssignmentsAgree_of_regionFixedColumns_eq_nil
    {operations : Operations F}
    (hcolumns : operations.regionFixedColumns = []) :
    operations.Forall Operation.FixedAssignmentsAgree := by
  apply List.forall_iff_forall_mem.mpr
  intro operation hoperation
  cases operation with
  | region name body =>
      apply RegionOperations.fixedAssignmentsAgree_of_fixedColumns_eq_nil
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro column hcolumn
      have : column ∈ operations.regionFixedColumns := by
        rw [Operations.regionFixedColumns, List.mem_flatMap]
        exact ⟨.region name body, hoperation, hcolumn⟩
      rw [hcolumns] at this
      exact List.not_mem_nil this
  | _ => trivial

/-- A layouter operation performs no fixed-column write. -/
def Operation.HasNoFixedWrites : Operation F → Prop
  | .region _ body => RegionOperations.HasNoFixedAssignments body
  | .loadTable _ values => values = []
  | .constrainInstance _ _ _ => True

/-- A layouter stream performs neither regional fixed writes nor nonempty table loads. -/
def Operations.HasNoFixedWrites (operations : Operations F) : Prop :=
  operations.Forall Operation.HasNoFixedWrites

/-- A stream with no fixed writes has no region-written fixed columns. -/
theorem Operations.HasNoFixedWrites.regionFixedColumns_eq_nil
    {operations : Operations F}
    (hoperations : operations.HasNoFixedWrites) :
    operations.regionFixedColumns = [] := by
  rw [Operations.regionFixedColumns, List.flatMap_eq_nil_iff]
  intro operation hoperation
  have hlawful :=
    List.forall_iff_forall_mem.mp hoperations operation hoperation
  cases operation with
  | region name body =>
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro column hcolumn
      simp only [RegionOperations.fixedColumns, List.mem_filterMap] at hcolumn
      obtain ⟨operation, hoperation, hfixed⟩ := hcolumn
      have hnoFixed :=
        List.forall_iff_forall_mem.mp hlawful operation hoperation
      cases operation <;> simp_all [RegionOperation.HasNoFixedAssignment]
  | constrainInstance => rfl
  | loadTable => rfl

/-- A reduced layouter footprint with no fixed writes certifies its source stream. -/
theorem FloorPlanner.SynthesisSummary.HasNoFixedWrites.hasNoFixedWrites
    {operations : Operations F}
    (hsummary :
      (FloorPlanner.synthesisSummary operations).HasNoFixedWrites) :
    Operations.HasNoFixedWrites operations := by
  induction operations with
  | nil => simp [Operations.HasNoFixedWrites]
  | cons operation rest inductionHypothesis =>
      unfold Operations.HasNoFixedWrites
      rw [List.forall_cons]
      cases operation with
      | region name body =>
          rw [FloorPlanner.synthesisSummary_region_cons] at hsummary
          rcases hsummary with ⟨hcolumns, htable⟩
          simp only [FloorPlanner.SynthesisSummary.combine_columns,
            FloorPlanner.SynthesisSummary.ofRegion_columns] at hcolumns
          simp only [FloorPlanner.SynthesisSummary.combine_tableRowExtent,
            FloorPlanner.SynthesisSummary.ofRegion_tableRowExtent] at htable
          constructor
          · apply FloorPlanner.RegionSynthesisSummary.HasNoFixedColumns.hasNoFixedAssignments
            intro index hcolumn
            exact hcolumns index
              ((FloorPlanner.mem_unionColumns_iff _ _ _).2 (.inl hcolumn))
          · apply inductionHypothesis
            constructor
            · intro index hcolumn
              exact hcolumns index
                ((FloorPlanner.mem_unionColumns_iff _ _ _).2 (.inr hcolumn))
            · omega
      | constrainInstance cell column row =>
          rw [FloorPlanner.synthesisSummary_constrainInstance_cons] at hsummary
          rcases hsummary with ⟨hcolumns, htable⟩
          simp only [FloorPlanner.SynthesisSummary.combine_columns,
            FloorPlanner.SynthesisSummary.ofInstanceRow_columns] at hcolumns
          simp only [FloorPlanner.SynthesisSummary.combine_tableRowExtent,
            FloorPlanner.SynthesisSummary.ofInstanceRow_tableRowExtent] at htable
          constructor
          · trivial
          · apply inductionHypothesis
            constructor
            · intro index hcolumn
              exact hcolumns index
                ((FloorPlanner.mem_unionColumns_iff _ _ _).2 (.inr hcolumn))
            · omega
      | loadTable table values =>
          rw [FloorPlanner.synthesisSummary_loadTable_cons] at hsummary
          rcases hsummary with ⟨hcolumns, htable⟩
          simp only [FloorPlanner.SynthesisSummary.combine_columns,
            FloorPlanner.SynthesisSummary.ofTableValues_columns,
            FloorPlanner.unionColumns_empty_left,
            FloorPlanner.synthesisSummary_columns_nodup rest] at hcolumns
          simp only [FloorPlanner.SynthesisSummary.combine_tableRowExtent,
            FloorPlanner.SynthesisSummary.ofTableValues] at htable
          have hvalues : values = [] := by
            split at htable <;> omega
          constructor
          · exact hvalues
          · apply inductionHypothesis
            exact ⟨hcolumns, by omega⟩

/-- A no-fixed-write stream has no nonempty table-column owners. -/
theorem Operations.HasNoFixedWrites.loadedTableColumns_eq_nil
    {operations : Operations F}
    (hoperations : Operations.HasNoFixedWrites operations) :
    operations.loadedTableColumns = [] := by
  induction operations with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      rw [Operations.HasNoFixedWrites, List.forall_cons] at hoperations
      cases operation with
      | region name body =>
          simpa [Operations.loadedTableColumns] using
            inductionHypothesis hoperations.2
      | constrainInstance cell column row =>
          simpa [Operations.loadedTableColumns] using
            inductionHypothesis hoperations.2
      | loadTable table values =>
          have hvalues := hoperations.1
          change values = [] at hvalues
          subst values
          simpa [Operations.loadedTableColumns] using
            inductionHypothesis hoperations.2

/-- A zero table extent in the exact synthesis summary means that synthesis contains no
nonempty table load. -/
theorem Operations.loadedTableColumns_eq_nil_of_tableRowExtent_eq_zero
    {operations : Operations F}
    (htable : (FloorPlanner.synthesisSummary operations).tableRowExtent = 0) :
    operations.loadedTableColumns = [] := by
  induction operations with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body =>
          rw [FloorPlanner.synthesisSummary_region_cons] at htable
          simp only [FloorPlanner.SynthesisSummary.combine_tableRowExtent,
            FloorPlanner.SynthesisSummary.ofRegion_tableRowExtent,
            max_eq_right (Nat.zero_le _)] at htable
          simpa [Operations.loadedTableColumns] using inductionHypothesis htable
      | constrainInstance cell column row =>
          rw [FloorPlanner.synthesisSummary_constrainInstance_cons] at htable
          simp only [FloorPlanner.SynthesisSummary.combine_tableRowExtent,
            FloorPlanner.SynthesisSummary.ofInstanceRow_tableRowExtent,
            max_eq_right (Nat.zero_le _)] at htable
          simpa [Operations.loadedTableColumns] using inductionHypothesis htable
      | loadTable table values =>
          rw [FloorPlanner.synthesisSummary_loadTable_cons] at htable
          simp only [FloorPlanner.SynthesisSummary.combine_tableRowExtent,
            FloorPlanner.SynthesisSummary.ofTableValues,
            Nat.max_eq_zero_iff] at htable
          have hvalues : values = [] := by
            split at htable <;> omega
          subst values
          simpa [Operations.loadedTableColumns] using inductionHypothesis htable.2

/--
The synthesis-local fixed-write discipline needed by keygen.

Region-local duplicate writes may agree, while nonempty table columns are owned by one
load and are disjoint from both region-written and constants columns. V1 placement then
separates different regions, and its constants allocator uses the remaining cells.
-/
structure Operations.FixedWritesLawful
    (operations : Operations F) (constantColumns : List (Column .fixed)) : Prop where
  regionAssignmentsAgree : operations.Forall Operation.FixedAssignmentsAgree
  loadedTableColumns_nodup : operations.loadedTableColumns.Nodup
  loadedTableColumns_disjoint_regionFixedColumns :
    operations.loadedTableColumns.Disjoint operations.regionFixedColumns
  loadedTableColumns_disjoint_constantColumns :
    operations.loadedTableColumns.Disjoint constantColumns

/-- Fixed-write lawfulness is preserved when the available constants columns are
narrowed. -/
theorem Operations.FixedWritesLawful.mono_constantColumns
    {operations : Operations F}
    {source target : List (Column .fixed)}
    (hlawful : operations.FixedWritesLawful source)
    (hsubset : ∀ column ∈ target, column ∈ source) :
    operations.FixedWritesLawful target where
  regionAssignmentsAgree := hlawful.regionAssignmentsAgree
  loadedTableColumns_nodup := hlawful.loadedTableColumns_nodup
  loadedTableColumns_disjoint_regionFixedColumns :=
    hlawful.loadedTableColumns_disjoint_regionFixedColumns
  loadedTableColumns_disjoint_constantColumns := by
    rw [List.disjoint_left]
    intro column htable htarget
    exact List.disjoint_left.mp
      hlawful.loadedTableColumns_disjoint_constantColumns
      htable (hsubset column htarget)

theorem Operations.FixedWritesLawful.append
    {left right : Operations F} {constantColumns : List (Column .fixed)}
    (hleft : left.FixedWritesLawful constantColumns)
    (hright : right.FixedWritesLawful constantColumns)
    (htables : left.loadedTableColumns.Disjoint right.loadedTableColumns)
    (hleftTables : left.loadedTableColumns.Disjoint right.regionFixedColumns)
    (hrightTables : right.loadedTableColumns.Disjoint left.regionFixedColumns) :
    (left ++ right).FixedWritesLawful constantColumns := by
  constructor
  · exact List.forall_append.mpr
      ⟨hleft.regionAssignmentsAgree, hright.regionAssignmentsAgree⟩
  · simp only [Operations.loadedTableColumns, List.filterMap_append]
    exact List.Nodup.append hleft.loadedTableColumns_nodup
      hright.loadedTableColumns_nodup htables
  · simp only [Operations.loadedTableColumns, Operations.regionFixedColumns,
      List.filterMap_append, List.flatMap_append]
    exact List.disjoint_append_left.mpr
      ⟨List.disjoint_append_right.mpr
          ⟨hleft.loadedTableColumns_disjoint_regionFixedColumns,
            hleftTables⟩,
        List.disjoint_append_right.mpr
          ⟨hrightTables, hright.loadedTableColumns_disjoint_regionFixedColumns⟩⟩
  · simp only [Operations.loadedTableColumns, List.filterMap_append]
    exact List.disjoint_append_left.mpr
      ⟨hleft.loadedTableColumns_disjoint_constantColumns,
        hright.loadedTableColumns_disjoint_constantColumns⟩

/-- Compose three synthesis stages when only the first stage loads tables. The two
cross-stage obligations then reduce to showing that the first stage's tables are
disjoint from each later stage's region-written fixed columns. -/
theorem Operations.FixedWritesLawful.append_noLaterTables
    {first middle last : Operations F}
    {constantColumns : List (Column .fixed)}
    (hfirst : first.FixedWritesLawful constantColumns)
    (hmiddle : middle.FixedWritesLawful constantColumns)
    (hlast : last.FixedWritesLawful constantColumns)
    (hmiddleTables : middle.loadedTableColumns = [])
    (hlastTables : last.loadedTableColumns = [])
    (hfirstMiddle : first.loadedTableColumns.Disjoint middle.regionFixedColumns)
    (hfirstLast : first.loadedTableColumns.Disjoint last.regionFixedColumns) :
    (first ++ (middle ++ last)).FixedWritesLawful constantColumns := by
  have hmiddleLast := Operations.FixedWritesLawful.append hmiddle hlast
    (by rw [hmiddleTables]; exact List.disjoint_nil_left _)
    (by rw [hmiddleTables]; exact List.disjoint_nil_left _)
    (by rw [hlastTables]; exact List.disjoint_nil_left _)
  have hmiddleLastTables :
      (middle ++ last).loadedTableColumns = [] := by
    have happend : (middle ++ last).loadedTableColumns =
        middle.loadedTableColumns ++ last.loadedTableColumns := by
      simp only [Operations.loadedTableColumns, List.filterMap_append]
    rw [happend, hmiddleTables, hlastTables, List.nil_append]
  apply Operations.FixedWritesLawful.append hfirst hmiddleLast
  · rw [hmiddleLastTables]
    exact List.disjoint_nil_right _
  · simp only [Operations.regionFixedColumns, List.flatMap_append]
    exact List.disjoint_append_right.mpr ⟨hfirstMiddle, hfirstLast⟩
  · rw [hmiddleLastTables]
    exact List.disjoint_nil_left _

/-- A stream with no fixed writes satisfies the complete fixed-write law for any
constant-column capability. -/
theorem Operations.HasNoFixedWrites.fixedWritesLawful
    {operations : Operations F} {constantColumns : List (Column .fixed)}
    (hoperations : Operations.HasNoFixedWrites operations) :
    operations.FixedWritesLawful constantColumns := by
  have hloaded := hoperations.loadedTableColumns_eq_nil
  constructor
  · apply List.forall_iff_forall_mem.mpr
    intro operation hoperation
    have hlawful := List.forall_iff_forall_mem.mp hoperations operation hoperation
    cases operation with
    | region name body =>
        exact RegionOperations.HasNoFixedAssignments.fixedAssignmentsAgree hlawful
    | _ => trivial
  · rw [hloaded]
    exact List.nodup_nil
  · rw [hloaded]
    exact List.disjoint_nil_left _
  · rw [hloaded]
    exact List.disjoint_nil_left _

/-- Region-local agreement plus the absence of table loads is the complete fixed-write
law. This is the compositional constructor used by wrappers whose children may write
fixed cells but do not load tables. -/
theorem Operations.FixedWritesLawful.ofRegionAssignmentsAgree
    {operations : Operations F} {constantColumns : List (Column .fixed)}
    (hregions : operations.Forall Operation.FixedAssignmentsAgree)
    (htable : (FloorPlanner.synthesisSummary operations).tableRowExtent = 0) :
    operations.FixedWritesLawful constantColumns := by
  have hloaded :=
    Operations.loadedTableColumns_eq_nil_of_tableRowExtent_eq_zero htable
  constructor
  · exact hregions
  · rw [hloaded]
    exact List.nodup_nil
  · rw [hloaded]
    exact List.disjoint_nil_left _
  · rw [hloaded]
    exact List.disjoint_nil_left _

end Halo2
