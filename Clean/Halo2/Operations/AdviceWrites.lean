module

public import Clean.Halo2.Operations.Keygen
public import Clean.Halo2.SynthesisSummary.Operations

@[expose] public section

/-!
# Compositional advice-write distinctness

`RegionOperations.AdviceWritesDistinct` asserts that no two `.assignAdvice` operations inside a
region write to the same `(column, localRow)` pair. `Operations.AdviceWritesDistinct` lifts this
region-by-region across a layouter stream.

Because distinct regions sharing an advice column are separated by floor-planner placement
(`SharedColumnIntervalsDisjoint`), per-region `AdviceWritesDistinct` composes cleanly without
tracking cross-region placement and discharges the advice half of `WritesConsistent` at top level.
-/

namespace Halo2

variable {F : Type}

/-- Advice `(column, localRow)` written by a single region operation, if any. -/
def RegionOperation.adviceWrites : RegionOperation F → List (Column .advice × ℕ)
  | .assignAdvice column row _ => [(column, row)]
  | _ => []

@[keygen_norm, keygen_spine]
theorem RegionOperation.adviceWrites_assignAdvice (column : Column .advice) (row : ℕ)
    (program : WitgenIR F 1) :
    RegionOperation.adviceWrites (.assignAdvice column row program) = [(column, row)] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperation.adviceWrites_assignFixed (column : Column .fixed) (row : ℕ) (value : F) :
    RegionOperation.adviceWrites (.assignFixed column row value) = [] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperation.adviceWrites_enableGate (gate : Gate F) (row : ℕ) :
    RegionOperation.adviceWrites (.enableGate gate row) = [] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperation.adviceWrites_enableLookup (argument : LookupArgument F)
    (selectors : List Selector) (row : ℕ) :
    RegionOperation.adviceWrites (.enableLookup argument selectors row) = [] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperation.adviceWrites_constrainEqual (left right : Cell) :
    RegionOperation.adviceWrites (F := F) (.constrainEqual left right) = [] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperation.adviceWrites_constrainConstant (cell : Cell) (value : F) :
    RegionOperation.adviceWrites (.constrainConstant cell value) = [] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperation.adviceWrites_constrainInstance (cell : Cell)
    (column : Column .instance) (row : ℕ) :
    RegionOperation.adviceWrites (F := F) (.constrainInstance cell column row) = [] := rfl

/-- Ordered list of all `(column, localRow)` advice writes in a region. -/
def RegionOperations.adviceWrites (operations : RegionOperations F) :
    List (Column .advice × ℕ) :=
  operations.flatMap RegionOperation.adviceWrites

@[keygen_norm, keygen_spine]
theorem RegionOperations.adviceWrites_nil :
    RegionOperations.adviceWrites (F := F) [] = [] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperations.adviceWrites_cons (operation : RegionOperation F)
    (rest : RegionOperations F) :
    RegionOperations.adviceWrites (operation :: rest) =
      operation.adviceWrites ++ RegionOperations.adviceWrites rest :=
  List.flatMap_cons ..

@[keygen_norm, keygen_spine]
theorem RegionOperations.adviceWrites_append (left right : RegionOperations F) :
    RegionOperations.adviceWrites (left ++ right) =
      RegionOperations.adviceWrites left ++ RegionOperations.adviceWrites right :=
  List.flatMap_append ..

/-- No two `.assignAdvice` operations in the region target the same `(column, localRow)`. -/
def RegionOperations.AdviceWritesDistinct (operations : RegionOperations F) : Prop :=
  operations.adviceWrites.Nodup

/-- A layouter operation has pairwise-distinct advice writes inside its region. -/
def Operation.AdviceWritesDistinct : Operation F → Prop
  | .region _ body => body.AdviceWritesDistinct
  | _ => True

/-- Every region in a layouter stream has pairwise-distinct advice writes. -/
def Operations.AdviceWritesDistinct (operations : Operations F) : Prop :=
  operations.Forall Operation.AdviceWritesDistinct

namespace RegionOperations

@[keygen_norm, keygen_spine]
theorem adviceWritesDistinct_nil :
    AdviceWritesDistinct (F := F) [] :=
  List.nodup_nil

theorem adviceWritesDistinct_cons_iff (operation : RegionOperation F)
    (rest : RegionOperations F) :
    AdviceWritesDistinct (operation :: rest) ↔
      (match operation with
        | .assignAdvice column row _ => (column, row) ∉ rest.adviceWrites
        | _ => True) ∧
        rest.AdviceWritesDistinct := by
  cases operation <;>
    simp [AdviceWritesDistinct, adviceWrites_cons, RegionOperation.adviceWrites, List.nodup_cons]

@[keygen_norm, keygen_spine]
theorem adviceWritesDistinct_assignAdvice_cons (column : Column .advice) (row : ℕ)
    (program : WitgenIR F 1) (rest : RegionOperations F) :
    AdviceWritesDistinct (.assignAdvice column row program :: rest) ↔
      (column, row) ∉ rest.adviceWrites ∧ rest.AdviceWritesDistinct :=
  adviceWritesDistinct_cons_iff (.assignAdvice column row program) rest

@[keygen_norm, keygen_spine]
theorem adviceWritesDistinct_assignFixed_cons (column : Column .fixed) (row : ℕ) (value : F)
    (rest : RegionOperations F) :
    AdviceWritesDistinct (.assignFixed column row value :: rest) ↔ rest.AdviceWritesDistinct := by
  simpa using adviceWritesDistinct_cons_iff (.assignFixed column row value) rest

@[keygen_norm, keygen_spine]
theorem adviceWritesDistinct_enableGate_cons (gate : Gate F) (row : ℕ)
    (rest : RegionOperations F) :
    AdviceWritesDistinct (.enableGate gate row :: rest) ↔ rest.AdviceWritesDistinct := by
  simpa using adviceWritesDistinct_cons_iff (.enableGate gate row) rest

@[keygen_norm, keygen_spine]
theorem adviceWritesDistinct_enableLookup_cons (argument : LookupArgument F)
    (selectors : List Selector) (row : ℕ) (rest : RegionOperations F) :
    AdviceWritesDistinct (.enableLookup argument selectors row :: rest) ↔
      rest.AdviceWritesDistinct := by
  simpa using adviceWritesDistinct_cons_iff (.enableLookup argument selectors row) rest

@[keygen_norm, keygen_spine]
theorem adviceWritesDistinct_constrainEqual_cons (left right : Cell)
    (rest : RegionOperations F) :
    AdviceWritesDistinct (F := F) (.constrainEqual left right :: rest) ↔
      rest.AdviceWritesDistinct := by
  simpa using adviceWritesDistinct_cons_iff (F := F) (.constrainEqual left right) rest

@[keygen_norm, keygen_spine]
theorem adviceWritesDistinct_constrainConstant_cons (cell : Cell) (value : F)
    (rest : RegionOperations F) :
    AdviceWritesDistinct (.constrainConstant cell value :: rest) ↔
      rest.AdviceWritesDistinct := by
  simpa using adviceWritesDistinct_cons_iff (.constrainConstant cell value) rest

@[keygen_norm, keygen_spine]
theorem adviceWritesDistinct_constrainInstance_cons (cell : Cell)
    (column : Column .instance) (row : ℕ) (rest : RegionOperations F) :
    AdviceWritesDistinct (F := F) (.constrainInstance cell column row :: rest) ↔
      rest.AdviceWritesDistinct := by
  simpa using adviceWritesDistinct_cons_iff (F := F) (.constrainInstance cell column row) rest

@[keygen_norm]
theorem not_mem_adviceWrites_nil (entry : Column .advice × ℕ) :
    entry ∉ ([] : List (Column .advice × ℕ)) ↔ True := by
  simp

@[keygen_norm]
theorem not_mem_adviceWrites_cons (c₁ c₂ : Column .advice) (r₁ r₂ : ℕ)
    (rest : List (Column .advice × ℕ)) :
    (c₁, r₁) ∉ (c₂, r₂) :: rest ↔ (r₁ = r₂ → c₁ ≠ c₂) ∧ (c₁, r₁) ∉ rest := by
  simp only [List.mem_cons, Prod.mk.injEq, not_or, not_and]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun hr hc => h1 hc hr, h2⟩,
    fun ⟨h1, h2⟩ => ⟨fun hc hr => h1 hr hc, h2⟩⟩

@[keygen_norm]
theorem not_mem_adviceWrites_append (entry : Column .advice × ℕ)
    (left right : List (Column .advice × ℕ)) :
    entry ∉ left ++ right ↔ entry ∉ left ∧ entry ∉ right := by
  simp

@[keygen_norm]
theorem not_adviceWrite_eq_iff (c₁ c₂ : Column .advice) (r₁ r₂ : ℕ) :
    (c₁, r₁) ≠ (c₂, r₂) ↔ (r₁ = r₂ → ¬ c₁ = c₂) := by
  simp only [ne_eq, Prod.mk.injEq, not_and]
  exact ⟨fun h hr hc => h hc hr, fun h hc hr => h hr hc⟩

@[keygen_norm]
theorem adviceWrites_offset_eq_add (offset delta : ℕ) :
    (offset = offset + delta) ↔ delta = 0 :=
  Nat.left_eq_add

@[keygen_norm]
theorem adviceWrites_add_eq_offset (offset delta : ℕ) :
    (offset + delta = offset) ↔ delta = 0 :=
  Nat.add_eq_left

@[keygen_norm]
theorem adviceWrites_add_eq_add (offset left right : ℕ) :
    (offset + left = offset + right) ↔ left = right :=
  Nat.add_left_cancel_iff

end RegionOperations

/-- Pairwise distinctness of a list of advice columns, used for `adviceColumnRequirements` on
gadgets whose advice columns are borrowed from a caller. -/
def ColumnsDistinct (columns : List (Column .advice)) : Prop :=
  columns.Nodup

@[keygen_norm]
theorem columnsDistinct_nil : ColumnsDistinct [] ↔ True := by
  simp [ColumnsDistinct]

@[keygen_norm]
theorem columnsDistinct_cons (column : Column .advice) (rest : List (Column .advice)) :
    ColumnsDistinct (column :: rest) ↔ column ∉ rest ∧ ColumnsDistinct rest := by
  simp [ColumnsDistinct, List.nodup_cons]

@[keygen_norm]
theorem not_mem_column_nil (column : Column .advice) :
    column ∉ ([] : List (Column .advice)) ↔ True := by
  simp

@[keygen_norm]
theorem not_mem_column_cons (c₁ c₂ : Column .advice) (rest : List (Column .advice)) :
    c₁ ∉ c₂ :: rest ↔ c₁ ≠ c₂ ∧ c₁ ∉ rest := by
  simp [not_or]

namespace RegionOperations

theorem adviceWritesDistinct_append_iff (left right : RegionOperations F) :
    AdviceWritesDistinct (left ++ right) ↔
      left.AdviceWritesDistinct ∧ right.AdviceWritesDistinct ∧
        left.adviceWrites.Disjoint right.adviceWrites := by
  simp only [AdviceWritesDistinct, adviceWrites_append, List.nodup_append]
  constructor
  · rintro ⟨hl, hr, hdisj⟩
    exact ⟨hl, hr, List.disjoint_left.mpr fun a ha hb => hdisj a ha a hb rfl⟩
  · rintro ⟨hl, hr, hdisj⟩
    refine ⟨hl, hr, fun a ha b hb hab => ?_⟩
    subst hab
    exact List.disjoint_left.mp hdisj ha hb

theorem adviceWritesDistinct_append_of_disjoint {left right : RegionOperations F}
    (hleft : left.AdviceWritesDistinct)
    (hright : right.AdviceWritesDistinct)
    (hdisj : left.adviceWrites.Disjoint right.adviceWrites) :
    (left ++ right).AdviceWritesDistinct :=
  (adviceWritesDistinct_append_iff left right).mpr ⟨hleft, hright, hdisj⟩

/-- Disjoint row intervals imply disjoint advice writes. -/
theorem adviceWrites_disjoint_of_row_sep {left right : RegionOperations F} (mid : ℕ)
    (hleft : ∀ col row, (col, row) ∈ left.adviceWrites → row < mid)
    (hright : ∀ col row, (col, row) ∈ right.adviceWrites → mid ≤ row) :
    left.adviceWrites.Disjoint right.adviceWrites := by
  rw [List.disjoint_left]
  rintro ⟨col, row⟩ hl hr
  have h1 := hleft col row hl
  have h2 := hright col row hr
  omega

/-- Membership in `adviceWrites` corresponds to an `.assignAdvice` operation in the region. -/
theorem mem_adviceWrites_iff {operations : RegionOperations F}
    {column : Column .advice} {row : ℕ} :
    (column, row) ∈ operations.adviceWrites ↔
      ∃ program : WitgenIR F 1, .assignAdvice column row program ∈ operations := by
  unfold adviceWrites
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨op, hop, hmem⟩
    cases op with
    | assignAdvice c r prog =>
      simp only [RegionOperation.adviceWrites, List.mem_singleton, Prod.mk.injEq] at hmem
      rcases hmem with ⟨rfl, rfl⟩
      exact ⟨prog, hop⟩
    | _ => simp [RegionOperation.adviceWrites] at hmem
  · rintro ⟨prog, hop⟩
    exact ⟨.assignAdvice column row prog, hop, List.mem_singleton_self _⟩

/-- Every advice write lies within the region synthesis summary's `rowCount` and `columns`. -/
theorem mem_synthesisSummary_of_mem_adviceWrites
    {operations : RegionOperations F} {column : Column .advice} {row : ℕ}
    (hmem : (column, row) ∈ operations.adviceWrites) :
    .column .advice column.index ∈
        (FloorPlanner.regionSynthesisSummary operations).columns ∧
      row < (FloorPlanner.regionSynthesisSummary operations).rowCount := by
  obtain ⟨prog, hop⟩ := mem_adviceWrites_iff.mp hmem
  refine ⟨?_, ?_⟩
  · exact FloorPlanner.mem_regionSynthesisSummary_columns_of_mem
      operations (.assignAdvice column row prog) hop (.column .advice column.index)
      (by simp [FloorPlanner.regionOperationShapeColumns])
  · have hext := FloorPlanner.regionOperationRowExtent_le_synthesisSummary_of_mem
      operations (.assignAdvice column row prog) hop
    simp only [FloorPlanner.regionOperationRowExtent] at hext
    omega

end RegionOperations

namespace Operations

@[keygen_norm, keygen_spine]
theorem adviceWritesDistinct_nil :
    AdviceWritesDistinct (F := F) [] :=
  trivial

@[keygen_norm, keygen_spine]
theorem adviceWritesDistinct_region_cons (name : String)
    (body : RegionOperations F) (rest : Operations F) :
    AdviceWritesDistinct (.region name body :: rest) ↔
      body.AdviceWritesDistinct ∧ rest.AdviceWritesDistinct :=
  List.forall_cons _ _ _

@[keygen_norm, keygen_spine]
theorem adviceWritesDistinct_constrainInstance_cons (cell : Cell)
    (column : Column .instance) (row : ℕ) (rest : Operations F) :
    AdviceWritesDistinct (.constrainInstance cell column row :: rest) ↔
      rest.AdviceWritesDistinct := by
  simp [AdviceWritesDistinct, Operation.AdviceWritesDistinct]

@[keygen_norm, keygen_spine]
theorem adviceWritesDistinct_loadTable_cons (table : TableColumn)
    (values : List F) (rest : Operations F) :
    AdviceWritesDistinct (.loadTable table values :: rest) ↔
      rest.AdviceWritesDistinct := by
  simp [AdviceWritesDistinct, Operation.AdviceWritesDistinct]

@[keygen_norm, keygen_spine]
theorem adviceWritesDistinct_append (left right : Operations F) :
    AdviceWritesDistinct (left ++ right) ↔
      left.AdviceWritesDistinct ∧ right.AdviceWritesDistinct :=
  List.forall_append

end Operations

/-! ## Self-copy-aware advice-write consistency

In Halo2, copying an already-assigned cell back into its own `(column, localRow)`
(`copyAdvice (AssignedCell.of self row col) col row`) emits `.assignAdvice col row (.ofFExpr (.expr src))`
with `src.cell = Cell.of self row col`. Such an idempotent self-copy leaves the cell's value
unchanged during witness execution. `RegionOperations.AdviceWritesConsistent self` permits later
idempotent self-copies of previously written advice cells while still forbidding any non-self-copy
advice clobber. -/

/-- Computable check that a region operation is an idempotent self-copy of `(self, row, col)`. -/
def RegionOperation.isSelfCopy (self : RegionIndex) : RegionOperation F → Bool
  | .assignAdvice col row (.ir [] (.lit v)) =>
      match v[0] with
      | .expr src => decide (src.cell = Cell.of self row col)
      | _ => false
  | _ => false

/-- Propositional version of `RegionOperation.isSelfCopy`. -/
def RegionOperation.IsSelfCopy (self : RegionIndex) (op : RegionOperation F) : Prop :=
  op.isSelfCopy self = true

@[keygen_norm]
theorem RegionOperation.isSelfCopy_assignAdvice_expr (self : RegionIndex)
    (col : Column .advice) (row : ℕ) (src : AssignedCell F) :
    RegionOperation.IsSelfCopy self (.assignAdvice col row (.ofFExpr (.expr src))) ↔
      src.cell = Cell.of self row col := by
  simp [RegionOperation.IsSelfCopy, RegionOperation.isSelfCopy, Witgen.WitgenIROver.ofFExpr]

/-- Advice `(column, localRow)` written by a single region operation, excluding idempotent
self-copies (`copyAdvice` of `(self, row, column)`). -/
def RegionOperation.nonSelfCopyAdviceWrites (self : RegionIndex) :
    RegionOperation F → List (Column .advice × ℕ)
  | op@(.assignAdvice col row _) =>
      if op.isSelfCopy self then [] else [(col, row)]
  | _ => []

@[keygen_norm, keygen_spine]
theorem RegionOperation.nonSelfCopyAdviceWrites_assignFixed (self : RegionIndex)
    (column : Column .fixed) (row : ℕ) (value : F) :
    RegionOperation.nonSelfCopyAdviceWrites self (.assignFixed column row value) = [] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperation.nonSelfCopyAdviceWrites_enableGate (self : RegionIndex)
    (gate : Gate F) (row : ℕ) :
    RegionOperation.nonSelfCopyAdviceWrites self (.enableGate gate row) = [] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperation.nonSelfCopyAdviceWrites_enableLookup (self : RegionIndex)
    (argument : LookupArgument F) (selectors : List Selector) (row : ℕ) :
    RegionOperation.nonSelfCopyAdviceWrites self (.enableLookup argument selectors row) = [] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperation.nonSelfCopyAdviceWrites_constrainEqual (self : RegionIndex)
    (left right : Cell) :
    RegionOperation.nonSelfCopyAdviceWrites (F := F) self (.constrainEqual left right) = [] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperation.nonSelfCopyAdviceWrites_constrainConstant (self : RegionIndex)
    (cell : Cell) (value : F) :
    RegionOperation.nonSelfCopyAdviceWrites self (.constrainConstant cell value) = [] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperation.nonSelfCopyAdviceWrites_constrainInstance (self : RegionIndex)
    (cell : Cell) (column : Column .instance) (row : ℕ) :
    RegionOperation.nonSelfCopyAdviceWrites (F := F) self
      (.constrainInstance cell column row) = [] := rfl

theorem RegionOperation.mem_nonSelfCopyAdviceWrites_iff (self : RegionIndex)
    (op : RegionOperation F) (col : Column .advice) (row : ℕ) :
    (col, row) ∈ op.nonSelfCopyAdviceWrites self ↔
      ∃ prog : WitgenIR F 1, op = .assignAdvice col row prog ∧ ¬ op.IsSelfCopy self := by
  cases op with
  | assignAdvice c r prog =>
    simp only [nonSelfCopyAdviceWrites, IsSelfCopy]
    cases hsc : RegionOperation.isSelfCopy self (.assignAdvice c r prog)
    · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton, Prod.mk.injEq,
        RegionOperation.assignAdvice.injEq, not_false_eq_true, and_true]
      exact ⟨fun ⟨h1, h2⟩ => ⟨prog, h1.symm, h2.symm, rfl⟩,
        fun ⟨_, h1, h2, _⟩ => ⟨h1.symm, h2.symm⟩⟩
    · simp
  | _ => simp [nonSelfCopyAdviceWrites]

theorem RegionOperation.mem_adviceWrites_of_mem_nonSelfCopy (self : RegionIndex)
    (op : RegionOperation F) {entry : Column .advice × ℕ}
    (hmem : entry ∈ op.nonSelfCopyAdviceWrites self) :
    entry ∈ op.adviceWrites := by
  obtain ⟨prog, hop, _⟩ := (op.mem_nonSelfCopyAdviceWrites_iff self entry.1 entry.2).mp hmem
  subst hop
  simp [RegionOperation.adviceWrites]

/-- Ordered list of all non-self-copy `(column, localRow)` advice writes in region `self`. -/
def RegionOperations.nonSelfCopyAdviceWrites (self : RegionIndex)
    (operations : RegionOperations F) : List (Column .advice × ℕ) :=
  operations.flatMap (RegionOperation.nonSelfCopyAdviceWrites self)

@[keygen_norm, keygen_spine]
theorem RegionOperations.nonSelfCopyAdviceWrites_nil (self : RegionIndex) :
    RegionOperations.nonSelfCopyAdviceWrites (F := F) self [] = [] := rfl

@[keygen_norm, keygen_spine]
theorem RegionOperations.nonSelfCopyAdviceWrites_cons (self : RegionIndex)
    (operation : RegionOperation F) (rest : RegionOperations F) :
    RegionOperations.nonSelfCopyAdviceWrites self (operation :: rest) =
      operation.nonSelfCopyAdviceWrites self ++
        RegionOperations.nonSelfCopyAdviceWrites self rest :=
  List.flatMap_cons ..

@[keygen_norm, keygen_spine]
theorem RegionOperations.nonSelfCopyAdviceWrites_append (self : RegionIndex)
    (left right : RegionOperations F) :
    RegionOperations.nonSelfCopyAdviceWrites self (left ++ right) =
      RegionOperations.nonSelfCopyAdviceWrites self left ++
        RegionOperations.nonSelfCopyAdviceWrites self right :=
  List.flatMap_append ..

theorem RegionOperations.mem_nonSelfCopyAdviceWrites_iff (self : RegionIndex)
    {operations : RegionOperations F} {column : Column .advice} {row : ℕ} :
    (column, row) ∈ operations.nonSelfCopyAdviceWrites self ↔
      ∃ program : WitgenIR F 1,
        .assignAdvice column row program ∈ operations ∧
          ¬ RegionOperation.IsSelfCopy self (.assignAdvice column row program) := by
  unfold nonSelfCopyAdviceWrites
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨op, hop, hmem⟩
    obtain ⟨prog, rfl, hns⟩ :=
      (op.mem_nonSelfCopyAdviceWrites_iff self column row).mp hmem
    exact ⟨prog, hop, hns⟩
  · rintro ⟨prog, hop, hns⟩
    exact ⟨.assignAdvice column row prog, hop,
      (RegionOperation.mem_nonSelfCopyAdviceWrites_iff self _ column row).mpr ⟨prog, rfl, hns⟩⟩

theorem RegionOperations.mem_adviceWrites_of_mem_nonSelfCopy (self : RegionIndex)
    {operations : RegionOperations F} {entry : Column .advice × ℕ}
    (hmem : entry ∈ operations.nonSelfCopyAdviceWrites self) :
    entry ∈ operations.adviceWrites := by
  obtain ⟨prog, hop, _⟩ := (operations.mem_nonSelfCopyAdviceWrites_iff self).mp hmem
  exact RegionOperations.mem_adviceWrites_iff.mpr ⟨prog, hop⟩

/-- Every `.assignAdvice` in region `self` is followed only by advice writes to other cells, by
semantically equivalent writes to the same cell, or by idempotent self-copies (`copyAdvice` of the
same cell). Defined inductively so `whnf` never forces reduction of large unrolled region loops. -/
inductive RegionOperations.AdviceWritesConsistent [FiniteField F] (self : RegionIndex) :
    RegionOperations F → Prop where
  | nil : RegionOperations.AdviceWritesConsistent self []
  | assignAdvice {col : Column .advice} {row : ℕ} {prog : WitgenIR F 1}
      {rest : RegionOperations F} :
      (∀ prog', RegionOperation.assignAdvice col row prog' ∈ rest →
        (∀ env : Placed ProverEnvironment F, (prog.eval env)[0] = (prog'.eval env)[0]) ∨
        RegionOperation.IsSelfCopy self (.assignAdvice col row prog')) →
      RegionOperations.AdviceWritesConsistent self rest →
      RegionOperations.AdviceWritesConsistent self (.assignAdvice col row prog :: rest)
  | assignFixed {col : Column .fixed} {row : ℕ} {val : F} {rest : RegionOperations F} :
      RegionOperations.AdviceWritesConsistent self rest →
      RegionOperations.AdviceWritesConsistent self (.assignFixed col row val :: rest)
  | enableGate {gate : Gate F} {row : ℕ} {rest : RegionOperations F} :
      RegionOperations.AdviceWritesConsistent self rest →
      RegionOperations.AdviceWritesConsistent self (.enableGate gate row :: rest)
  | enableLookup {arg : LookupArgument F} {sels : List Selector} {row : ℕ}
      {rest : RegionOperations F} :
      RegionOperations.AdviceWritesConsistent self rest →
      RegionOperations.AdviceWritesConsistent self (.enableLookup arg sels row :: rest)
  | constrainEqual {left right : Cell} {rest : RegionOperations F} :
      RegionOperations.AdviceWritesConsistent self rest →
      RegionOperations.AdviceWritesConsistent self (.constrainEqual left right :: rest)
  | constrainConstant {cell : Cell} {val : F} {rest : RegionOperations F} :
      RegionOperations.AdviceWritesConsistent self rest →
      RegionOperations.AdviceWritesConsistent self (.constrainConstant cell val :: rest)
  | constrainInstance {cell : Cell} {col : Column .instance} {row : ℕ}
      {rest : RegionOperations F} :
      RegionOperations.AdviceWritesConsistent self rest →
      RegionOperations.AdviceWritesConsistent self (.constrainInstance cell col row :: rest)

namespace RegionOperations

section Consistent
variable [FiniteField F]

@[keygen_norm, keygen_spine]
theorem adviceWritesConsistent_nil (self : RegionIndex) :
    AdviceWritesConsistent (F := F) self [] :=
  .nil

@[keygen_norm, keygen_spine]
theorem adviceWritesConsistent_assignAdvice_cons (self : RegionIndex)
    (column : Column .advice) (row : ℕ) (program : WitgenIR F 1) (rest : RegionOperations F) :
    AdviceWritesConsistent self (.assignAdvice column row program :: rest) ↔
      (∀ prog', RegionOperation.assignAdvice column row prog' ∈ rest →
        (∀ env : Placed ProverEnvironment F, (program.eval env)[0] = (prog'.eval env)[0]) ∨
        RegionOperation.IsSelfCopy self (.assignAdvice column row prog')) ∧
      rest.AdviceWritesConsistent self :=
  ⟨fun h => by cases h with | assignAdvice h1 h2 => exact ⟨h1, h2⟩,
   fun ⟨h1, h2⟩ => .assignAdvice h1 h2⟩

theorem adviceWritesConsistent_assignAdvice_of_not_mem (self : RegionIndex)
    (column : Column .advice) (row : ℕ) (program : WitgenIR F 1) (rest : RegionOperations F)
    (hnot : (column, row) ∉ rest.nonSelfCopyAdviceWrites self)
    (hrest : rest.AdviceWritesConsistent self) :
    AdviceWritesConsistent self (.assignAdvice column row program :: rest) :=
  .assignAdvice (fun prog' hmem => Or.inr (by
    by_contra hns
    exact hnot ((rest.mem_nonSelfCopyAdviceWrites_iff self).mpr ⟨prog', hmem, hns⟩))) hrest

@[keygen_norm, keygen_spine]
theorem adviceWritesConsistent_assignFixed_cons (self : RegionIndex)
    (column : Column .fixed) (row : ℕ) (value : F) (rest : RegionOperations F) :
    AdviceWritesConsistent self (.assignFixed column row value :: rest) ↔
      rest.AdviceWritesConsistent self :=
  ⟨fun h => by cases h with | assignFixed h' => exact h', .assignFixed⟩

@[keygen_norm, keygen_spine]
theorem adviceWritesConsistent_enableGate_cons (self : RegionIndex)
    (gate : Gate F) (row : ℕ) (rest : RegionOperations F) :
    AdviceWritesConsistent self (.enableGate gate row :: rest) ↔
      rest.AdviceWritesConsistent self :=
  ⟨fun h => by cases h with | enableGate h' => exact h', .enableGate⟩

@[keygen_norm, keygen_spine]
theorem adviceWritesConsistent_enableLookup_cons (self : RegionIndex)
    (argument : LookupArgument F) (selectors : List Selector) (row : ℕ)
    (rest : RegionOperations F) :
    AdviceWritesConsistent self (.enableLookup argument selectors row :: rest) ↔
      rest.AdviceWritesConsistent self :=
  ⟨fun h => by cases h with | enableLookup h' => exact h', .enableLookup⟩

@[keygen_norm, keygen_spine]
theorem adviceWritesConsistent_constrainEqual_cons (self : RegionIndex)
    (left right : Cell) (rest : RegionOperations F) :
    AdviceWritesConsistent (F := F) self (.constrainEqual left right :: rest) ↔
      rest.AdviceWritesConsistent self :=
  ⟨fun h => by cases h with | constrainEqual h' => exact h', .constrainEqual⟩

@[keygen_norm, keygen_spine]
theorem adviceWritesConsistent_constrainConstant_cons (self : RegionIndex)
    (cell : Cell) (value : F) (rest : RegionOperations F) :
    AdviceWritesConsistent self (.constrainConstant cell value :: rest) ↔
      rest.AdviceWritesConsistent self :=
  ⟨fun h => by cases h with | constrainConstant h' => exact h', .constrainConstant⟩

@[keygen_norm, keygen_spine]
theorem adviceWritesConsistent_constrainInstance_cons (self : RegionIndex)
    (cell : Cell) (column : Column .instance) (row : ℕ) (rest : RegionOperations F) :
    AdviceWritesConsistent (F := F) self (.constrainInstance cell column row :: rest) ↔
      rest.AdviceWritesConsistent self :=
  ⟨fun h => by cases h with | constrainInstance h' => exact h', .constrainInstance⟩

omit [FiniteField F] in
@[keygen_norm]
theorem not_mem_nonSelfCopyAdviceWrites_assignAdvice_append (self : RegionIndex)
    (c₁ c₂ : Column .advice) (r₁ r₂ : ℕ) (program : WitgenIR F 1)
    (rest : List (Column .advice × ℕ)) :
    (c₁, r₁) ∉ RegionOperation.nonSelfCopyAdviceWrites self (.assignAdvice c₂ r₂ program) ++ rest ↔
      (¬ RegionOperation.IsSelfCopy self (.assignAdvice c₂ r₂ program) → (c₁, r₁) ≠ (c₂, r₂)) ∧
      (c₁, r₁) ∉ rest := by
  rw [List.mem_append, not_or]
  constructor
  · rintro ⟨hhead, htail⟩
    refine ⟨fun hns heq => ?_, htail⟩
    rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
    exact hhead ((RegionOperation.mem_nonSelfCopyAdviceWrites_iff self _ c₁ r₁).mpr
      ⟨program, rfl, hns⟩)
  · rintro ⟨hhead, htail⟩
    refine ⟨fun hmem => ?_, htail⟩
    obtain ⟨prog', heq, hns⟩ :=
      (RegionOperation.mem_nonSelfCopyAdviceWrites_iff self _ c₁ r₁).mp hmem
    cases heq
    exact hhead hns rfl

theorem AdviceWritesDistinct.toConsistent (self : RegionIndex)
    {operations : RegionOperations F} (h : operations.AdviceWritesDistinct) :
    operations.AdviceWritesConsistent self := by
  induction operations with
  | nil => exact .nil
  | cons op rest ih =>
    rw [adviceWritesDistinct_cons_iff] at h
    cases op with
    | assignAdvice col row prog =>
      exact adviceWritesConsistent_assignAdvice_of_not_mem self col row prog rest
        (fun hmem => h.1 (mem_adviceWrites_of_mem_nonSelfCopy self hmem)) (ih h.2)
    | assignFixed _ _ _ => exact .assignFixed (ih h.2)
    | enableGate _ _ => exact .enableGate (ih h.2)
    | enableLookup _ _ _ => exact .enableLookup (ih h.2)
    | constrainEqual _ _ => exact .constrainEqual (ih h.2)
    | constrainConstant _ _ => exact .constrainConstant (ih h.2)
    | constrainInstance _ _ _ => exact .constrainInstance (ih h.2)

theorem adviceWritesConsistent_append_iff (self : RegionIndex)
    (left right : RegionOperations F) :
    (left ++ right).AdviceWritesConsistent self ↔
      left.AdviceWritesConsistent self ∧ right.AdviceWritesConsistent self ∧
        ∀ col row prog₁ prog₂,
          RegionOperation.assignAdvice col row prog₁ ∈ left →
          RegionOperation.assignAdvice col row prog₂ ∈ right →
          (∀ env : Placed ProverEnvironment F, (prog₁.eval env)[0] = (prog₂.eval env)[0]) ∨
          RegionOperation.IsSelfCopy self (.assignAdvice col row prog₂) := by
  induction left with
  | nil =>
    simp [adviceWritesConsistent_nil]
  | cons op rest ih =>
    cases op with
    | assignAdvice col row prog =>
      simp only [List.cons_append, adviceWritesConsistent_assignAdvice_cons, List.mem_append,
        List.mem_cons, ih]
      constructor
      · rintro ⟨hhead, hrest, hright, hcompat⟩
        refine ⟨⟨fun p hp => hhead p (Or.inl hp), hrest⟩, hright, ?_⟩
        intro c r p1 p2 hl hr
        rcases hl with heq | hl
        · cases heq
          exact hhead p2 (Or.inr hr)
        · exact hcompat c r p1 p2 hl hr
      · rintro ⟨⟨hhead, hrest⟩, hright, hcompat⟩
        refine ⟨fun p hp => ?_, hrest, hright, fun c r p1 p2 hl hr =>
          hcompat c r p1 p2 (Or.inr hl) hr⟩
        rcases hp with hp | hp
        · exact hhead p hp
        · exact hcompat col row prog p (Or.inl rfl) hp
    | assignFixed _ _ _ =>
      simp only [List.cons_append, adviceWritesConsistent_assignFixed_cons, List.mem_cons,
        reduceCtorEq, false_or, ih]
    | enableGate _ _ =>
      simp only [List.cons_append, adviceWritesConsistent_enableGate_cons, List.mem_cons,
        reduceCtorEq, false_or, ih]
    | enableLookup _ _ _ =>
      simp only [List.cons_append, adviceWritesConsistent_enableLookup_cons, List.mem_cons,
        reduceCtorEq, false_or, ih]
    | constrainEqual _ _ =>
      simp only [List.cons_append, adviceWritesConsistent_constrainEqual_cons, List.mem_cons,
        reduceCtorEq, false_or, ih]
    | constrainConstant _ _ =>
      simp only [List.cons_append, adviceWritesConsistent_constrainConstant_cons, List.mem_cons,
        reduceCtorEq, false_or, ih]
    | constrainInstance _ _ _ =>
      simp only [List.cons_append, adviceWritesConsistent_constrainInstance_cons, List.mem_cons,
        reduceCtorEq, false_or, ih]

theorem adviceWritesConsistent_append_of_disjoint (self : RegionIndex)
    {left right : RegionOperations F}
    (hleft : left.AdviceWritesConsistent self)
    (hright : right.AdviceWritesConsistent self)
    (hdisj : left.adviceWrites.Disjoint (right.nonSelfCopyAdviceWrites self)) :
    (left ++ right).AdviceWritesConsistent self := by
  rw [adviceWritesConsistent_append_iff]
  refine ⟨hleft, hright, fun col row prog₁ prog₂ hl hr => Or.inr ?_⟩
  by_contra hns
  exact List.disjoint_left.mp hdisj
    (mem_adviceWrites_iff.mpr ⟨prog₁, hl⟩)
    ((right.mem_nonSelfCopyAdviceWrites_iff self).mpr ⟨prog₂, hr, hns⟩)

theorem adviceWritesConsistent_append_of_adviceWrites_disjoint (self : RegionIndex)
    {left right : RegionOperations F}
    (hleft : left.AdviceWritesConsistent self)
    (hright : right.AdviceWritesConsistent self)
    (hdisj : left.adviceWrites.Disjoint right.adviceWrites) :
    (left ++ right).AdviceWritesConsistent self :=
  adviceWritesConsistent_append_of_disjoint self hleft hright
    (List.disjoint_left.mpr fun _ hl hr =>
      List.disjoint_left.mp hdisj hl (mem_adviceWrites_of_mem_nonSelfCopy self hr))

end Consistent

end RegionOperations

/-- Every region in a layouter stream starting at region index `i₀` has consistent advice writes.
Defined inductively so `whnf` never forces reduction of large operation streams. -/
inductive Operations.AdviceWritesConsistentFrom [FiniteField F] :
    RegionIndex → Operations F → Prop where
  | nil (i₀ : RegionIndex) : Operations.AdviceWritesConsistentFrom i₀ []
  | region {i₀ : RegionIndex} {name : String} {body : RegionOperations F} {rest : Operations F} :
      RegionOperations.AdviceWritesConsistent i₀ body →
      Operations.AdviceWritesConsistentFrom (i₀ + 1) rest →
      Operations.AdviceWritesConsistentFrom i₀ (.region name body :: rest)
  | constrainInstance {i₀ : RegionIndex} {cell : Cell} {col : Column .instance} {row : ℕ}
      {rest : Operations F} :
      Operations.AdviceWritesConsistentFrom i₀ rest →
      Operations.AdviceWritesConsistentFrom i₀ (.constrainInstance cell col row :: rest)
  | loadTable {i₀ : RegionIndex} {table : TableColumn} {values : List F} {rest : Operations F} :
      Operations.AdviceWritesConsistentFrom i₀ rest →
      Operations.AdviceWritesConsistentFrom i₀ (.loadTable table values :: rest)

/-- Top-level alias: every region starting at `0` has consistent advice writes. -/
abbrev Operations.AdviceWritesConsistent [FiniteField F] (operations : Operations F) : Prop :=
  operations.AdviceWritesConsistentFrom 0

namespace Operations

section Consistent
variable [FiniteField F]

@[keygen_norm, keygen_spine]
theorem adviceWritesConsistentFrom_nil (i₀ : RegionIndex) :
    AdviceWritesConsistentFrom (F := F) i₀ [] :=
  .nil i₀

@[keygen_norm, keygen_spine]
theorem adviceWritesConsistentFrom_region_cons (i₀ : RegionIndex) (name : String)
    (body : RegionOperations F) (rest : Operations F) :
    AdviceWritesConsistentFrom i₀ (.region name body :: rest) ↔
      body.AdviceWritesConsistent i₀ ∧ rest.AdviceWritesConsistentFrom (i₀ + 1) :=
  ⟨fun h => by cases h with | region h1 h2 => exact ⟨h1, h2⟩,
   fun ⟨h1, h2⟩ => .region h1 h2⟩

@[keygen_norm, keygen_spine]
theorem adviceWritesConsistentFrom_constrainInstance_cons (i₀ : RegionIndex)
    (cell : Cell) (column : Column .instance) (row : ℕ) (rest : Operations F) :
    AdviceWritesConsistentFrom i₀ (.constrainInstance cell column row :: rest) ↔
      rest.AdviceWritesConsistentFrom i₀ :=
  ⟨fun h => by cases h with | constrainInstance h' => exact h', .constrainInstance⟩

@[keygen_norm, keygen_spine]
theorem adviceWritesConsistentFrom_loadTable_cons (i₀ : RegionIndex)
    (table : TableColumn) (values : List F) (rest : Operations F) :
    AdviceWritesConsistentFrom i₀ (.loadTable table values :: rest) ↔
      rest.AdviceWritesConsistentFrom i₀ :=
  ⟨fun h => by cases h with | loadTable h' => exact h', .loadTable⟩

@[keygen_norm, keygen_spine]
theorem adviceWritesConsistentFrom_append (i₀ : RegionIndex) (left right : Operations F) :
    AdviceWritesConsistentFrom i₀ (left ++ right) ↔
      left.AdviceWritesConsistentFrom i₀ ∧
        right.AdviceWritesConsistentFrom (i₀ + left.regionCount) := by
  induction left generalizing i₀ with
  | nil => simp [adviceWritesConsistentFrom_nil, Operations.regionCount]
  | cons op rest ih =>
    cases op with
    | region name body =>
      simp only [List.cons_append, adviceWritesConsistentFrom_region_cons, Operations.regionCount, ih,
        and_assoc, Nat.add_assoc]
    | constrainInstance _ _ _ =>
      simp only [List.cons_append, adviceWritesConsistentFrom_constrainInstance_cons,
        Operations.regionCount, ih]
    | loadTable _ _ =>
      simp only [List.cons_append, adviceWritesConsistentFrom_loadTable_cons,
        Operations.regionCount, ih]

theorem AdviceWritesDistinct.toConsistent (i₀ : RegionIndex)
    {operations : Operations F} (h : operations.AdviceWritesDistinct) :
    operations.AdviceWritesConsistentFrom i₀ := by
  induction operations generalizing i₀ with
  | nil => exact .nil i₀
  | cons op rest ih =>
    cases op with
    | region name body =>
      rw [adviceWritesDistinct_region_cons] at h
      exact .region (h.1.toConsistent i₀) (ih (i₀ + 1) h.2)
    | constrainInstance _ _ _ =>
      rw [adviceWritesDistinct_constrainInstance_cons] at h
      exact .constrainInstance (ih i₀ h)
    | loadTable _ _ =>
      rw [adviceWritesDistinct_loadTable_cons] at h
      exact .loadTable (ih i₀ h)

end Consistent

end Operations

end Halo2
