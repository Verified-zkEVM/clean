import Clean.Halo2.Configure
import Clean.Halo2.Provable
import Clean.Halo2.SynthesisSummaryAttr
import Clean.Halo2.WitnessIR

/-!
# Halo2 synthesize-layer operations — DESIGN SKETCH

Port of the operation layer of `Clean/Circuit/Operations.lean` to halo2. Two levels of
operations, mirroring Rust's two synthesize APIs:

- Region level (Rust `Region<F>` methods): assignments, copies, gate enables — all at
  region-local rows. Region-level gadget composition (e.g.
  `add_incomplete.assign_region(…, offset, region)` called inside variable-base mul's
  big region) is row-offset-shifted, exactly Clean's offset-generic subcircuit pattern
  at row granularity.
- Layouter level (Rust `Layouter<F>`): creating regions, instance-column copies.
  Regions get indices from a threaded counter (prefix-computable, like Clean's offset);
  their *placement* `place : RegionIndex → ℕ` is a semantics parameter, computed at top
  level by the floor planner.

**The subcircuit mechanism** exists at *both* levels — it is what makes parent proofs
scale by isolating them from child circuit internals. Unlike main Clean (and per issue
Verified-zkEVM/clean#358), there is no `Subcircuit` type and no dedicated operation: a
subcircuit call simply *appends the child's operation list* (the monad's `bind` produces
`++`), so the operation enums are plain non-recursive lists. The proof boundary is not a
constructor but a *folded term*: the child ops appear in parent hypotheses as
`Constraints … ((child.call …).operations i)` with the list folded behind the
formal-circuit constant, isolated by the `constraints_append`/`regionCount_append`
lemma family. Consequences:

- There is a single ground-truth `Constraints` predicate. A subcircuit's constraints
  appear in parent hypotheses as one *opaque chunk* — never spilled into the parent's
  conjunction, because the folded call constant blocks list reduction.
- The contracts (`Spec`/`Assumptions`/prover variants) live on the formal-circuit
  packages, which provide per-circuit *forward lemmas*
  (`Constraints chunk → (Assumptions → Spec)` for soundness; the reverse direction for
  completeness). A custom tactic (`subcircuit_rw`) applies them — rewriting hypotheses
  to the weaker but higher-level spec form, which simp fundamentally cannot do. This
  replaces main Clean's `ConstraintsHold.Soundness`/`.Completeness` predicate variants.
- A layouter-level call advances the region counter by the child list's `regionCount`
  (per-circuit lemmas evaluate it to a literal); a region-level call contributes ops in
  the ambient region.
  TODO: the `SubcircuitsConsistent` discipline (cells in child ops reference the
  ambient region, by construction of the monad) ports with the formal-circuit layer.

Other key design points:

- **`enableGate` is itself subcircuit-like**: one operation that records the selector
  activation (for layout/VK compilation) *and* carries the gate's constraints (for
  semantics), so the semantics never needs the global `ConstraintSystem` threaded
  through. The bridge to the compiled CS's `∀ rows, guard·poly = 0` view is a
  once-per-circuit lemma at the VK boundary.
- **Assignments are witness-only**: `assignAdvice` creates a cell and its witness
  program (witgen IR over cell atoms; `.native` is the escape hatch); it adds no
  constraint. Copies and gate enables are the constraints.
- Lookups add no per-region operation: lookup arguments are CS-global and hold at every
  row. TODO: their satisfaction enters the top-level semantics with the lookup port.
- TODO: `Requirements`-style well-formedness (row bounds, no double assignment).

Rust reference: `halo2_proofs/src/circuit.rs` (`Region`, `Layouter`, `Cell`).
-/

namespace Halo2

variable {F : Type}

/-- An operation inside a region, at region-local rows. A region-level subcircuit call
appends the child fragment's operations (sharing the caller's region). Consistency of
subcircuit cells with the ambient region (`SubcircuitsConsistent` in main Clean) is
maintained by the circuit monad and ported with the formal-circuit layer. -/
inductive RegionOperation (F : Type) where
  /-- Witness a value into an advice cell at a local row. Rust: `region.assign_advice`.
  Adds no constraint. -/
  | assignAdvice : Column .advice → ℕ → WitgenIR F 1 → RegionOperation F
  /-- Assign a fixed cell. Rust: `region.assign_fixed`. Pins the fixed column's value
  (fixed values are circuit data; the assignment is checked by the semantics and feeds
  the VK's fixed columns). -/
  | assignFixed : Column .fixed → ℕ → F → RegionOperation F
  /-- Enable a gate at a local row. Rust: `selector.enable(region, offset)`. Records the
  activation of `gate.selector` and carries `gate.constraints` for semantics. -/
  | enableGate : Gate F → ℕ → RegionOperation F
  /-- Enable a lookup argument at a local row (the dual of `enableGate`). There is no
  single Rust method: a gadget "enables a lookup at a row" by enabling the complex
  selector(s) its input expressions are gated on; in the port
  `enableLookup arg enabled row` is the sugar the gadget's `synthesize` emits alongside
  those `enable`s. Carries the registered `LookupArgument` (its input/table tuples) for
  semantics plus `enabled`, the selectors turned on at *this* row. Unlike a gate — whose
  polynomials only ever contain its own single selector — a lookup input's gating
  selectors genuinely vary per enabled row (range-check: `q_lookup = 1` at every
  participating row, but `q_running` is 1 only at running-sum rows and 0 at short rows,
  selecting *which* word is looked up — `lookup-design.md` §1.4). So the activation
  valuation is the per-row `enabled ↦ 1, rest ↦ 0`, not a fixed own-selector device. -/
  | enableLookup : LookupArgument F → List Selector → ℕ → RegionOperation F
  /-- Copy constraint between two (possibly cross-region) cells.
  Rust: `region.constrain_equal`. -/
  | constrainEqual : Cell → Cell → RegionOperation F
  /-- Copy constraint against the constants column. Rust: `region.constrain_constant`. -/
  | constrainConstant : Cell → F → RegionOperation F
  /-- Copy constraint between a cell and an instance-column row, recorded inside the
  region (Rust: the copy half of `region.assign_advice_from_instance`). The instance row
  is absolute. Rust's fused `assign_advice_from_instance` is monad sugar — an
  `assignAdvice` witnessing the instance value plus this copy; see `Basic.lean`. -/
  | constrainInstance : Cell → Column .instance → ℕ → RegionOperation F

abbrev RegionOperations (F : Type) := List (RegionOperation F)

/-- A layouter-level operation: regions, instance copies, table loads. Subcircuit calls
contribute no operation of their own — they append the child gadget's operations. -/
inductive Operation (F : Type) where
  /-- A named region containing region-level operations. The region's index is not
  stored: like Clean's offsets, indices are recomputed by the semantics while folding. -/
  | region : String → RegionOperations F → Operation F
  /-- Copy constraint between a cell and an instance-column row.
  Rust: `layouter.constrain_instance`. -/
  | constrainInstance : Cell → Column .instance → ℕ → Operation F
  /-- Load a lookup table: fill a `TableColumn` (a fixed column) with `values` at absolute
  rows `[0, values.length)`, then default-fill every remaining usable row with the row-0
  value. Rust: `layouter.assign_table` (`table_layouter.rs`) + the floor planner's
  `fill_from_row` default-fill (`single_pass.rs:176-182`). Addresses absolute rows, so it
  is a layouter-level op, not a region op. See `lookup-design.md` §2.4. -/
  | loadTable : TableColumn → List F → Operation F

abbrev Operations (F : Type) := List (Operation F)

/-! ## Compositional synthesis footprint

The floor planner measures columns and row extents from the synthesis stream.  Keep
that vocabulary here, below both circuit monads, so formal circuits can expose a small
exact summary without exposing their operation lists. -/

namespace FloorPlanner

/-- A concrete or virtual column participating in a region's floor-planner shape. -/
inductive RegionColumn where
  | column : ColumnKind → ℕ → RegionColumn
  | selector : ℕ → RegionColumn
deriving DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

namespace RegionColumn

/-- `Any`'s consensus-critical ordering rank. -/
def kindRank : ColumnKind → ℕ
  | .instance => 0
  | .advice => 1
  | .fixed => 2

/-- An injective key used by hashing and the floor planner's ordering. -/
def ordKey : RegionColumn → ℕ × ℕ × ℕ
  | .column kind index => (0, kindRank kind, index)
  | .selector index => (1, 0, index)

instance : Hashable RegionColumn := ⟨fun column => hash column.ordKey⟩

/-- The consensus-critical strict order used by Halo 2's V1 planner. -/
def lt (left right : RegionColumn) : Bool :=
  let (leftGroup, leftKind, leftIndex) := left.ordKey
  let (rightGroup, rightKind, rightIndex) := right.ordKey
  leftGroup < rightGroup ||
    (leftGroup == rightGroup &&
      (leftKind < rightKind ||
        (leftKind == rightKind && leftIndex < rightIndex)))

def isAdvice : RegionColumn → Bool
  | .column .advice _ => true
  | _ => false

end RegionColumn

/-- Add a column to a first-seen-order finite set. -/
def addColumn (columns : List RegionColumn) (column : RegionColumn) :
    List RegionColumn :=
  if column ∈ columns then columns else columns ++ [column]

/-- Union two first-seen-order finite column sets. -/
def unionColumns (left right : List RegionColumn) : List RegionColumn :=
  right.foldl addColumn left

theorem mem_foldl_addColumn_iff
    (added initial : List RegionColumn) (column : RegionColumn) :
    column ∈ added.foldl addColumn initial ↔
      column ∈ initial ∨ column ∈ added := by
  induction added generalizing initial with
  | nil => simp
  | cons head rest inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      by_cases hhead : head ∈ initial
      · simp only [addColumn, hhead, ↓reduceIte, List.mem_cons]
        aesop
      · simp only [addColumn, hhead, ↓reduceIte, List.mem_append,
          List.mem_cons]
        aesop

/-- The one-past-last row measured for a region operation. -/
@[circuit_norm] def regionOperationRowExtent : RegionOperation F → ℕ
  | .assignAdvice _ row _
  | .assignFixed _ row _
  | .enableGate _ row
  | .enableLookup _ _ row => row + 1
  | .constrainEqual _ _
  | .constrainConstant _ _
  | .constrainInstance _ _ _ => 0

/-- The columns added to a region shape by one operation. -/
@[circuit_norm] def regionOperationShapeColumns : RegionOperation F → List RegionColumn
  | .assignAdvice column _ _ => [.column .advice column.index]
  | .assignFixed column _ _ => [.column .fixed column.index]
  | .enableGate gate _ => [.selector gate.selector.index]
  | .enableLookup _ enabled _ => enabled.map fun selector => .selector selector.index
  | .constrainEqual _ _
  | .constrainConstant _ _
  | .constrainInstance _ _ _ => []

/-- Whether an operation asks V1 to allocate a deferred constant cell. -/
@[circuit_norm] def regionOperationConstantSiteCount : RegionOperation F → ℕ
  | .constrainConstant _ _ => 1
  | _ => 0

/-- Exact summary of a fragment synthesized inside one ambient region. -/
@[ext] structure RegionSynthesisSummary where
  columns : List RegionColumn := []
  rowCount : ℕ := 0
  constantSiteCount : ℕ := 0

namespace RegionSynthesisSummary

def combine (left right : RegionSynthesisSummary) : RegionSynthesisSummary where
  columns := left.columns ++ right.columns
  rowCount := max left.rowCount right.rowCount
  constantSiteCount := left.constantSiteCount + right.constantSiteCount

@[circuit_norm] theorem combine_columns (left right : RegionSynthesisSummary) :
    (left.combine right).columns = left.columns ++ right.columns := rfl

@[circuit_norm] theorem combine_rowCount (left right : RegionSynthesisSummary) :
    (left.combine right).rowCount = max left.rowCount right.rowCount := rfl

@[circuit_norm] theorem combine_constantSiteCount
    (left right : RegionSynthesisSummary) :
    (left.combine right).constantSiteCount =
      left.constantSiteCount + right.constantSiteCount := rfl

@[circuit_norm] theorem combine_empty (summary : RegionSynthesisSummary) :
    summary.combine {} = summary := by
  cases summary
  simp [combine]

@[circuit_norm] theorem empty_combine (summary : RegionSynthesisSummary) :
    ({} : RegionSynthesisSummary).combine summary = summary := by
  cases summary
  simp [combine]

def ofOperation (operation : RegionOperation F) : RegionSynthesisSummary where
  columns := regionOperationShapeColumns operation
  rowCount := regionOperationRowExtent operation
  constantSiteCount := regionOperationConstantSiteCount operation

@[circuit_norm] theorem ofOperation_columns (operation : RegionOperation F) :
    (ofOperation operation).columns = regionOperationShapeColumns operation := rfl

@[circuit_norm] theorem ofOperation_rowCount (operation : RegionOperation F) :
    (ofOperation operation).rowCount = regionOperationRowExtent operation := rfl

@[circuit_norm] theorem ofOperation_constantSiteCount
    (operation : RegionOperation F) :
    (ofOperation operation).constantSiteCount =
      regionOperationConstantSiteCount operation := rfl

end RegionSynthesisSummary

/-- Exact synthesis summary of a region-operation stream. -/
def regionSynthesisSummary : RegionOperations F → RegionSynthesisSummary
  | [] => {}
  | operation :: rest =>
      (RegionSynthesisSummary.ofOperation operation).combine
        (regionSynthesisSummary rest)

@[circuit_norm] theorem regionSynthesisSummary_nil_columns :
    (regionSynthesisSummary ([] : RegionOperations F)).columns = [] := rfl

@[circuit_norm] theorem regionSynthesisSummary_nil_rowCount :
    (regionSynthesisSummary ([] : RegionOperations F)).rowCount = 0 := rfl

@[circuit_norm] theorem regionSynthesisSummary_nil_constantSiteCount :
    (regionSynthesisSummary ([] : RegionOperations F)).constantSiteCount = 0 := rfl

@[circuit_norm] theorem regionSynthesisSummary_cons_columns
    (operation : RegionOperation F) (rest : RegionOperations F) :
    (regionSynthesisSummary (operation :: rest)).columns =
      regionOperationShapeColumns operation ++
        (regionSynthesisSummary rest).columns := rfl

@[circuit_norm] theorem regionSynthesisSummary_cons_rowCount
    (operation : RegionOperation F) (rest : RegionOperations F) :
    (regionSynthesisSummary (operation :: rest)).rowCount =
      max (regionOperationRowExtent operation)
        (regionSynthesisSummary rest).rowCount := rfl

@[circuit_norm] theorem regionSynthesisSummary_cons_constantSiteCount
    (operation : RegionOperation F) (rest : RegionOperations F) :
    (regionSynthesisSummary (operation :: rest)).constantSiteCount =
      regionOperationConstantSiteCount operation +
        (regionSynthesisSummary rest).constantSiteCount := rfl

theorem regionOperationRowExtent_le_synthesisSummary_of_mem
    (operations : RegionOperations F) (operation : RegionOperation F)
    (hoperation : operation ∈ operations) :
    regionOperationRowExtent operation ≤
      (regionSynthesisSummary operations).rowCount := by
  induction operations with
  | nil => simp at hoperation
  | cons head rest inductionHypothesis =>
      rw [List.mem_cons] at hoperation
      simp only [regionSynthesisSummary, RegionSynthesisSummary.combine,
        RegionSynthesisSummary.ofOperation]
      rcases hoperation with rfl | hrest
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis hrest).trans (Nat.le_max_right _ _)

theorem mem_regionSynthesisSummary_columns_of_mem
    (operations : RegionOperations F) (operation : RegionOperation F)
    (hoperation : operation ∈ operations) (column : RegionColumn)
    (hcolumn : column ∈ regionOperationShapeColumns operation) :
    column ∈ (regionSynthesisSummary operations).columns := by
  induction operations with
  | nil => simp at hoperation
  | cons head rest inductionHypothesis =>
      rw [List.mem_cons] at hoperation
      simp only [regionSynthesisSummary, RegionSynthesisSummary.combine,
        RegionSynthesisSummary.ofOperation, List.mem_append]
      rcases hoperation with rfl | hrest
      · exact Or.inl hcolumn
      · exact Or.inr (inductionHypothesis hrest)

/-- Exact summary of a layouter synthesis stream.  `columnOccupancy column` is the
sum of region heights allocated in `column`; placement can move those intervals but
cannot change their total occupied length. -/
@[ext] structure SynthesisSummary where
  columns : List RegionColumn := []
  columnOccupancy : RegionColumn → ℕ := fun _ => 0
  constantSiteCount : ℕ := 0

namespace SynthesisSummary

def combine (left right : SynthesisSummary) : SynthesisSummary where
  columns := left.columns ++ right.columns
  columnOccupancy := fun column =>
    left.columnOccupancy column + right.columnOccupancy column
  constantSiteCount := left.constantSiteCount + right.constantSiteCount

@[circuit_norm] theorem combine_columns (left right : SynthesisSummary) :
    (left.combine right).columns = left.columns ++ right.columns := rfl

@[circuit_norm] theorem combine_columnOccupancy
    (left right : SynthesisSummary) (column : RegionColumn) :
    (left.combine right).columnOccupancy column =
      left.columnOccupancy column + right.columnOccupancy column := rfl

@[circuit_norm] theorem combine_constantSiteCount
    (left right : SynthesisSummary) :
    (left.combine right).constantSiteCount =
      left.constantSiteCount + right.constantSiteCount := rfl

@[circuit_norm] theorem combine_empty (summary : SynthesisSummary) :
    summary.combine {} = summary := by
  apply SynthesisSummary.ext
  · simp [combine]
  · funext column
    simp [combine]
  · simp [combine]

@[circuit_norm] theorem empty_combine (summary : SynthesisSummary) :
    ({} : SynthesisSummary).combine summary = summary := by
  apply SynthesisSummary.ext
  · simp [combine]
  · funext column
    simp [combine]
  · simp [combine]

def ofRegion (summary : RegionSynthesisSummary) : SynthesisSummary where
  columns := summary.columns
  columnOccupancy := fun column =>
    if column ∈ summary.columns then summary.rowCount else 0
  constantSiteCount := summary.constantSiteCount

@[circuit_norm] theorem ofRegion_columns (summary : RegionSynthesisSummary) :
    (ofRegion summary).columns = summary.columns := rfl

@[circuit_norm] theorem ofRegion_columnOccupancy
    (summary : RegionSynthesisSummary) (column : RegionColumn) :
    (ofRegion summary).columnOccupancy column =
      if column ∈ summary.columns then summary.rowCount else 0 := rfl

@[circuit_norm] theorem ofRegion_constantSiteCount
    (summary : RegionSynthesisSummary) :
    (ofRegion summary).constantSiteCount = summary.constantSiteCount := rfl

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
        intro accumulator haccumulator hvalues
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
  | .constrainInstance _ _ _ :: rest => synthesisSummary rest
  | .loadTable _ _ :: rest => synthesisSummary rest

@[circuit_norm] theorem synthesisSummary_nil_columns :
    (synthesisSummary ([] : Operations F)).columns = [] := rfl

@[circuit_norm] theorem synthesisSummary_nil_columnOccupancy
    (column : RegionColumn) :
    (synthesisSummary ([] : Operations F)).columnOccupancy column = 0 := rfl

@[circuit_norm] theorem synthesisSummary_nil_constantSiteCount :
    (synthesisSummary ([] : Operations F)).constantSiteCount = 0 := rfl

@[circuit_norm] theorem synthesisSummary_region_cons_columns
    (name : String) (body : RegionOperations F) (rest : Operations F) :
    (synthesisSummary (.region name body :: rest)).columns =
      (regionSynthesisSummary body).columns ++
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

@[circuit_norm] theorem synthesisSummary_constrainInstance_cons_columns
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : Operations F) :
    (synthesisSummary (.constrainInstance cell column row :: rest)).columns =
      (synthesisSummary rest).columns := rfl

@[circuit_norm] theorem synthesisSummary_constrainInstance_cons_columnOccupancy
    (cell : Cell) (instanceColumn : Column .instance) (row : ℕ)
    (rest : Operations F) (column : RegionColumn) :
    (synthesisSummary
      (.constrainInstance cell instanceColumn row :: rest)).columnOccupancy column =
        (synthesisSummary rest).columnOccupancy column := rfl

@[circuit_norm] theorem synthesisSummary_constrainInstance_cons_constantSiteCount
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : Operations F) :
    (synthesisSummary
      (.constrainInstance cell column row :: rest)).constantSiteCount =
        (synthesisSummary rest).constantSiteCount := rfl

@[circuit_norm] theorem synthesisSummary_loadTable_cons_columns
    (column : TableColumn) (values : List F) (rest : Operations F) :
    (synthesisSummary (.loadTable column values :: rest)).columns =
      (synthesisSummary rest).columns := rfl

@[circuit_norm] theorem synthesisSummary_loadTable_cons_columnOccupancy
    (tableColumn : TableColumn) (values : List F) (rest : Operations F)
    (column : RegionColumn) :
    (synthesisSummary (.loadTable tableColumn values :: rest)).columnOccupancy column =
      (synthesisSummary rest).columnOccupancy column := rfl

@[circuit_norm] theorem synthesisSummary_loadTable_cons_constantSiteCount
    (column : TableColumn) (values : List F) (rest : Operations F) :
    (synthesisSummary (.loadTable column values :: rest)).constantSiteCount =
      (synthesisSummary rest).constantSiteCount := rfl

@[circuit_norm] theorem regionSynthesisSummary_append
    (left right : RegionOperations F) :
    regionSynthesisSummary (left ++ right) =
      (regionSynthesisSummary left).combine (regionSynthesisSummary right) := by
  induction left with
  | nil =>
      apply RegionSynthesisSummary.ext <;>
        simp [RegionSynthesisSummary.combine, regionSynthesisSummary]
  | cons operation rest inductionHypothesis =>
      simp only [List.cons_append, regionSynthesisSummary,
        inductionHypothesis]
      apply RegionSynthesisSummary.ext
      · simp [RegionSynthesisSummary.combine]
      · simp [RegionSynthesisSummary.combine, Nat.max_assoc]
      · simp [RegionSynthesisSummary.combine, Nat.add_assoc]

@[circuit_norm] theorem synthesisSummary_append
    (left right : Operations F) :
    synthesisSummary (left ++ right) =
      (synthesisSummary left).combine (synthesisSummary right) := by
  induction left with
  | nil =>
      apply SynthesisSummary.ext
      · simp [SynthesisSummary.combine, synthesisSummary]
      · funext column
        simp [SynthesisSummary.combine, synthesisSummary]
      · simp [SynthesisSummary.combine, synthesisSummary]
  | cons operation rest inductionHypothesis =>
      cases operation <;>
        simp only [List.cons_append, synthesisSummary,
          inductionHypothesis]
      · apply SynthesisSummary.ext
        · simp [SynthesisSummary.combine]
        · funext column
          simp [SynthesisSummary.combine, Nat.add_assoc]
        · simp [SynthesisSummary.combine, Nat.add_assoc]

attribute [synthesis_summary_norm]
  regionOperationRowExtent
  regionOperationShapeColumns
  regionOperationConstantSiteCount
  RegionSynthesisSummary.combine_columns
  RegionSynthesisSummary.combine_rowCount
  RegionSynthesisSummary.combine_constantSiteCount
  RegionSynthesisSummary.ofOperation_columns
  RegionSynthesisSummary.ofOperation_rowCount
  RegionSynthesisSummary.ofOperation_constantSiteCount
  regionSynthesisSummary_nil_columns
  regionSynthesisSummary_nil_rowCount
  regionSynthesisSummary_nil_constantSiteCount
  regionSynthesisSummary_cons_columns
  regionSynthesisSummary_cons_rowCount
  regionSynthesisSummary_cons_constantSiteCount
  SynthesisSummary.combine_columns
  SynthesisSummary.combine_columnOccupancy
  SynthesisSummary.combine_constantSiteCount
  SynthesisSummary.ofRegion_columns
  SynthesisSummary.ofRegion_columnOccupancy
  SynthesisSummary.ofRegion_constantSiteCount
  synthesisSummary_nil_columns
  synthesisSummary_nil_columnOccupancy
  synthesisSummary_nil_constantSiteCount
  synthesisSummary_region_cons_columns
  synthesisSummary_region_cons_columnOccupancy
  synthesisSummary_region_cons_constantSiteCount
  synthesisSummary_constrainInstance_cons_columns
  synthesisSummary_constrainInstance_cons_columnOccupancy
  synthesisSummary_constrainInstance_cons_constantSiteCount
  synthesisSummary_loadTable_cons_columns
  synthesisSummary_loadTable_cons_columnOccupancy
  synthesisSummary_loadTable_cons_constantSiteCount
  regionSynthesisSummary_append
  synthesisSummary_append

end FloorPlanner

/-! ## Configure/synthesis registration -/

/--
Gate, lookup, and equality-column capabilities supplied by a circuit's caller rather
than created by the circuit's own configure program.

This is the keygen analogue of an effect requirement: leaf region circuits commonly
receive an already-configured chip `Config` and use its arguments while contributing
no configure delta of their own.
-/
structure KeygenRequirements (F ConfigInput InputVar : Type) where
  /--
  Provenance required of configuration values borrowed from the caller. This stays
  folded across circuit boundaries; it never exposes a child's operation stream.
  -/
  configLawful : ConfigInput → Type := fun _ => Unit
  gates : ∀ input, configLawful input → List (Gate F) := fun _ _ => []
  lookups : ∀ input, configLawful input → List (LookupArgument F) := fun _ _ => []
  permutationColumns : ∀ input, configLawful input → List AnyColumn := fun _ _ => []
  /-- Equality-enabled columns required by the concrete cells passed to synthesis. -/
  inputPermutationColumns : ∀ configInput, configLawful configInput →
      InputVar → List AnyColumn := fun _ _ _ => []

/-- A configure input has no keygen requirements left for an enclosing circuit. -/
structure KeygenRequirements.EmptyAt
    {ConfigInput InputVar : Type}
    (self : KeygenRequirements F ConfigInput InputVar)
    (input : ConfigInput) where
  configLawful : self.configLawful input
  gates_eq : self.gates input configLawful = []
  lookups_eq : self.lookups input configLawful = []
  permutationColumns_eq : self.permutationColumns input configLawful = []
  inputPermutationColumns_eq : ∀ inputVar,
    self.inputPermutationColumns input configLawful inputVar = []

/--
Static registration of one region operation in explicit configure-produced gate and
lookup lists.

Assignments need no configure-phase registration. Gate and lookup activations must
refer to arguments emitted by configure; copy-like operations must use columns on
which configure enabled equality.
-/
@[circuit_norm]
def RegionOperation.KeygenRegistered
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (permutationColumns : List AnyColumn) :
    RegionOperation F → Prop
  | .enableGate gate _ => gate ∈ gates
  | .enableLookup argument _ _ => argument ∈ lookups
  | .constrainEqual left right =>
      left.column ∈ permutationColumns ∧ right.column ∈ permutationColumns
  | .constrainConstant cell _ => cell.column ∈ permutationColumns
  | .constrainInstance cell column _ =>
      cell.column ∈ permutationColumns ∧ column.toAny ∈ permutationColumns
  | _ => True

/-- Static registration of one layouter operation in explicit configure metadata. -/
@[circuit_norm]
def Operation.KeygenRegistered
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (permutationColumns : List AnyColumn) :
    Operation F → Prop
  | .region _ body =>
      body.Forall (RegionOperation.KeygenRegistered gates lookups permutationColumns)
  | .constrainInstance cell column _ =>
      cell.column ∈ permutationColumns ∧ column.toAny ∈ permutationColumns
  | _ => True

/--
Every gate, lookup, and equality-dependent operation emitted by synthesis is covered
by the supplied configure-produced capabilities.
-/
def Operations.KeygenRegistered
    (operations : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (permutationColumns : List AnyColumn) : Prop :=
  operations.Forall (Operation.KeygenRegistered gates lookups permutationColumns)

@[circuit_norm]
theorem Operations.KeygenRegistered.nil
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered [] gates lookups permutationColumns := by
  simp [Operations.KeygenRegistered]

@[circuit_norm]
theorem Operations.KeygenRegistered.append
    (left right : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered (left ++ right) gates lookups permutationColumns ↔
      Operations.KeygenRegistered left gates lookups permutationColumns ∧
        Operations.KeygenRegistered right gates lookups permutationColumns := by
  simp [Operations.KeygenRegistered]

@[circuit_norm]
theorem Operations.KeygenRegistered.region_cons
    (name : String) (body : RegionOperations F) (rest : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered (.region name body :: rest) gates lookups permutationColumns ↔
      body.Forall (RegionOperation.KeygenRegistered gates lookups permutationColumns) ∧
        Operations.KeygenRegistered rest gates lookups permutationColumns := by
  simp [Operations.KeygenRegistered, Operation.KeygenRegistered]

@[circuit_norm]
theorem Operations.KeygenRegistered.constrainInstance_cons
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered
        (.constrainInstance cell column row :: rest) gates lookups permutationColumns ↔
      cell.column ∈ permutationColumns ∧ column.toAny ∈ permutationColumns ∧
        Operations.KeygenRegistered rest gates lookups permutationColumns := by
  simp [Operations.KeygenRegistered, Operation.KeygenRegistered, and_assoc]

@[circuit_norm]
theorem Operations.KeygenRegistered.loadTable_cons
    (table : TableColumn) (values : List F) (rest : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered
        (.loadTable table values :: rest) gates lookups permutationColumns ↔
      Operations.KeygenRegistered rest gates lookups permutationColumns := by
  simp [Operations.KeygenRegistered, Operation.KeygenRegistered]

/-- Registration is monotone in both configure-produced argument lists. -/
theorem Operations.KeygenRegistered.mono
    {operations : Operations F}
    {sourceGates targetGates : List (Gate F)}
    {sourceLookups targetLookups : List (LookupArgument F)}
    {sourcePermutationColumns targetPermutationColumns : List AnyColumn}
    (hregistered :
      operations.KeygenRegistered sourceGates sourceLookups sourcePermutationColumns)
    (hgates : ∀ gate, gate ∈ sourceGates → gate ∈ targetGates)
    (hlookups :
      ∀ argument, argument ∈ sourceLookups → argument ∈ targetLookups)
    (hpermutationColumns : ∀ column,
      column ∈ sourcePermutationColumns → column ∈ targetPermutationColumns) :
    operations.KeygenRegistered targetGates targetLookups targetPermutationColumns := by
  rw [Operations.KeygenRegistered,
    List.forall_iff_forall_mem] at hregistered ⊢
  intro operation hoperation
  have hoperationRegistered := hregistered operation hoperation
  cases operation with
  | region name body =>
      rw [Operation.KeygenRegistered,
        List.forall_iff_forall_mem] at hoperationRegistered ⊢
      intro regionOperation hregionOperation
      have hregionRegistered :=
        hoperationRegistered regionOperation hregionOperation
      cases regionOperation with
      | enableGate gate row =>
          exact hgates gate hregionRegistered
      | enableLookup argument selectors row =>
          exact hlookups argument hregionRegistered
      | assignAdvice
      | assignFixed =>
          trivial
      | constrainEqual left right =>
          exact ⟨hpermutationColumns left.column hregionRegistered.1,
            hpermutationColumns right.column hregionRegistered.2⟩
      | constrainConstant cell value =>
          exact hpermutationColumns cell.column hregionRegistered
      | constrainInstance cell column row =>
          exact ⟨hpermutationColumns cell.column hregionRegistered.1,
            hpermutationColumns column.toAny hregionRegistered.2⟩
  | constrainInstance cell column row =>
      exact ⟨hpermutationColumns cell.column hoperationRegistered.1,
        hpermutationColumns column.toAny hoperationRegistered.2⟩
  | loadTable =>
      trivial

/-- Region-operation registration is monotone in both available argument lists. -/
theorem RegionOperations.keygenRegistered_mono
    {operations : RegionOperations F}
    {sourceGates targetGates : List (Gate F)}
    {sourceLookups targetLookups : List (LookupArgument F)}
    {sourcePermutationColumns targetPermutationColumns : List AnyColumn}
    (hregistered :
      operations.Forall
        (RegionOperation.KeygenRegistered sourceGates sourceLookups
          sourcePermutationColumns))
    (hgates : ∀ gate, gate ∈ sourceGates → gate ∈ targetGates)
    (hlookups :
      ∀ argument, argument ∈ sourceLookups → argument ∈ targetLookups)
    (hpermutationColumns : ∀ column,
      column ∈ sourcePermutationColumns → column ∈ targetPermutationColumns) :
    operations.Forall
      (RegionOperation.KeygenRegistered targetGates targetLookups
        targetPermutationColumns) := by
  rw [List.forall_iff_forall_mem] at hregistered ⊢
  intro operation hoperation
  have hoperationRegistered := hregistered operation hoperation
  cases operation with
  | enableGate gate row =>
      exact hgates gate hoperationRegistered
  | enableLookup argument selectors row =>
      exact hlookups argument hoperationRegistered
  | assignAdvice
  | assignFixed =>
      trivial
  | constrainEqual left right =>
      exact ⟨hpermutationColumns left.column hoperationRegistered.1,
        hpermutationColumns right.column hoperationRegistered.2⟩
  | constrainConstant cell value =>
      exact hpermutationColumns cell.column hoperationRegistered
  | constrainInstance cell column row =>
      exact ⟨hpermutationColumns cell.column hoperationRegistered.1,
        hpermutationColumns column.toAny hoperationRegistered.2⟩

/--
Registration against a configure delta remains true after interpreting that delta
over any initial constraint system.
-/
theorem Operations.KeygenRegistered.applyConfigureDelta
    {operations : Operations F} {delta : ConfigureDelta F}
    (initial : ConstraintSystem F) (counts : ConfigureCounts)
    (hregistered :
      operations.KeygenRegistered delta.gates delta.lookups
        delta.permutationRequests) :
    operations.KeygenRegistered
      (delta.apply initial counts).gates
      (delta.apply initial counts).lookups
      (delta.apply initial counts).permutationColumns := by
  apply hregistered.mono
  · intro gate hgate
    exact List.mem_append_right initial.gates hgate
  · intro argument hargument
    exact List.mem_append_right initial.lookups hargument
  · intro column hcolumn
    rw [ConfigureDelta.apply, mem_appendFirstEncounters]
    exact Or.inr hcolumn

/-- Existing constraint-system spelling of configure/synthesis registration. -/
@[circuit_norm]
def RegionOperation.KeygenCoherent
    (cs : ConstraintSystem F) : RegionOperation F → Prop :=
  RegionOperation.KeygenRegistered cs.gates cs.lookups cs.permutationColumns

/-- Existing constraint-system spelling of configure/synthesis registration. -/
@[circuit_norm]
def Operation.KeygenCoherent
    (cs : ConstraintSystem F) : Operation F → Prop :=
  Operation.KeygenRegistered cs.gates cs.lookups cs.permutationColumns

/-- Every synthesis-enabled argument was registered in a constraint system. -/
def OperationsKeygenCoherent
    (cs : ConstraintSystem F) (operations : Operations F) : Prop :=
  operations.KeygenRegistered cs.gates cs.lookups cs.permutationColumns

@[circuit_norm]
theorem OperationsKeygenCoherent.nil
    (cs : ConstraintSystem F) :
    OperationsKeygenCoherent cs [] := by
  exact Operations.KeygenRegistered.nil cs.gates cs.lookups cs.permutationColumns

/-- Configure/synthesis coherence composes across operation-stream append. -/
@[circuit_norm]
theorem OperationsKeygenCoherent.append
    (cs : ConstraintSystem F) (left right : Operations F) :
    OperationsKeygenCoherent cs (left ++ right) ↔
      OperationsKeygenCoherent cs left ∧
        OperationsKeygenCoherent cs right := by
  exact Operations.KeygenRegistered.append
    left right cs.gates cs.lookups cs.permutationColumns

/-- A region is coherent exactly when each operation in its body is coherent. -/
@[circuit_norm]
theorem OperationsKeygenCoherent.region_cons
    (cs : ConstraintSystem F) (name : String)
    (body : RegionOperations F) (rest : Operations F) :
    OperationsKeygenCoherent cs (.region name body :: rest) ↔
      body.Forall (RegionOperation.KeygenCoherent cs) ∧
        OperationsKeygenCoherent cs rest := by
  exact Operations.KeygenRegistered.region_cons
    name body rest cs.gates cs.lookups cs.permutationColumns

@[circuit_norm]
theorem OperationsKeygenCoherent.constrainInstance_cons
    (cs : ConstraintSystem F) (cell : Cell)
    (column : Column .instance) (row : ℕ) (rest : Operations F) :
    OperationsKeygenCoherent cs
        (.constrainInstance cell column row :: rest) ↔
      cell.column ∈ cs.permutationColumns ∧
        column.toAny ∈ cs.permutationColumns ∧
        OperationsKeygenCoherent cs rest := by
  exact Operations.KeygenRegistered.constrainInstance_cons
    cell column row rest cs.gates cs.lookups cs.permutationColumns

@[circuit_norm]
theorem OperationsKeygenCoherent.loadTable_cons
    (cs : ConstraintSystem F) (table : TableColumn)
    (values : List F) (rest : Operations F) :
    OperationsKeygenCoherent cs (.loadTable table values :: rest) ↔
      OperationsKeygenCoherent cs rest := by
  exact Operations.KeygenRegistered.loadTable_cons
    table values rest cs.gates cs.lookups cs.permutationColumns

/-- Delta registration supplies coherence in every interpreted configure result. -/
theorem Operations.KeygenRegistered.operationsKeygenCoherent_apply
    {operations : Operations F} {delta : ConfigureDelta F}
    (initial : ConstraintSystem F) (counts : ConfigureCounts)
    (hregistered :
      operations.KeygenRegistered delta.gates delta.lookups
        delta.permutationRequests) :
    OperationsKeygenCoherent (delta.apply initial counts) operations :=
  hregistered.applyConfigureDelta initial counts

/-! ## Selector activation vocabulary

These definitions describe the operation stream itself: which selector indices occur
syntactically in an expression, which selectors an operation enables, and which
operations activate a selector at a region-local row. Keeping them below the keygen
layer lets floor planning state its placement facts without importing keygen.
-/

/-- Selector indices occurring in an expression, with syntax-order multiplicity. -/
@[circuit_norm]
def Expression.selectorIndices : Expression F Query → List ℕ
  | .var (.selector selector) => [selector.index]
  | .var _ => []
  | .const _ => []
  | .add left right =>
      left.selectorIndices ++ right.selectorIndices
  | .mul left right =>
      left.selectorIndices ++ right.selectorIndices

/-- Membership in an enabled-selector list, by the index used by semantics. -/
@[circuit_norm]
def SelectorEnabledAtIndex
    (enabled : List Selector) (selector : ℕ) : Prop :=
  ∃ candidate ∈ enabled, candidate.index = selector

/-- An operation activates selector `selector` at region-local `row`. -/
@[circuit_norm]
def RegionOperation.ActivatesSelectorAt
    (selector row : ℕ) : RegionOperation F → Prop
  | .enableGate gate operationRow =>
      gate.selector.index = selector ∧ operationRow = row
  | .enableLookup _ enabled operationRow =>
      SelectorEnabledAtIndex enabled selector ∧ operationRow = row
  | _ => False

/-- Number of region indices a list of operations consumes (the `localLength`
analogue) — computed, not cached; per-circuit lemmas evaluate it to a literal. -/
def Operations.regionCount : Operations F → ℕ
  | [] => 0
  | .region _ _ :: ops => 1 + Operations.regionCount ops
  | .constrainInstance _ _ _ :: ops => Operations.regionCount ops
  | .loadTable _ _ :: ops => Operations.regionCount ops

section Semantics
variable [FiniteField F]

/-- Read a (possibly foreign) cell. NOT `@[circuit_norm]` (normal-form unification,
mirroring `AssignedCell.eval`): abstract cell reads stay folded; known-kind cells
reduce to the typed accessors via the `eval_of_*` rules below, so copy constraints
line up with the query/assigned-cell paths at the `env.advice` spelling. -/
def Cell.eval (place : RegionIndex → ℕ) (env : Environment F) (c : Cell) : F :=
  env.get c.column ((place c.regionIndex + c.rowOffset : ℕ) : ℤ)

omit [FiniteField F] in
/-- An assigned cell's `Cell.eval` is its `AssignedCell.eval` — ONE canonical folded
atom for abstract cell reads (copy constraints arrive at `Cell.eval x.cell`,
witness/assign facts at `AssignedCell.eval x`; without this they are separate folded
spellings that simp cannot cross). -/
@[circuit_norm]
lemma Cell.eval_cell [Field F] (place : RegionIndex → ℕ) (env : Environment F)
    (c : AssignedCell F) :
    Cell.eval place env c.cell = AssignedCell.eval place env c := rfl

omit [FiniteField F] in
@[circuit_norm]
lemma Cell.eval_of_advice (place : RegionIndex → ℕ) (env : Environment F)
    (self : RegionIndex) (row : ℕ) (col : Column .advice) :
    Cell.eval place env (.of self row col)
      = env.advice col ((place self + row : ℕ) : ℤ) := rfl

omit [FiniteField F] in
@[circuit_norm]
lemma Cell.eval_of_fixed (place : RegionIndex → ℕ) (env : Environment F)
    (self : RegionIndex) (row : ℕ) (col : Column .fixed) :
    Cell.eval place env (.of self row col)
      = env.fixed col ((place self + row : ℕ) : ℤ) := rfl

omit [FiniteField F] in
@[circuit_norm]
lemma Cell.eval_of_inst (place : RegionIndex → ℕ) (env : Environment F)
    (self : RegionIndex) (row : ℕ) (col : Column .instance) :
    Cell.eval place env (.of self row col)
      = env.inst col ((place self + row : ℕ) : ℤ) := rfl

/-- Constraints of one region operation, for a region with index `self`. A subcircuit
call's constraints are the *opaque chunk* `RegionOperations.Constraints … <folded child
ops>` — the proof boundary: parent hypotheses keep the chunk folded, and the per-circuit
forward lemmas (formal-circuit layer) rewrite it to the child's `Assumptions → Spec`. -/
def RegionOperation.Constraints (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) : RegionOperation F → Prop
  | .assignAdvice _ _ _ => True
  | .assignFixed col row v => env.get col (place self + row : ℕ) = v
  | .enableGate gate row =>
      -- compiled polys vanish under `own selector ↦ 1`; sound because genuine selectors
      -- never occur in a foreign gate's polynomials (see halo2-selector-survey.md).
      -- `List.Forall` (not `∀ c ∈ …`) so `circuit_norm` reduces it to a clean conjunction.
      gate.constraints.Forall fun c =>
        c.poly.eval (Query.eval env (fun i => if i = gate.selector.index then 1 else 0)
          (place self + row : ℕ)) = 0
  | .enableLookup arg enabled row =>
      -- membership (not permutation): the input tuple at this row equals the table tuple
      -- at *some* usable table row (`lookup-design.md` §2.2). The witness is bounded by
      -- `env.usableRows` for faithfulness: the prover truncates the input expression and
      -- builds the table multiset over `usable_rows = n − (blinding + 1)` only
      -- (`lookup/prover.rs:573-585`), so blinding rows never participate on either side.
      -- ℕ-with-cast spelling: table rows share the `(↑(n : ℕ) : ℤ)` row normal form of
      -- all other reads. Inputs are evaluated under the local activation valuation
      -- `enabled ↦ 1, rest ↦ 0` — which selectors are on at this row decides *which* word
      -- the gated input expression reduces to (running-sum vs short row, §1.4); the table
      -- side is a rotation-0 fixed query, unaffected by the valuation.
      ∃ tableRow : ℕ, tableRow < env.usableRows ∧
        arg.inputs.map (Expression.eval (Query.eval env
          (fun i => if i ∈ enabled.map Selector.index then 1 else 0) (place self + row : ℕ)))
        = arg.tables.map (Expression.eval (Query.eval env
          (fun i => if i ∈ enabled.map Selector.index then 1 else 0) (tableRow : ℤ)))
  | .constrainEqual a b => a.eval place env = b.eval place env
  | .constrainConstant a v => a.eval place env = v
  | .constrainInstance cell instCol instRow =>
      cell.eval place env = env.get instCol (instRow : ℤ)

/-- Constraints of a list of region operations. -/
def RegionOperations.Constraints (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment F) : RegionOperations F → Prop
  | [] => True
  | op :: ops =>
      op.Constraints place self env ∧ RegionOperations.Constraints place self env ops

/--
Ground truth: what it means that "constraints hold" on a sequence of operations,
*including* all constraints inside subcircuits (their ops are appended into the list).
The single satisfaction predicate (issue #358 — no separate `Soundness`/`Completeness`
views): `place` is the region placement (the analogue of main Clean's `offset`,
instantiated at top level with the floor planner's output), `i` the index of the next
region (threaded like Clean's offset). A folded subcircuit chunk in the middle of a
parent's list is isolated by `constraints_append`, advancing the region counter by the
chunk's `regionCount`.
-/
def Constraints (place : RegionIndex → ℕ) (env : Environment F) :
    Operations F → (i : RegionIndex) → Prop
  | [], _ => True
  | .region _ ops' :: ops, i =>
      ops'.Constraints place i env ∧ Constraints place env ops (i + 1)
  | .constrainInstance cell col row :: ops, i =>
      cell.eval place env = env.get col row ∧ Constraints place env ops i
  | .loadTable tbl values :: ops, i =>
      -- explicit block: rows `[0, values.length)` hold the loaded values
      (∀ r : ℕ, r < values.length → env.fixed tbl.inner (r : ℤ) = values[r]!) ∧
      -- default-fill (`lookup-design.md` §1.3.1): unused usable rows carry the row-0 value.
      -- Conditional on `values ≠ []` so an empty load imposes no bogus default.
      (values ≠ [] → ∀ r : ℕ, values.length ≤ r → r < env.usableRows →
        env.fixed tbl.inner (r : ℤ) = values[0]!) ∧
      Constraints place env ops i

/-- The witness condition for completeness: the environment assigns each advice cell
the value computed by its witness program (main Clean: `ExtendsVector`), and each fixed
cell the value the circuit assigns. The `assignFixed` clause mirrors its `Constraints`
equation — like `loadTable`'s witness clause (`ExtendsWitnesses` below): fixed-column
contents are circuit data the honest environment carries, so a completeness proof can
discharge the corresponding constraint (they are keygen-time assignments, not prover
witness choices). -/
def RegionOperation.ExtendsWitness (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) : RegionOperation F → Prop
  | .assignAdvice col row compute =>
      env.get col (place self + row : ℕ) = (compute.eval ⟨place, env⟩)[0]
  | .assignFixed col row v => env.get col (place self + row : ℕ) = v
  | _ => True

/-- Witness condition for a list of region operations. -/
def RegionOperations.ExtendsWitnesses (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : ProverEnvironment F) : RegionOperations F → Prop
  | [] => True
  | op :: ops =>
      op.ExtendsWitness place self env ∧ RegionOperations.ExtendsWitnesses place self env ops

/-- All-regions witness condition, threading the region counter like `Constraints`. -/
def ExtendsWitnesses (place : RegionIndex → ℕ) (env : ProverEnvironment F) :
    Operations F → (i : RegionIndex) → Prop
  | [], _ => True
  | .region _ ops' :: ops, i =>
      ops'.ExtendsWitnesses place i env ∧ ExtendsWitnesses place env ops (i + 1)
  | .constrainInstance _ _ _ :: ops, i => ExtendsWitnesses place env ops i
  | .loadTable tbl values :: ops, i =>
      -- The honest prover's environment holds exactly that column content: the explicit
      -- block plus the row-0 default-fill over the usable rows. Discharges the `loadTable`
      -- `Constraints` in the completeness proof of a table loader. See `lookup-design.md` §2.4.
      (∀ r : ℕ, r < values.length → env.fixed tbl.inner (r : ℤ) = values[r]!) ∧
      (values ≠ [] → ∀ r : ℕ, values.length ≤ r → r < env.usableRows →
        env.fixed tbl.inner (r : ℤ) = values[0]!) ∧
      ExtendsWitnesses place env ops i
end Semantics

end Halo2
