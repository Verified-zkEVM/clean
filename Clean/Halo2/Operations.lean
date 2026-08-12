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

theorem mem_unionColumns_iff
    (left right : List RegionColumn) (column : RegionColumn) :
    column ∈ unionColumns left right ↔ column ∈ left ∨ column ∈ right :=
  mem_foldl_addColumn_iff right left column

theorem unionColumns_addColumn_right
    (left right : List RegionColumn) (column : RegionColumn) :
    unionColumns left (addColumn right column) =
      addColumn (unionColumns left right) column := by
  by_cases hcolumn : column ∈ right
  · have hunion : column ∈ unionColumns left right :=
      (mem_unionColumns_iff left right column).2 (.inr hcolumn)
    rw [addColumn, if_pos hcolumn, addColumn, if_pos hunion]
  · rw [addColumn, if_neg hcolumn]
    unfold unionColumns
    rw [List.foldl_append]
    rfl

theorem unionColumns_assoc
    (left middle right : List RegionColumn) :
    unionColumns (unionColumns left middle) right =
      unionColumns left (unionColumns middle right) := by
  induction right generalizing middle with
  | nil => rfl
  | cons column rest inductionHypothesis =>
      change unionColumns
          (addColumn (unionColumns left middle) column) rest =
        unionColumns left (unionColumns (addColumn middle column) rest)
      rw [← unionColumns_addColumn_right]
      exact inductionHypothesis (addColumn middle column)

theorem unionColumns_normalize_right
    (left right : List RegionColumn) :
    unionColumns left (unionColumns [] right) = unionColumns left right := by
  rw [← unionColumns_assoc]
  rfl

/-- Unioning columns already present on the left changes nothing. -/
theorem unionColumns_eq_left_of_subset
    (left right : List RegionColumn) (hsubset : ∀ column ∈ right, column ∈ left) :
    unionColumns left right = left := by
  induction right generalizing left with
  | nil => rfl
  | cons column rest inductionHypothesis =>
      change unionColumns (addColumn left column) rest = left
      rw [addColumn, if_pos (hsubset column (by simp))]
      exact inductionHypothesis left fun candidate hcandidate =>
        hsubset candidate (by simp [hcandidate])

theorem unionColumns_self (columns : List RegionColumn) :
    unionColumns columns columns = columns :=
  unionColumns_eq_left_of_subset columns columns fun _ => id

theorem unionColumns_normalized_left (columns : List RegionColumn) :
    unionColumns (unionColumns [] columns) columns = unionColumns [] columns :=
  unionColumns_eq_left_of_subset _ _ fun column hcolumn =>
    (mem_unionColumns_iff [] columns column).2 (.inr hcolumn)

@[circuit_norm, synthesis_summary_norm]
theorem unionColumns_nil_right (columns : List RegionColumn) :
    unionColumns columns [] = columns := rfl

theorem unionColumns_normalize_append
    (left right : List RegionColumn) :
    unionColumns [] (left ++ right) =
      unionColumns (unionColumns [] left) (unionColumns [] right) := by
  unfold unionColumns
  rw [List.foldl_append]
  exact (unionColumns_normalize_right _ _).symm

/-- Appending only columns already covered by the first source list does not change
its normalized column summary. -/
theorem unionColumns_normalize_append_redundant
    (left right : List RegionColumn)
    (hsubset : ∀ column ∈ right, column ∈ left) :
    unionColumns [] (left ++ right) = unionColumns [] left := by
  rw [unionColumns_normalize_append]
  apply unionColumns_eq_left_of_subset
  intro column hcolumn
  have hright := (mem_unionColumns_iff [] right column).1 hcolumn
  have hright' : column ∈ right := hright.resolve_left (by simp)
  exact (mem_unionColumns_iff [] left column).2
    (.inr (hsubset column hright'))

/-- Adjacent normalized column fragments reduce to one normalized source list. -/
@[circuit_norm, synthesis_summary_norm]
theorem unionColumns_merge_normalized
    (left right : List RegionColumn) :
    unionColumns (unionColumns [] left) (unionColumns [] right) =
      unionColumns [] (left ++ right) :=
  (unionColumns_normalize_append left right).symm

@[circuit_norm, synthesis_summary_norm]
theorem unionColumns_collapse_normalized
    (left right : List RegionColumn)
    (rest : List RegionColumn) :
    unionColumns (unionColumns [] left)
        (unionColumns (unionColumns [] right) rest) =
      unionColumns (unionColumns [] (left ++ right)) rest := by
  rw [← unionColumns_assoc, ← unionColumns_normalize_append]

theorem mem_foldr_unionColumns_iff
    (columns : List (List RegionColumn)) (column : RegionColumn) :
    column ∈ columns.foldr unionColumns [] ↔
      ∃ members ∈ columns, column ∈ members := by
  induction columns with
  | nil => simp
  | cons members rest inductionHypothesis =>
      rw [List.foldr_cons, mem_unionColumns_iff, inductionHypothesis]
      aesop

theorem addColumn_nodup
    (columns : List RegionColumn) (column : RegionColumn)
    (hcolumns : columns.Nodup) :
    (addColumn columns column).Nodup := by
  by_cases hcolumn : column ∈ columns
  · simpa [addColumn, hcolumn]
  · simpa [addColumn, hcolumn] using
      hcolumns.append (by simp) (by simpa using hcolumn)

theorem unionColumns_nodup
    (left right : List RegionColumn) (hleft : left.Nodup) :
    (unionColumns left right).Nodup := by
  induction right generalizing left with
  | nil => exact hleft
  | cons column rest inductionHypothesis =>
      exact inductionHypothesis _ (addColumn_nodup left column hleft)

theorem unionColumns_empty_left
    (columns : List RegionColumn) (hcolumns : columns.Nodup) :
    unionColumns [] columns = columns := by
  have general : ∀ (left right : List RegionColumn), right.Nodup →
      (∀ column ∈ right, column ∉ left) →
      unionColumns left right = left ++ right := by
    intro left right hright hdisjoint
    induction right generalizing left with
    | nil => simp [unionColumns]
    | cons column rest inductionHypothesis =>
        rw [List.nodup_cons] at hright
        have hcolumn : column ∉ left := hdisjoint column (by simp)
        change unionColumns (addColumn left column) rest =
          left ++ column :: rest
        rw [addColumn, if_neg hcolumn]
        rw [inductionHypothesis (left ++ [column]) hright.2]
        · simp [List.append_assoc]
        · intro candidate hcandidate
          simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨hdisjoint candidate (by simp [hcandidate]),
            fun heq => hright.1 (heq ▸ hcandidate)⟩
  simpa using general [] columns hcolumns (by simp)

theorem unionColumns_normalized_nil_left (columns : List RegionColumn) :
    unionColumns [] (unionColumns [] columns) = unionColumns [] columns :=
  unionColumns_empty_left _ (unionColumns_nodup [] columns (by simp))

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

/-- The one-past-last absolute instance row named by a region operation. -/
@[circuit_norm] def regionOperationInstanceRowExtent : RegionOperation F → ℕ
  | .constrainInstance _ _ row => row + 1
  | _ => 0

/-- Exact summary of a fragment synthesized inside one ambient region. -/
@[ext] structure RegionSynthesisSummary where
  columns : List RegionColumn := []
  rowCount : ℕ := 0
  constantSiteCount : ℕ := 0
  instanceRowExtent : ℕ := 0

namespace RegionSynthesisSummary

/-- A reduced region summary from its distinct-column source list and exact numerical
footprint. -/
def ofColumns (columns : List RegionColumn) (rowCount constantSiteCount : ℕ)
    (instanceRowExtent : ℕ := 0) :
    RegionSynthesisSummary where
  columns := unionColumns [] columns
  rowCount := rowCount
  constantSiteCount := constantSiteCount
  instanceRowExtent := instanceRowExtent

/-- The closed-form summary of `count` repetitions of the same column shape,
whose `i`th repetition occupies through
`offset + stride * i + rowCount` and requests `constantSiteCount` constants. -/
def repeatColumns (columns : List RegionColumn) (offset stride rowCount
    constantSiteCount count : ℕ) : RegionSynthesisSummary :=
  if count = 0 then {}
  else
    ofColumns columns
      (offset + stride * (count - 1) + rowCount)
      (count * constantSiteCount)

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumns_columns (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ) :
    (repeatColumns columns offset stride rowCount constantSiteCount count).columns =
      if count = 0 then [] else unionColumns [] columns := by
  cases count <;> rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumns_rowCount (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ) :
    (repeatColumns columns offset stride rowCount constantSiteCount count).rowCount =
      if count = 0 then 0 else offset + stride * (count - 1) + rowCount := by
  cases count <;> rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumns_constantSiteCount (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ) :
    (repeatColumns columns offset stride rowCount constantSiteCount count).constantSiteCount =
      count * constantSiteCount := by
  cases count <;> simp [repeatColumns, ofColumns]

@[circuit_norm, synthesis_summary_norm] theorem ofColumns_columns
    (columns : List RegionColumn) (rowCount constantSiteCount : ℕ) :
    (ofColumns columns rowCount constantSiteCount).columns =
      unionColumns [] columns := rfl

@[circuit_norm, synthesis_summary_norm] theorem ofColumns_rowCount
    (columns : List RegionColumn) (rowCount constantSiteCount : ℕ) :
    (ofColumns columns rowCount constantSiteCount).rowCount = rowCount := rfl

@[circuit_norm, synthesis_summary_norm] theorem ofColumns_constantSiteCount
    (columns : List RegionColumn) (rowCount constantSiteCount : ℕ) :
    (ofColumns columns rowCount constantSiteCount).constantSiteCount =
      constantSiteCount := rfl

@[circuit_norm, synthesis_summary_norm] theorem ofColumns_instanceRowExtent
    (columns : List RegionColumn) (rowCount constantSiteCount instanceRowExtent : ℕ) :
    (ofColumns columns rowCount constantSiteCount instanceRowExtent).instanceRowExtent =
      instanceRowExtent := rfl

def combine (left right : RegionSynthesisSummary) : RegionSynthesisSummary where
  columns := unionColumns left.columns right.columns
  rowCount := max left.rowCount right.rowCount
  constantSiteCount := left.constantSiteCount + right.constantSiteCount
  instanceRowExtent := max left.instanceRowExtent right.instanceRowExtent

theorem combine_assoc (left middle right : RegionSynthesisSummary) :
    left.combine (middle.combine right) =
      (left.combine middle).combine right := by
  apply RegionSynthesisSummary.ext
  · exact (unionColumns_assoc _ _ _).symm
  · exact (Nat.max_assoc _ _ _).symm
  · exact (Nat.add_assoc _ _ _).symm
  · exact (Nat.max_assoc _ _ _).symm

@[circuit_norm, synthesis_summary_norm]
theorem combine_columns (left right : RegionSynthesisSummary) :
    (left.combine right).columns =
      unionColumns left.columns right.columns := rfl

@[circuit_norm, synthesis_summary_norm]
theorem combine_rowCount (left right : RegionSynthesisSummary) :
    (left.combine right).rowCount = max left.rowCount right.rowCount := rfl

@[circuit_norm, synthesis_summary_norm] theorem combine_constantSiteCount
    (left right : RegionSynthesisSummary) :
    (left.combine right).constantSiteCount =
      left.constantSiteCount + right.constantSiteCount := rfl

@[circuit_norm, synthesis_summary_norm] theorem combine_instanceRowExtent
    (left right : RegionSynthesisSummary) :
    (left.combine right).instanceRowExtent =
      max left.instanceRowExtent right.instanceRowExtent := rfl

/-- Combining two reduced column summaries keeps a single reduced column source and
combines only their numerical footprints. -/
@[circuit_norm, synthesis_summary_norm]
theorem ofColumns_combine_ofColumns
    (leftColumns rightColumns : List RegionColumn)
    (leftRows rightRows leftConstants rightConstants : ℕ) :
    (ofColumns leftColumns leftRows leftConstants).combine
        (ofColumns rightColumns rightRows rightConstants) =
      ofColumns (leftColumns ++ rightColumns)
        (max leftRows rightRows) (leftConstants + rightConstants) := by
  apply RegionSynthesisSummary.ext
  · exact unionColumns_merge_normalized _ _
  · rfl
  · rfl
  · rfl

/-- Combining a reduced summary whose columns are already covered by the left
summary changes only the numerical footprint. This keeps compositional summaries
compact when a later operation reuses an existing region footprint. -/
theorem ofColumns_combine_ofColumns_of_subset
    (leftColumns rightColumns : List RegionColumn)
    (leftRows rightRows leftConstants rightConstants : ℕ)
    (hsubset : ∀ column ∈ rightColumns, column ∈ leftColumns) :
    (ofColumns leftColumns leftRows leftConstants).combine
        (ofColumns rightColumns rightRows rightConstants) =
      ofColumns leftColumns (max leftRows rightRows)
        (leftConstants + rightConstants) := by
  rw [ofColumns_combine_ofColumns]
  apply RegionSynthesisSummary.ext
  · exact unionColumns_normalize_append_redundant
      leftColumns rightColumns hsubset
  · rfl
  · rfl
  · rfl

/-- Repeated source columns may be removed before constructing a reduced region
summary. -/
theorem ofColumns_append_redundant
    (left right : List RegionColumn) (rowCount constantSiteCount : ℕ)
    (hsubset : ∀ column ∈ right, column ∈ left) :
    ofColumns (left ++ right) rowCount constantSiteCount =
      ofColumns left rowCount constantSiteCount := by
  apply RegionSynthesisSummary.ext
  · exact unionColumns_normalize_append_redundant left right hsubset
  · rfl
  · rfl
  · rfl

/-- Deferred-constant requests of a reduced summary fold are the sum of the
component requests. -/
@[synthesis_summary_norm]
theorem foldr_combine_constantSiteCount
    (summaries : List RegionSynthesisSummary) :
    (summaries.foldr combine {}).constantSiteCount =
      (summaries.map (fun summary => summary.constantSiteCount)).sum := by
  induction summaries with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      simp only [List.foldr_cons, combine_constantSiteCount,
        List.map_cons, List.sum_cons, inductionHypothesis]

@[circuit_norm, synthesis_summary_norm] theorem combine_empty
    (summary : RegionSynthesisSummary) :
    summary.combine {} = summary := by
  cases summary
  simp [combine, unionColumns]

theorem empty_combine (summary : RegionSynthesisSummary)
    (hcolumns : summary.columns.Nodup) :
    ({} : RegionSynthesisSummary).combine summary = summary := by
  apply RegionSynthesisSummary.ext
  · exact unionColumns_empty_left _ hcolumns
  · simp [combine]
  · simp [combine]
  · simp [combine]

/-- An explicitly reduced summary is a left identity target as well as a right
identity source. -/
@[circuit_norm, synthesis_summary_norm]
theorem empty_combine_ofColumns (columns : List RegionColumn)
    (rowCount constantSiteCount : ℕ) :
    ({} : RegionSynthesisSummary).combine
        (ofColumns columns rowCount constantSiteCount) =
      ofColumns columns rowCount constantSiteCount :=
  empty_combine _ (unionColumns_nodup [] columns (by simp))

private theorem foldr_ofColumns_eq_repeatColumns_combine
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (accumulator : RegionSynthesisSummary) (haccumulator : accumulator.columns.Nodup) :
    (List.ofFn fun i : Fin count =>
      ofColumns columns (offset + stride * i.val + rowCount) constantSiteCount).foldr
        combine accumulator =
      (repeatColumns columns offset stride rowCount constantSiteCount count).combine
        accumulator := by
  induction count generalizing accumulator with
  | zero =>
      simpa [repeatColumns] using (empty_combine accumulator haccumulator).symm
  | succ count inductionHypothesis =>
      rw [List.ofFn_succ']
      simp only [List.concat_eq_append, List.foldr_append, List.foldr,
        Fin.val_castSucc]
      rw [inductionHypothesis]
      · cases count with
        | zero =>
            apply RegionSynthesisSummary.ext
            · simp only [repeatColumns, Nat.succ_ne_zero, if_false,
                combine_columns]
              exact unionColumns_empty_left _
                (unionColumns_nodup _ _
                  (unionColumns_nodup [] columns (by simp)))
            · simp [repeatColumns, combine, ofColumns]
            · simp [repeatColumns, combine, ofColumns]
            · simp [repeatColumns, combine, ofColumns]
        | succ count =>
            apply RegionSynthesisSummary.ext
            · simp only [repeatColumns, Nat.succ_ne_zero, if_false,
                combine_columns, ofColumns_columns, Nat.add_one_sub_one]
              rw [← unionColumns_assoc, unionColumns_self]
            · simp only [repeatColumns, Nat.succ_ne_zero, if_false,
                combine_rowCount, ofColumns_rowCount, Fin.val_last,
                Nat.add_one_sub_one]
              rw [Nat.max_eq_right]
              exact (Nat.add_le_add_right
                (Nat.add_le_add_left
                  (Nat.mul_le_mul_left stride (Nat.le_succ count)) offset) rowCount).trans
                    (Nat.le_max_left _ _)
            · simp only [repeatColumns, Nat.succ_ne_zero, if_false,
                combine_constantSiteCount, ofColumns_constantSiteCount,
                Nat.add_one_sub_one, Nat.succ_mul]
              omega
            · simp [repeatColumns, combine, ofColumns]
      · exact unionColumns_nodup _ _
          (unionColumns_nodup [] columns (by simp))

/-- Folding repeated identical region shapes reduces to a constant-size summary. -/
@[synthesis_summary_norm]
theorem foldr_ofColumns_eq_repeatColumns
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ) :
    (List.ofFn fun i : Fin count =>
      ofColumns columns (offset + stride * i.val + rowCount) constantSiteCount).foldr
        combine {} =
      repeatColumns columns offset stride rowCount constantSiteCount count := by
  rw [foldr_ofColumns_eq_repeatColumns_combine]
  · exact combine_empty _
  · simp

def ofOperation (operation : RegionOperation F) : RegionSynthesisSummary where
  columns := unionColumns [] (regionOperationShapeColumns operation)
  rowCount := regionOperationRowExtent operation
  constantSiteCount := regionOperationConstantSiteCount operation
  instanceRowExtent := regionOperationInstanceRowExtent operation

@[circuit_norm] theorem ofOperation_columns (operation : RegionOperation F) :
    (ofOperation operation).columns =
      unionColumns [] (regionOperationShapeColumns operation) := rfl

@[circuit_norm] theorem ofOperation_rowCount (operation : RegionOperation F) :
    (ofOperation operation).rowCount = regionOperationRowExtent operation := rfl

@[circuit_norm] theorem ofOperation_constantSiteCount
    (operation : RegionOperation F) :
    (ofOperation operation).constantSiteCount =
      regionOperationConstantSiteCount operation := rfl

@[circuit_norm] theorem ofOperation_instanceRowExtent
    (operation : RegionOperation F) :
    (ofOperation operation).instanceRowExtent =
      regionOperationInstanceRowExtent operation := rfl

end RegionSynthesisSummary

/-- The operation-independent portion of one V1 region measurement. Region indices
are supplied later by the enclosing layouter sequence. -/
@[ext] structure RegionShapeSummary where
  columns : List RegionColumn
  rowCount : ℕ
deriving Inhabited

/-- Forget deferred-constant metadata when publishing a region to the V1 planner. -/
def RegionSynthesisSummary.toRegionShapeSummary
    (summary : RegionSynthesisSummary) : RegionShapeSummary where
  columns := summary.columns
  rowCount := summary.rowCount

@[circuit_norm, synthesis_summary_norm]
theorem RegionSynthesisSummary.toRegionShapeSummary_columns
    (summary : RegionSynthesisSummary) :
    summary.toRegionShapeSummary.columns = summary.columns := rfl

@[circuit_norm, synthesis_summary_norm]
theorem RegionSynthesisSummary.toRegionShapeSummary_rowCount
    (summary : RegionSynthesisSummary) :
    summary.toRegionShapeSummary.rowCount = summary.rowCount := rfl

/-- Exact synthesis summary of a region-operation stream. -/
def regionSynthesisSummary : RegionOperations F → RegionSynthesisSummary
  | [] => {}
  | operation :: rest =>
      (RegionSynthesisSummary.ofOperation operation).combine
        (regionSynthesisSummary rest)

theorem regionSynthesisSummary_columns_nodup
    (operations : RegionOperations F) :
    (regionSynthesisSummary operations).columns.Nodup := by
  induction operations with
  | nil => simp [regionSynthesisSummary]
  | cons operation rest _ =>
      exact unionColumns_nodup _ _
        (unionColumns_nodup [] (regionOperationShapeColumns operation) (by simp))

@[circuit_norm] theorem regionSynthesisSummary_nil_columns :
    (regionSynthesisSummary ([] : RegionOperations F)).columns = [] := rfl

@[circuit_norm] theorem regionSynthesisSummary_nil_rowCount :
    (regionSynthesisSummary ([] : RegionOperations F)).rowCount = 0 := rfl

@[circuit_norm] theorem regionSynthesisSummary_nil_constantSiteCount :
    (regionSynthesisSummary ([] : RegionOperations F)).constantSiteCount = 0 := rfl

@[circuit_norm] theorem regionSynthesisSummary_nil_instanceRowExtent :
    (regionSynthesisSummary ([] : RegionOperations F)).instanceRowExtent = 0 := rfl

/-- The empty operation stream has the empty reduced summary. -/
@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_nil :
    regionSynthesisSummary ([] : RegionOperations F) = {} := rfl

theorem regionSynthesisSummary_cons_columns
    (operation : RegionOperation F) (rest : RegionOperations F) :
    (regionSynthesisSummary (operation :: rest)).columns =
      unionColumns (unionColumns [] (regionOperationShapeColumns operation))
        (regionSynthesisSummary rest).columns := rfl

/-- A measured region that touches a planner column occupies at least one row. -/
theorem regionSynthesisSummary_rowCount_pos_of_columns_nonempty
    (operations : RegionOperations F)
    (hcolumns : (regionSynthesisSummary operations).columns ≠ []) :
    0 < (regionSynthesisSummary operations).rowCount := by
  induction operations with
  | nil => exact False.elim (hcolumns rfl)
  | cons operation rest inductionHypothesis =>
      have hnonempty :
          (unionColumns [] (regionOperationShapeColumns operation) ≠ []) ∨
            (regionSynthesisSummary rest).columns ≠ [] := by
        by_contra hneither
        rw [not_or] at hneither
        push Not at hneither
        apply hcolumns
        rw [regionSynthesisSummary_cons_columns,
          hneither.1, hneither.2]
        rfl
      rw [regionSynthesisSummary,
        RegionSynthesisSummary.combine_rowCount]
      rcases hnonempty with hoperation | hrest
      · have hextent : 0 < regionOperationRowExtent operation := by
          cases operation <;>
            simp_all [regionOperationShapeColumns, unionColumns,
              addColumn, regionOperationRowExtent]
        exact hextent.trans_le (Nat.le_max_left _ _)
      · exact (inductionHypothesis hrest).trans_le
          (Nat.le_max_right _ _)

theorem regionSynthesisSummary_columns_eq_unionColumns
    (operations : RegionOperations F) :
    (regionSynthesisSummary operations).columns =
      unionColumns [] (operations.flatMap regionOperationShapeColumns) := by
  induction operations with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      simp only [regionSynthesisSummary_cons_columns, List.flatMap_cons,
        inductionHypothesis, unionColumns_normalize_right]
      unfold unionColumns
      rw [List.foldl_append]

theorem regionSynthesisSummary_cons_rowCount
    (operation : RegionOperation F) (rest : RegionOperations F) :
    (regionSynthesisSummary (operation :: rest)).rowCount =
      max (regionOperationRowExtent operation)
        (regionSynthesisSummary rest).rowCount := rfl

theorem regionSynthesisSummary_cons_constantSiteCount
    (operation : RegionOperation F) (rest : RegionOperations F) :
    (regionSynthesisSummary (operation :: rest)).constantSiteCount =
      regionOperationConstantSiteCount operation +
        (regionSynthesisSummary rest).constantSiteCount := rfl

theorem regionSynthesisSummary_cons_instanceRowExtent
    (operation : RegionOperation F) (rest : RegionOperations F) :
    (regionSynthesisSummary (operation :: rest)).instanceRowExtent =
      max (regionOperationInstanceRowExtent operation)
        (regionSynthesisSummary rest).instanceRowExtent := rfl

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_constrainEqual_cons_columns
    (left right : Cell) (rest : RegionOperations F) :
    (regionSynthesisSummary (.constrainEqual left right :: rest)).columns =
      (regionSynthesisSummary rest).columns := by
  rw [regionSynthesisSummary_cons_columns]
  simp only [regionOperationShapeColumns, unionColumns_nil_right]
  exact unionColumns_empty_left _ (regionSynthesisSummary_columns_nodup rest)

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_constrainEqual_cons_rowCount
    (left right : Cell) (rest : RegionOperations F) :
    (regionSynthesisSummary (.constrainEqual left right :: rest)).rowCount =
      (regionSynthesisSummary rest).rowCount := by
  simp only [regionSynthesisSummary_cons_rowCount, regionOperationRowExtent,
    Nat.zero_max]

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_constrainEqual_cons_constantSiteCount
    (left right : Cell) (rest : RegionOperations F) :
    (regionSynthesisSummary
      (.constrainEqual left right :: rest)).constantSiteCount =
        (regionSynthesisSummary rest).constantSiteCount := by
  simp only [regionSynthesisSummary_cons_constantSiteCount,
    regionOperationConstantSiteCount, Nat.zero_add]

/-- Copy constraints do not occupy rows, columns, or deferred constant sites. -/
@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_constrainEqual_cons
    (left right : Cell) (rest : RegionOperations F) :
    regionSynthesisSummary (.constrainEqual left right :: rest) =
      regionSynthesisSummary rest := by
  apply RegionSynthesisSummary.ext
  · exact regionSynthesisSummary_constrainEqual_cons_columns left right rest
  · exact regionSynthesisSummary_constrainEqual_cons_rowCount left right rest
  · exact regionSynthesisSummary_constrainEqual_cons_constantSiteCount left right rest
  · simp [regionSynthesisSummary_cons_instanceRowExtent,
      regionOperationInstanceRowExtent]

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_constrainConstant_cons_columns
    (cell : Cell) (constant : F) (rest : RegionOperations F) :
    (regionSynthesisSummary (.constrainConstant cell constant :: rest)).columns =
      (regionSynthesisSummary rest).columns := by
  rw [regionSynthesisSummary_cons_columns]
  simp only [regionOperationShapeColumns, unionColumns_nil_right]
  exact unionColumns_empty_left _ (regionSynthesisSummary_columns_nodup rest)

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_constrainConstant_cons_rowCount
    (cell : Cell) (constant : F) (rest : RegionOperations F) :
    (regionSynthesisSummary (.constrainConstant cell constant :: rest)).rowCount =
      (regionSynthesisSummary rest).rowCount := by
  simp only [regionSynthesisSummary_cons_rowCount, regionOperationRowExtent,
    Nat.zero_max]

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_constrainInstance_cons_columns
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : RegionOperations F) :
    (regionSynthesisSummary
      (.constrainInstance cell column row :: rest)).columns =
        (regionSynthesisSummary rest).columns := by
  rw [regionSynthesisSummary_cons_columns]
  simp only [regionOperationShapeColumns, unionColumns_nil_right]
  exact unionColumns_empty_left _ (regionSynthesisSummary_columns_nodup rest)

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_constrainInstance_cons_rowCount
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : RegionOperations F) :
    (regionSynthesisSummary
      (.constrainInstance cell column row :: rest)).rowCount =
        (regionSynthesisSummary rest).rowCount := by
  simp only [regionSynthesisSummary_cons_rowCount, regionOperationRowExtent,
    Nat.zero_max]

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_assignAdvice_cons_columns
    (column : Column .advice) (row : ℕ) (value : WitgenIR F 1)
    (rest : RegionOperations F) :
    (regionSynthesisSummary (.assignAdvice column row value :: rest)).columns =
      unionColumns (unionColumns [] [.column .advice column.index])
        (regionSynthesisSummary rest).columns := by
  rw [regionSynthesisSummary_cons_columns]
  rfl

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_assignAdvice_cons_rowCount
    (column : Column .advice) (row : ℕ) (value : WitgenIR F 1)
    (rest : RegionOperations F) :
    (regionSynthesisSummary (.assignAdvice column row value :: rest)).rowCount =
      max (row + 1) (regionSynthesisSummary rest).rowCount := by
  rw [regionSynthesisSummary_cons_rowCount]
  rfl

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_assignAdvice_cons_constantSiteCount
    (column : Column .advice) (row : ℕ) (value : WitgenIR F 1)
    (rest : RegionOperations F) :
    (regionSynthesisSummary
      (.assignAdvice column row value :: rest)).constantSiteCount =
        (regionSynthesisSummary rest).constantSiteCount := by
  simp only [regionSynthesisSummary_cons_constantSiteCount,
    regionOperationConstantSiteCount, Nat.zero_add]

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_assignFixed_cons_columns
    (column : Column .fixed) (row : ℕ) (value : F)
    (rest : RegionOperations F) :
    (regionSynthesisSummary (.assignFixed column row value :: rest)).columns =
      unionColumns (unionColumns [] [.column .fixed column.index])
        (regionSynthesisSummary rest).columns := by
  rw [regionSynthesisSummary_cons_columns]
  rfl

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_assignFixed_cons_rowCount
    (column : Column .fixed) (row : ℕ) (value : F)
    (rest : RegionOperations F) :
    (regionSynthesisSummary (.assignFixed column row value :: rest)).rowCount =
      max (row + 1) (regionSynthesisSummary rest).rowCount := by
  rw [regionSynthesisSummary_cons_rowCount]
  rfl

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_assignFixed_cons_constantSiteCount
    (column : Column .fixed) (row : ℕ) (value : F)
    (rest : RegionOperations F) :
    (regionSynthesisSummary
      (.assignFixed column row value :: rest)).constantSiteCount =
        (regionSynthesisSummary rest).constantSiteCount := by
  simp only [regionSynthesisSummary_cons_constantSiteCount,
    regionOperationConstantSiteCount, Nat.zero_add]

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_enableGate_cons_columns
    (gate : Gate F) (row : ℕ) (rest : RegionOperations F) :
    (regionSynthesisSummary (.enableGate gate row :: rest)).columns =
      unionColumns (unionColumns [] [.selector gate.selector.index])
        (regionSynthesisSummary rest).columns := by
  rw [regionSynthesisSummary_cons_columns]
  rfl

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_enableGate_cons_rowCount
    (gate : Gate F) (row : ℕ) (rest : RegionOperations F) :
    (regionSynthesisSummary (.enableGate gate row :: rest)).rowCount =
      max (row + 1) (regionSynthesisSummary rest).rowCount := by
  rw [regionSynthesisSummary_cons_rowCount]
  rfl

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_enableGate_cons_constantSiteCount
    (gate : Gate F) (row : ℕ) (rest : RegionOperations F) :
    (regionSynthesisSummary
      (.enableGate gate row :: rest)).constantSiteCount =
        (regionSynthesisSummary rest).constantSiteCount := by
  simp only [regionSynthesisSummary_cons_constantSiteCount,
    regionOperationConstantSiteCount, Nat.zero_add]

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_enableLookup_cons_columns
    (lookup : LookupArgument F) (enabled : List Selector) (row : ℕ)
    (rest : RegionOperations F) :
    (regionSynthesisSummary (.enableLookup lookup enabled row :: rest)).columns =
      unionColumns (unionColumns [] (enabled.map fun selector =>
        .selector selector.index)) (regionSynthesisSummary rest).columns := by
  rw [regionSynthesisSummary_cons_columns]
  rfl

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_enableLookup_cons_rowCount
    (lookup : LookupArgument F) (enabled : List Selector) (row : ℕ)
    (rest : RegionOperations F) :
    (regionSynthesisSummary (.enableLookup lookup enabled row :: rest)).rowCount =
      max (row + 1) (regionSynthesisSummary rest).rowCount := by
  rw [regionSynthesisSummary_cons_rowCount]
  rfl

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_enableLookup_cons_constantSiteCount
    (lookup : LookupArgument F) (enabled : List Selector) (row : ℕ)
    (rest : RegionOperations F) :
    (regionSynthesisSummary
      (.enableLookup lookup enabled row :: rest)).constantSiteCount =
        (regionSynthesisSummary rest).constantSiteCount := by
  simp only [regionSynthesisSummary_cons_constantSiteCount,
    regionOperationConstantSiteCount, Nat.zero_add]

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_constrainConstant_cons_constantSiteCount
    (cell : Cell) (constant : F) (rest : RegionOperations F) :
    (regionSynthesisSummary
      (.constrainConstant cell constant :: rest)).constantSiteCount =
        1 + (regionSynthesisSummary rest).constantSiteCount := by
  rw [regionSynthesisSummary_cons_constantSiteCount]
  rfl

/-- A single advice assignment reduces to its concrete one-column summary. -/
@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_single_assignAdvice
    (column : Column .advice) (row : ℕ) (value : WitgenIR F 1) :
    regionSynthesisSummary [.assignAdvice column row value] =
      RegionSynthesisSummary.ofColumns
        [.column .advice column.index] (row + 1) 0 := by
  apply RegionSynthesisSummary.ext
  · simp only [regionSynthesisSummary_assignAdvice_cons_columns,
      regionSynthesisSummary_nil_columns, RegionSynthesisSummary.ofColumns_columns,
      unionColumns_nil_right]
  · simp only [regionSynthesisSummary_assignAdvice_cons_rowCount,
      regionSynthesisSummary_nil_rowCount, RegionSynthesisSummary.ofColumns_rowCount,
      Nat.max_zero]
  · simp only [regionSynthesisSummary_assignAdvice_cons_constantSiteCount,
      regionSynthesisSummary_nil_constantSiteCount,
      RegionSynthesisSummary.ofColumns_constantSiteCount]
  · exact regionSynthesisSummary_nil_instanceRowExtent (F := F)

/-- A single fixed assignment reduces to its concrete one-column summary. -/
@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_single_assignFixed
    (column : Column .fixed) (row : ℕ) (value : F) :
    regionSynthesisSummary [.assignFixed column row value] =
      RegionSynthesisSummary.ofColumns
        [.column .fixed column.index] (row + 1) 0 := by
  apply RegionSynthesisSummary.ext
  · simp only [regionSynthesisSummary_assignFixed_cons_columns,
      regionSynthesisSummary_nil_columns, RegionSynthesisSummary.ofColumns_columns,
      unionColumns_nil_right]
  · simp only [regionSynthesisSummary_assignFixed_cons_rowCount,
      regionSynthesisSummary_nil_rowCount, RegionSynthesisSummary.ofColumns_rowCount,
      Nat.max_zero]
  · simp only [regionSynthesisSummary_assignFixed_cons_constantSiteCount,
      regionSynthesisSummary_nil_constantSiteCount,
      RegionSynthesisSummary.ofColumns_constantSiteCount]
  · exact regionSynthesisSummary_nil_instanceRowExtent (F := F)

/-- A single gate enable reduces to its selector-column summary. -/
@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_single_enableGate
    (gate : Gate F) (row : ℕ) :
    regionSynthesisSummary [.enableGate gate row] =
      RegionSynthesisSummary.ofColumns
        [.selector gate.selector.index] (row + 1) 0 := by
  apply RegionSynthesisSummary.ext
  · simp only [regionSynthesisSummary_enableGate_cons_columns,
      regionSynthesisSummary_nil_columns,
      RegionSynthesisSummary.ofColumns_columns, unionColumns_nil_right]
  · simp only [regionSynthesisSummary_enableGate_cons_rowCount,
      regionSynthesisSummary_nil_rowCount,
      RegionSynthesisSummary.ofColumns_rowCount, Nat.max_zero]
  · simp only [regionSynthesisSummary_enableGate_cons_constantSiteCount,
      regionSynthesisSummary_nil_constantSiteCount,
      RegionSynthesisSummary.ofColumns_constantSiteCount]
  · exact regionSynthesisSummary_nil_instanceRowExtent (F := F)

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_constrainInstance_cons_constantSiteCount
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : RegionOperations F) :
    (regionSynthesisSummary
      (.constrainInstance cell column row :: rest)).constantSiteCount =
        (regionSynthesisSummary rest).constantSiteCount := by
  simp only [regionSynthesisSummary_cons_constantSiteCount,
    regionOperationConstantSiteCount, Nat.zero_add]

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
        RegionSynthesisSummary.ofOperation]
      apply (mem_unionColumns_iff _ _ _).2
      rcases hoperation with rfl | hrest
      · exact .inl ((mem_unionColumns_iff _ _ _).2 (.inr hcolumn))
      · exact .inr (inductionHypothesis hrest)

/-- A region program which never requests a deferred constant cell has zero
constant-allocation demand. -/
theorem regionSynthesisSummary_constantSiteCount_eq_zero_of_forall
    (operations : RegionOperations F)
    (hoperations : operations.Forall fun operation =>
      regionOperationConstantSiteCount operation = 0) :
    (regionSynthesisSummary operations).constantSiteCount = 0 := by
  induction operations with
  | nil =>
      rw [regionSynthesisSummary_nil_constantSiteCount]
  | cons operation rest inductionHypothesis =>
      rw [regionSynthesisSummary_cons_constantSiteCount]
      simp only [List.forall_cons] at hoperations
      rw [hoperations.1, inductionHypothesis hoperations.2, Nat.zero_add]

/-- Zero deferred-constant demand means that every operation in the region avoids
requesting one. This is the converse used to compose exact summaries through loops. -/
theorem forall_regionOperationConstantSiteCount_eq_zero_of_regionSynthesisSummary
    (operations : RegionOperations F)
    (hsummary : (regionSynthesisSummary operations).constantSiteCount = 0) :
    operations.Forall fun operation =>
      regionOperationConstantSiteCount operation = 0 := by
  induction operations with
  | nil => simp only [List.Forall]
  | cons operation rest inductionHypothesis =>
      rw [regionSynthesisSummary_cons_constantSiteCount] at hsummary
      obtain ⟨hoperation, hrest⟩ := Nat.add_eq_zero_iff.mp hsummary
      rw [List.forall_cons]
      exact ⟨hoperation, inductionHypothesis hrest⟩

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

namespace SynthesisSummary

def combine (left right : SynthesisSummary) : SynthesisSummary where
  columns := unionColumns left.columns right.columns
  columnOccupancy := fun column =>
    left.columnOccupancy column + right.columnOccupancy column
  constantSiteCount := left.constantSiteCount + right.constantSiteCount
  regionShapes := left.regionShapes ++ right.regionShapes
  tableRowExtent := max left.tableRowExtent right.tableRowExtent
  instanceRowExtent := max left.instanceRowExtent right.instanceRowExtent

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

/-- Fully reduced summary of `count` identical layouter fragments. -/
def replicate (count : ℕ) (summary : SynthesisSummary) : SynthesisSummary where
  columns := if count = 0 then [] else summary.columns
  columnOccupancy := fun column => count * summary.columnOccupancy column
  constantSiteCount := count * summary.constantSiteCount
  regionShapes := (List.replicate count summary.regionShapes).flatten
  tableRowExtent := if count = 0 then 0 else summary.tableRowExtent
  instanceRowExtent := if count = 0 then 0 else summary.instanceRowExtent

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
theorem replicate_regionShapes (count : ℕ) (summary : SynthesisSummary) :
    (replicate count summary).regionShapes =
      (List.replicate count summary.regionShapes).flatten := rfl

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

@[circuit_norm, synthesis_summary_norm] theorem combine_regionShapes
    (left right : SynthesisSummary) :
    (left.combine right).regionShapes =
      left.regionShapes ++ right.regionShapes := rfl

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

def ofRegion (summary : RegionSynthesisSummary) : SynthesisSummary where
  columns := summary.columns
  columnOccupancy := fun column =>
    if column ∈ summary.columns then summary.rowCount else 0
  constantSiteCount := summary.constantSiteCount
  regionShapes := [summary.toRegionShapeSummary]
  tableRowExtent := 0
  instanceRowExtent := summary.instanceRowExtent

/-- Reduced summary of one absolute instance-row reference. -/
def ofInstanceRow (row : ℕ) : SynthesisSummary where
  instanceRowExtent := row + 1

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
  | cons operation rest inductionHypothesis =>
      simp only [List.cons_append, regionSynthesisSummary,
        inductionHypothesis]
      apply RegionSynthesisSummary.ext
      · simp [RegionSynthesisSummary.combine, unionColumns_assoc]
      · simp [RegionSynthesisSummary.combine, Nat.max_assoc]
      · simp [RegionSynthesisSummary.combine, Nat.add_assoc]
      · simp [RegionSynthesisSummary.combine, Nat.max_assoc]

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
  RegionSynthesisSummary.combine_columns
  RegionSynthesisSummary.combine_rowCount
  RegionSynthesisSummary.combine_constantSiteCount
  RegionSynthesisSummary.ofOperation_columns
  RegionSynthesisSummary.ofOperation_rowCount
  RegionSynthesisSummary.ofOperation_constantSiteCount
  regionSynthesisSummary_nil_columns
  regionSynthesisSummary_nil_rowCount
  regionSynthesisSummary_nil_constantSiteCount
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
  /-- Concrete caller-owned cells that synthesis may use in copy constraints. -/
  inputCells : ∀ configInput, configLawful configInput →
      InputVar → List Cell := fun _ _ _ => []

/-- Equality-enabled columns required by the concrete cells passed to synthesis. -/
def KeygenRequirements.inputPermutationColumns
    {ConfigInput InputVar : Type}
    (self : KeygenRequirements F ConfigInput InputVar)
    (configInput : ConfigInput) (configLawful : self.configLawful configInput)
    (input : InputVar) : List AnyColumn :=
  (self.inputCells configInput configLawful input).map Cell.column

/-- A configure input has no keygen requirements left for an enclosing circuit. -/
structure KeygenRequirements.EmptyAt
    {ConfigInput InputVar : Type}
    (self : KeygenRequirements F ConfigInput InputVar)
    (input : ConfigInput) where
  configLawful : self.configLawful input
  gates_eq : self.gates input configLawful = []
  lookups_eq : self.lookups input configLawful = []
  permutationColumns_eq : self.permutationColumns input configLawful = []
  inputCells_eq : ∀ inputVar,
    self.inputCells input configLawful inputVar = []

/-! ## Copy-cell provenance -/

/-- Cells created by assignments in one concrete region. -/
def RegionOperation.assignedCells (region : RegionIndex) : RegionOperation F → List Cell
  | .assignAdvice column row _ => [.of region row column]
  | .assignFixed column row _ => [.of region row column]
  | _ => []

/-- Cells referenced as regional endpoints of copy constraints. -/
def RegionOperation.copiedCells : RegionOperation F → List Cell
  | .constrainEqual left right => [left, right]
  | .constrainConstant cell _ => [cell]
  | .constrainInstance cell _ _ => [cell]
  | _ => []

def RegionOperations.assignedCells (operations : RegionOperations F)
    (region : RegionIndex) : List Cell :=
  operations.flatMap (RegionOperation.assignedCells region)

def RegionOperations.copiedCells (operations : RegionOperations F) : List Cell :=
  operations.flatMap RegionOperation.copiedCells

def RegionOperations.CopyCellsAssigned (operations : RegionOperations F)
    (region : RegionIndex) (inputCells : List Cell) : Prop :=
  ∀ cell ∈ operations.copiedCells,
    cell ∈ inputCells ++ operations.assignedCells region

/-- Cells assigned by a layouter stream, with the same region-index walk used by V1. -/
def Operations.assignedCellsFrom : Operations F → RegionIndex → List Cell
  | [], _ => []
  | .region _ body :: rest, region =>
      body.assignedCells region ++ assignedCellsFrom rest (region + 1)
  | .constrainInstance _ _ _ :: rest, region => assignedCellsFrom rest region
  | .loadTable _ _ :: rest, region => assignedCellsFrom rest region

def Operations.assignedCells (operations : Operations F) : List Cell :=
  operations.assignedCellsFrom 0

/-- Cells referenced by one copy-like layouter operation. -/
def Operation.copiedCells : Operation F → List Cell
  | .region _ body => body.copiedCells
  | .constrainInstance cell _ _ => [cell]
  | .loadTable _ _ => []

/-- Cells referenced by every copy-like operation in a layouter stream. -/
def Operations.copiedCells (operations : Operations F) : List Cell :=
  operations.flatMap Operation.copiedCells

/-- Every copied regional cell was either supplied by the caller or created by an
assignment in this synthesis stream. -/
def Operations.CopyCellsAssigned (operations : Operations F)
    (initialRegion : RegionIndex) (inputCells : List Cell) : Prop :=
  ∀ cell ∈ operations.copiedCells,
    cell ∈ inputCells ++ operations.assignedCellsFrom initialRegion

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

/-- Membership in an enabled-selector list, by the index used by semantics. -/
@[circuit_norm]
def SelectorEnabledAtIndex
    (enabled : List Selector) (selector : ℕ) : Prop :=
  ∃ candidate ∈ enabled, candidate.index = selector

theorem selectorEnabledAtIndex_cons_self
    (selector : Selector) (rest : List Selector) :
    SelectorEnabledAtIndex (selector :: rest) selector.index :=
  ⟨selector, by simp, rfl⟩

theorem complexSelectorEnabledAtIndex_cons_self
    (selector : ComplexSelector) (rest : List Selector) :
    SelectorEnabledAtIndex ((selector : Selector) :: rest) selector.index :=
  ⟨selector, by simp, by simp⟩

/-- An operation activates selector `selector` at region-local `row`. -/
@[circuit_norm]
def RegionOperation.ActivatesSelectorAt
    (selector row : ℕ) : RegionOperation F → Prop
  | .enableGate gate operationRow =>
      gate.selector.index = selector ∧ operationRow = row
  | .enableLookup _ enabled operationRow =>
      SelectorEnabledAtIndex enabled selector ∧ operationRow = row
  | _ => False

/-- A lookup activation enables its mandatory master selector and no selector outside
the lookup's declared selector set. This property is local to the operation and is
therefore stable under circuit composition. -/
@[circuit_norm]
def RegionOperation.LookupActivationWellFormed : RegionOperation F → Prop
  | .enableLookup argument enabled _ =>
      SelectorEnabledAtIndex enabled argument.masterSelector.index ∧
        enabled.Forall fun selector =>
          selector.index = argument.masterSelector.index ∨
            selector.index ∈ argument.auxiliarySelectorIndices
  | _ => True

/-- Region-list lift of lookup-local activation well-formedness. -/
@[circuit_norm]
def RegionOperations.LookupActivationsWellFormed
    (operations : RegionOperations F) : Prop :=
  operations.Forall RegionOperation.LookupActivationWellFormed

/-- Layouter operation lift of lookup-local activation well-formedness. -/
@[circuit_norm]
def Operation.LookupActivationsWellFormed : Operation F → Prop
  | .region _ body => body.LookupActivationsWellFormed
  | _ => True

/-- Every lookup activation in every synthesized region is locally well-formed. -/
@[circuit_norm]
def Operations.LookupActivationsWellFormed
    (operations : Operations F) : Prop :=
  operations.Forall Operation.LookupActivationsWellFormed

/-- A gate never activates a selector used as an auxiliary by a configured lookup. -/
@[circuit_norm]
def Gate.AvoidsLookupAuxiliarySelectors
    (gate : Gate F) (lookups : List (LookupArgument F)) : Prop :=
  lookups.Forall fun lookup =>
    lookup.auxiliarySelectorIndices.Forall fun selector =>
      selector ≠ gate.selector.index

/-- A selector activation respects every configured lookup's master-selector
discipline. Gate selectors may not be auxiliary lookup selectors. A lookup activation
which turns on an auxiliary selector must turn on that lookup's master in the same
operation. `List.Forall` makes concrete configure output reduce compositionally. -/
@[circuit_norm]
def RegionOperation.LookupSelectorsLawful
    (lookups : List (LookupArgument F)) : RegionOperation F → Prop
  | .enableGate gate _ =>
      gate.AvoidsLookupAuxiliarySelectors lookups
  | .enableLookup _ enabled _ =>
      lookups.Forall fun lookup =>
        lookup.auxiliarySelectorIndices.Forall fun selector =>
          SelectorEnabledAtIndex enabled selector →
            SelectorEnabledAtIndex enabled lookup.masterSelector.index
  | _ => True

/-- Region-operation-list lift of `RegionOperation.LookupSelectorsLawful`. -/
@[circuit_norm]
def RegionOperations.LookupSelectorsLawful
    (lookups : List (LookupArgument F)) (operations : RegionOperations F) : Prop :=
  operations.Forall (RegionOperation.LookupSelectorsLawful lookups)

/-- Layouter operation lift of lookup-selector lawfulness. -/
@[circuit_norm]
def Operation.LookupSelectorsLawful
    (lookups : List (LookupArgument F)) : Operation F → Prop
  | .region _ body => body.LookupSelectorsLawful lookups
  | _ => True

/-- Every selector activation in every synthesized region follows the configured
lookup master-selector discipline. -/
@[circuit_norm]
def Operations.LookupSelectorsLawful
    (lookups : List (LookupArgument F)) (operations : Operations F) : Prop :=
  operations.Forall (Operation.LookupSelectorsLawful lookups)

/-- The standard lookup-enabling constructor satisfies its own master-selector
obligation independently of which auxiliary selectors are selected. -/
theorem LookupArgument.lookupSelectorsLawful_enable_self
    (argument : LookupArgument F) (auxiliarySelectors : List Selector) (row : ℕ) :
    RegionOperation.LookupSelectorsLawful [argument]
      (.enableLookup argument
        (argument.masterSelector :: auxiliarySelectors) row) := by
  rw [RegionOperation.LookupSelectorsLawful, List.forall_cons]
  constructor
  · rw [List.forall_iff_forall_mem]
    intro _ _ _
    exact ⟨argument.masterSelector, by simp, rfl⟩
  · trivial

/-- The standard lookup constructor is locally well-formed whenever its explicitly
enabled auxiliary selectors belong to the lookup expression. -/
theorem LookupArgument.lookupActivationWellFormed_enable
    (argument : LookupArgument F) (auxiliarySelectors : List Selector) (row : ℕ)
    (hauxiliary : auxiliarySelectors.Forall fun selector =>
      selector.index ∈ argument.selectorIndices) :
    RegionOperation.LookupActivationWellFormed
      (.enableLookup argument
        (argument.masterSelector :: auxiliarySelectors) row) := by
  constructor
  · exact selectorEnabledAtIndex_cons_self _ _
  · rw [List.forall_cons]
    constructor
    · exact Or.inl rfl
    · exact hauxiliary.imp fun _ hselector => by
        simpa only [LookupArgument.selectorIndices, List.mem_cons] using hselector

/-- Registration, lookup-local activation well-formedness, and configure-time selector
compatibility imply the global master-selector discipline for one operation. -/
theorem RegionOperation.lookupSelectorsLawful_of_registered
    {operation : RegionOperation F}
    {gates : List (Gate F)} {lookups : List (LookupArgument F)}
    {permutationColumns : List AnyColumn}
    (hregistered : operation.KeygenRegistered
      gates lookups permutationColumns)
    (hactivation : operation.LookupActivationWellFormed)
    (hcompatible : Halo2.LookupSelectorsCompatible gates lookups) :
    operation.LookupSelectorsLawful lookups := by
  cases operation with
  | enableGate gate row =>
      exact List.forall_iff_forall_mem.mpr fun argument hargument =>
        (List.forall_iff_forall_mem.mp
          (List.forall_iff_forall_mem.mp hcompatible.1 gate hregistered)
          argument hargument).1
  | enableLookup source enabled row =>
      rw [RegionOperation.LookupSelectorsLawful,
        List.forall_iff_forall_mem]
      intro target htarget
      rw [List.forall_iff_forall_mem]
      intro selector hselector henabled
      obtain ⟨candidate, hcandidate, hcandidateIndex⟩ := henabled
      have hsourceSelector : selector ∈ source.selectorIndices := by
        rw [← hcandidateIndex]
        simpa only [LookupArgument.selectorIndices, List.mem_cons] using
          (List.forall_iff_forall_mem.mp hactivation.2
            candidate hcandidate)
      have hpair := List.forall_iff_forall_mem.mp
        (List.forall_iff_forall_mem.mp hcompatible.2 source hregistered)
        target htarget
      have hmaster := List.forall_iff_forall_mem.mp hpair
        selector hsourceSelector hselector
      have hmaster' :
          target.masterSelector.index = source.masterSelector.index := by
        simpa [LookupArgument.selectorUsage] using hmaster
      rw [hmaster']
      exact hactivation.1
  | assignAdvice | assignFixed | constrainEqual | constrainConstant |
      constrainInstance =>
      trivial

theorem RegionOperations.lookupSelectorsLawful_of_registered
    {operations : RegionOperations F}
    {gates : List (Gate F)} {lookups : List (LookupArgument F)}
    {permutationColumns : List AnyColumn}
    (hregistered : operations.Forall
      (RegionOperation.KeygenRegistered gates lookups permutationColumns))
    (hactivations : operations.LookupActivationsWellFormed)
    (hcompatible : Halo2.LookupSelectorsCompatible gates lookups) :
    operations.LookupSelectorsLawful lookups := by
  rw [RegionOperations.LookupSelectorsLawful,
    List.forall_iff_forall_mem] at ⊢
  intro operation hoperation
  exact RegionOperation.lookupSelectorsLawful_of_registered
    (List.forall_iff_forall_mem.mp hregistered operation hoperation)
    (List.forall_iff_forall_mem.mp hactivations operation hoperation)
    hcompatible

theorem Operation.lookupSelectorsLawful_of_registered
    {operation : Operation F}
    {gates : List (Gate F)} {lookups : List (LookupArgument F)}
    {permutationColumns : List AnyColumn}
    (hregistered : operation.KeygenRegistered
      gates lookups permutationColumns)
    (hactivations : operation.LookupActivationsWellFormed)
    (hcompatible : Halo2.LookupSelectorsCompatible gates lookups) :
    operation.LookupSelectorsLawful lookups := by
  cases operation with
  | region name body =>
      exact RegionOperations.lookupSelectorsLawful_of_registered
        hregistered hactivations hcompatible
  | constrainInstance | loadTable =>
      trivial

theorem Operations.lookupSelectorsLawful_of_registered
    {operations : Operations F}
    {gates : List (Gate F)} {lookups : List (LookupArgument F)}
    {permutationColumns : List AnyColumn}
    (hregistered : operations.KeygenRegistered
      gates lookups permutationColumns)
    (hactivations : operations.LookupActivationsWellFormed)
    (hcompatible : Halo2.LookupSelectorsCompatible gates lookups) :
    operations.LookupSelectorsLawful lookups := by
  rw [Operations.LookupSelectorsLawful,
    List.forall_iff_forall_mem] at ⊢
  intro operation hoperation
  exact Operation.lookupSelectorsLawful_of_registered
    (List.forall_iff_forall_mem.mp hregistered operation hoperation)
    (List.forall_iff_forall_mem.mp hactivations operation hoperation)
    hcompatible

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
