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

attribute [synthesis_summary_norm] Nat.zero_max Nat.max_zero Nat.max_self

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

/-- Concrete columns in a region footprint. -/
def physicalColumns (columns : List RegionColumn) : List RegionColumn :=
  columns.filter fun
    | .column _ _ => true
    | .selector _ => false

/-- Virtual selector columns in a region footprint. -/
def selectorColumns (columns : List RegionColumn) : List RegionColumn :=
  columns.filter fun
    | .column _ _ => false
    | .selector _ => true

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

/-- The contribution of an operation to the number of activated lookup arguments. -/
@[circuit_norm] def regionOperationLookupActivationCount : RegionOperation F → ℕ
  | .enableLookup _ _ _ => 1
  | _ => 0

/-- The selector activations contributed by one region operation, retaining the
selector index and region-local row. -/
@[circuit_norm] def regionOperationSelectorActivations :
    RegionOperation F → List (ℕ × ℕ)
  | .enableGate gate row => [(gate.selector.index, row)]
  | .enableLookup _ enabled row =>
      enabled.map fun selector => (selector.index, row)
  | _ => []

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
  lookupActivationCount : ℕ := 0
  selectorActivations : List (ℕ × ℕ) := []

namespace RegionSynthesisSummary

/-- The reduced region footprint contains no fixed-column writes. -/
def HasNoFixedColumns (summary : RegionSynthesisSummary) : Prop :=
  ∀ index, .column .fixed index ∉ summary.columns

/-- A reduced region summary from its distinct-column source list and exact numerical
footprint. -/
def ofColumns (columns : List RegionColumn) (rowCount constantSiteCount : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    RegionSynthesisSummary where
  columns := unionColumns [] columns
  rowCount := rowCount
  constantSiteCount := constantSiteCount
  lookupActivationCount := lookupActivationCount
  instanceRowExtent := instanceRowExtent

/-- Attach the exact local selector activations to an otherwise reduced region
footprint. -/
def withSelectorActivations (summary : RegionSynthesisSummary)
    (activations : List (ℕ × ℕ)) : RegionSynthesisSummary :=
  { summary with selectorActivations := activations }

@[circuit_norm, synthesis_summary_norm]
theorem withSelectorActivations_columns
    (summary : RegionSynthesisSummary) (activations : List (ℕ × ℕ)) :
    (summary.withSelectorActivations activations).columns = summary.columns := rfl

@[circuit_norm, synthesis_summary_norm]
theorem withSelectorActivations_rowCount
    (summary : RegionSynthesisSummary) (activations : List (ℕ × ℕ)) :
    (summary.withSelectorActivations activations).rowCount = summary.rowCount := rfl

@[circuit_norm, synthesis_summary_norm]
theorem withSelectorActivations_constantSiteCount
    (summary : RegionSynthesisSummary) (activations : List (ℕ × ℕ)) :
    (summary.withSelectorActivations activations).constantSiteCount =
      summary.constantSiteCount := rfl

@[circuit_norm, synthesis_summary_norm]
theorem withSelectorActivations_instanceRowExtent
    (summary : RegionSynthesisSummary) (activations : List (ℕ × ℕ)) :
    (summary.withSelectorActivations activations).instanceRowExtent =
      summary.instanceRowExtent := rfl

@[circuit_norm, synthesis_summary_norm]
theorem withSelectorActivations_lookupActivationCount
    (summary : RegionSynthesisSummary) (activations : List (ℕ × ℕ)) :
    (summary.withSelectorActivations activations).lookupActivationCount =
      summary.lookupActivationCount := rfl

@[synthesis_summary_norm]
theorem hasNoFixedColumns_withSelectorActivations
    (summary : RegionSynthesisSummary) (activations : List (ℕ × ℕ)) :
    (summary.withSelectorActivations activations).HasNoFixedColumns ↔
      summary.HasNoFixedColumns := by
  rfl

@[circuit_norm, synthesis_summary_norm]
theorem empty_withSelectorActivations :
    ({} : RegionSynthesisSummary).withSelectorActivations [] = {} := rfl

@[circuit_norm, synthesis_summary_norm]
theorem withSelectorActivations_selectorActivations
    (summary : RegionSynthesisSummary) (activations : List (ℕ × ℕ)) :
    (summary.withSelectorActivations activations).selectorActivations =
      activations := rfl

@[synthesis_summary_norm]
theorem hasNoFixedColumns_ofColumns
    (columns : List RegionColumn) (rowCount constantSiteCount : ℕ)
    (instanceRowExtent : ℕ := 0) {lookupActivationCount : ℕ} :
    HasNoFixedColumns
        (ofColumns columns rowCount constantSiteCount instanceRowExtent
          lookupActivationCount) ↔
      ∀ index, .column .fixed index ∉ columns := by
  constructor
  · intro hsummary index hcolumn
    exact hsummary index
      ((mem_unionColumns_iff [] columns _).2 (.inr hcolumn))
  · intro hcolumns index hcolumn
    rcases (mem_unionColumns_iff [] columns _).1 hcolumn with hnil | hsource
    · exact (List.not_mem_nil hnil).elim
    · exact hcolumns index hsource

/-- The closed-form summary of `count` repetitions of the same column shape,
whose `i`th repetition occupies through
`offset + stride * i + rowCount` and requests `constantSiteCount` constants. -/
def repeatColumns (columns : List RegionColumn) (offset stride rowCount
    constantSiteCount count : ℕ) (instanceRowExtent : ℕ := 0)
    (lookupActivationCount : ℕ := 0) :
    RegionSynthesisSummary :=
  if count = 0 then {}
  else
    ofColumns columns
      (offset + stride * (count - 1) + rowCount)
      (count * constantSiteCount) instanceRowExtent
      (count * lookupActivationCount)

/-- Compact selector rows for repeated identical region fragments. -/
def repeatedSelectorActivations (selector offset stride : ℕ) :
    ℕ → List (ℕ × ℕ)
  | 0 => []
  | count + 1 =>
      repeatedSelectorActivations selector offset stride count ++
        [(selector, offset + stride * count)]

/-- Compact selector rows for a repeated fixed pattern. Each pair contains a selector
index and its row offset within one repetition. -/
def repeatedSelectorPattern (pattern : List (ℕ × ℕ)) (offset stride : ℕ) :
    ℕ → List (ℕ × ℕ)
  | 0 => []
  | count + 1 =>
      repeatedSelectorPattern pattern offset stride count ++
        pattern.map fun (selector, row) =>
          (selector, offset + stride * count + row)

/-- The compact exact summary of repeated footprints with a fixed selector pattern. -/
def repeatColumnsWithSelectorPattern (pattern : List (ℕ × ℕ))
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    RegionSynthesisSummary :=
  (repeatColumns columns offset stride rowCount constantSiteCount count
    instanceRowExtent lookupActivationCount).withSelectorActivations
      (repeatedSelectorPattern pattern offset stride count)

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelectorPattern_columns (pattern : List (ℕ × ℕ))
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorPattern pattern columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).columns =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).columns := rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelectorPattern_rowCount (pattern : List (ℕ × ℕ))
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorPattern pattern columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).rowCount =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).rowCount := rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelectorPattern_constantSiteCount (pattern : List (ℕ × ℕ))
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorPattern pattern columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).constantSiteCount =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).constantSiteCount := rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelectorPattern_instanceRowExtent (pattern : List (ℕ × ℕ))
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorPattern pattern columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).instanceRowExtent =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).instanceRowExtent := rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelectorPattern_lookupActivationCount (pattern : List (ℕ × ℕ))
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorPattern pattern columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).lookupActivationCount =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).lookupActivationCount := rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelectorPattern_selectorActivations
    (pattern : List (ℕ × ℕ)) (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorPattern pattern columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).selectorActivations =
      repeatedSelectorPattern pattern offset stride count := rfl

@[synthesis_summary_norm]
theorem hasNoFixedColumns_repeatColumnsWithSelectorPattern
    (pattern : List (ℕ × ℕ)) (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorPattern pattern columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).HasNoFixedColumns ↔
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).HasNoFixedColumns := by
  rfl

/-- The compact exact summary of repeated identical footprints which each activate
one selector at a possibly distinct row within the repeated footprint. -/
def repeatColumnsWithSelectorAt (selector selectorOffset : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    RegionSynthesisSummary :=
  (repeatColumns columns offset stride rowCount constantSiteCount count
    instanceRowExtent lookupActivationCount).withSelectorActivations
      (repeatedSelectorActivations selector selectorOffset stride count)

/-- The common case where each repetition activates its selector at its base row. -/
def repeatColumnsWithSelector (selector : ℕ) (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    RegionSynthesisSummary :=
  repeatColumnsWithSelectorAt selector offset columns offset stride rowCount
    constantSiteCount count instanceRowExtent lookupActivationCount

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelectorAt_columns (selector selectorOffset : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorAt selector selectorOffset columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).columns =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).columns := rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelectorAt_rowCount (selector selectorOffset : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorAt selector selectorOffset columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).rowCount =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).rowCount := rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelectorAt_constantSiteCount (selector selectorOffset : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorAt selector selectorOffset columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).constantSiteCount =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).constantSiteCount := rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelectorAt_instanceRowExtent (selector selectorOffset : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorAt selector selectorOffset columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).instanceRowExtent =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).instanceRowExtent := rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelectorAt_lookupActivationCount (selector selectorOffset : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorAt selector selectorOffset columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).lookupActivationCount =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).lookupActivationCount := rfl

@[synthesis_summary_norm]
theorem hasNoFixedColumns_repeatColumnsWithSelectorAt (selector selectorOffset : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorAt selector selectorOffset columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).HasNoFixedColumns ↔
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).HasNoFixedColumns := by
  rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelector_columns (selector : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelector selector columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).columns =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).columns := rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelector_rowCount (selector : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelector selector columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).rowCount =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).rowCount := rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelector_constantSiteCount (selector : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelector selector columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).constantSiteCount =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).constantSiteCount := rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelector_instanceRowExtent (selector : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelector selector columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).instanceRowExtent =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).instanceRowExtent := rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelector_lookupActivationCount (selector : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelector selector columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).lookupActivationCount =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).lookupActivationCount := rfl

@[synthesis_summary_norm]
theorem hasNoFixedColumns_repeatColumnsWithSelector (selector : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelector selector columns offset stride rowCount
      constantSiteCount count instanceRowExtent
      lookupActivationCount).HasNoFixedColumns ↔
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).HasNoFixedColumns := by
  rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumns_columns (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) {lookupActivationCount : ℕ} :
    (repeatColumns columns offset stride rowCount constantSiteCount count
      instanceRowExtent lookupActivationCount).columns =
      if count = 0 then [] else unionColumns [] columns := by
  cases count <;> rfl

@[synthesis_summary_norm]
theorem hasNoFixedColumns_repeatColumns
    (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) {lookupActivationCount : ℕ} :
    (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).HasNoFixedColumns ↔
      count = 0 ∨ ∀ index, .column .fixed index ∉ columns := by
  by_cases hcount : count = 0
  · subst count
    simp [repeatColumns, HasNoFixedColumns]
  · simp [repeatColumns, hcount, hasNoFixedColumns_ofColumns]

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumns_rowCount (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) {lookupActivationCount : ℕ} :
    (repeatColumns columns offset stride rowCount constantSiteCount count
      instanceRowExtent lookupActivationCount).rowCount =
      if count = 0 then 0 else offset + stride * (count - 1) + rowCount := by
  cases count <;> rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumns_constantSiteCount (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) {lookupActivationCount : ℕ} :
    (repeatColumns columns offset stride rowCount constantSiteCount count
      instanceRowExtent lookupActivationCount).constantSiteCount =
      count * constantSiteCount := by
  cases count <;> simp [repeatColumns, ofColumns]

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumns_instanceRowExtent (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) {lookupActivationCount : ℕ} :
    (repeatColumns columns offset stride rowCount constantSiteCount count
      instanceRowExtent lookupActivationCount).instanceRowExtent =
        if count = 0 then 0 else instanceRowExtent := by
  cases count <;> rfl

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumns_lookupActivationCount (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumns columns offset stride rowCount constantSiteCount count
      instanceRowExtent lookupActivationCount).lookupActivationCount =
        count * lookupActivationCount := by
  cases count <;> simp [repeatColumns, ofColumns]

@[circuit_norm, synthesis_summary_norm] theorem ofColumns_columns
    (columns : List RegionColumn) (rowCount constantSiteCount : ℕ)
    {instanceRowExtent lookupActivationCount : ℕ} :
    (ofColumns columns rowCount constantSiteCount instanceRowExtent
      lookupActivationCount).columns =
      unionColumns [] columns := rfl

theorem ofColumns_columns_nodup (columns : List RegionColumn)
    (rowCount constantSiteCount : ℕ) (instanceRowExtent : ℕ := 0)
    (lookupActivationCount : ℕ := 0) :
    (ofColumns columns rowCount constantSiteCount instanceRowExtent
      lookupActivationCount).columns.Nodup :=
  unionColumns_nodup [] columns (by simp)

theorem withSelectorActivations_ofColumns_columns_nodup
    (columns : List RegionColumn) (rowCount constantSiteCount : ℕ)
    (selectorActivations : List (ℕ × ℕ)) (instanceRowExtent : ℕ := 0)
    (lookupActivationCount : ℕ := 0) :
    ((ofColumns columns rowCount constantSiteCount instanceRowExtent
      lookupActivationCount).withSelectorActivations selectorActivations).columns.Nodup :=
  ofColumns_columns_nodup columns rowCount constantSiteCount
    instanceRowExtent lookupActivationCount

@[circuit_norm, synthesis_summary_norm] theorem ofColumns_rowCount
    (columns : List RegionColumn) (rowCount constantSiteCount : ℕ)
    {instanceRowExtent lookupActivationCount : ℕ} :
    (ofColumns columns rowCount constantSiteCount instanceRowExtent
      lookupActivationCount).rowCount = rowCount := rfl

@[circuit_norm, synthesis_summary_norm] theorem ofColumns_constantSiteCount
    (columns : List RegionColumn) (rowCount constantSiteCount : ℕ)
    {instanceRowExtent lookupActivationCount : ℕ} :
    (ofColumns columns rowCount constantSiteCount instanceRowExtent
      lookupActivationCount).constantSiteCount =
      constantSiteCount := rfl

@[circuit_norm, synthesis_summary_norm] theorem ofColumns_lookupActivationCount
    (columns : List RegionColumn) (rowCount constantSiteCount : ℕ)
    {instanceRowExtent lookupActivationCount : ℕ} :
    (ofColumns columns rowCount constantSiteCount
      instanceRowExtent lookupActivationCount).lookupActivationCount =
        lookupActivationCount := rfl

@[circuit_norm, synthesis_summary_norm] theorem ofColumns_instanceRowExtent
    (columns : List RegionColumn) (rowCount constantSiteCount : ℕ)
    {instanceRowExtent lookupActivationCount : ℕ} :
    (ofColumns columns rowCount constantSiteCount instanceRowExtent
      lookupActivationCount).instanceRowExtent =
      instanceRowExtent := rfl

@[circuit_norm, synthesis_summary_norm] theorem ofColumns_selectorActivations
    (columns : List RegionColumn) (rowCount constantSiteCount : ℕ)
    {instanceRowExtent lookupActivationCount : ℕ} :
    (ofColumns columns rowCount constantSiteCount instanceRowExtent
      lookupActivationCount).selectorActivations = [] := rfl

def combine (left right : RegionSynthesisSummary) : RegionSynthesisSummary where
  columns := unionColumns left.columns right.columns
  rowCount := max left.rowCount right.rowCount
  constantSiteCount := left.constantSiteCount + right.constantSiteCount
  lookupActivationCount := left.lookupActivationCount + right.lookupActivationCount
  instanceRowExtent := max left.instanceRowExtent right.instanceRowExtent
  selectorActivations := left.selectorActivations ++ right.selectorActivations

@[synthesis_summary_norm]
theorem hasNoFixedColumns_combine
    (left right : RegionSynthesisSummary) :
    (left.combine right).HasNoFixedColumns ↔
      left.HasNoFixedColumns ∧ right.HasNoFixedColumns := by
  simp only [HasNoFixedColumns, combine, mem_unionColumns_iff, not_or]
  aesop

theorem combine_assoc (left middle right : RegionSynthesisSummary) :
    left.combine (middle.combine right) =
      (left.combine middle).combine right := by
  apply RegionSynthesisSummary.ext
  · exact (unionColumns_assoc _ _ _).symm
  · exact (Nat.max_assoc _ _ _).symm
  · exact (Nat.add_assoc _ _ _).symm
  · exact (Nat.max_assoc _ _ _).symm
  · exact (Nat.add_assoc _ _ _).symm
  · exact (List.append_assoc _ _ _).symm

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

@[circuit_norm, synthesis_summary_norm] theorem combine_lookupActivationCount
    (left right : RegionSynthesisSummary) :
    (left.combine right).lookupActivationCount =
      left.lookupActivationCount + right.lookupActivationCount := rfl

@[circuit_norm, synthesis_summary_norm] theorem combine_instanceRowExtent
    (left right : RegionSynthesisSummary) :
    (left.combine right).instanceRowExtent =
      max left.instanceRowExtent right.instanceRowExtent := rfl

@[circuit_norm, synthesis_summary_norm] theorem combine_selectorActivations
    (left right : RegionSynthesisSummary) :
    (left.combine right).selectorActivations =
      left.selectorActivations ++ right.selectorActivations := rfl

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

/-- Lookup activations of a reduced summary fold are the sum of the component
counts. -/
@[synthesis_summary_norm]
theorem foldr_combine_lookupActivationCount
    (summaries : List RegionSynthesisSummary) :
    (summaries.foldr combine {}).lookupActivationCount =
      (summaries.map (fun summary => summary.lookupActivationCount)).sum := by
  induction summaries with
  | nil => rfl
  | cons summary rest inductionHypothesis =>
      simp only [List.foldr_cons, combine_lookupActivationCount,
        List.map_cons, List.sum_cons, inductionHypothesis]

/-- A fold of region summaries that never touch instance rows also never touches
instance rows. -/
@[synthesis_summary_norm]
theorem foldr_combine_instanceRowExtent_eq_zero
    (summaries : List RegionSynthesisSummary)
    (hzero : ∀ summary ∈ summaries, summary.instanceRowExtent = 0) :
    (summaries.foldr combine {}).instanceRowExtent = 0 := by
  induction summaries with
  | nil => simp only [List.foldr_nil]
  | cons summary rest inductionHypothesis =>
      simp only [List.foldr_cons, combine_instanceRowExtent]
      rw [hzero summary (List.mem_cons_self),
        inductionHypothesis (fun child hchild =>
          hzero child (List.mem_cons_of_mem summary hchild))]
      simp only [max_self]

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

@[circuit_norm, synthesis_summary_norm]
theorem empty_combine_withSelectorActivations_ofColumns
    (columns : List RegionColumn) (rowCount constantSiteCount : ℕ)
    (selectorActivations : List (ℕ × ℕ)) :
    ({} : RegionSynthesisSummary).combine
        ((ofColumns columns rowCount constantSiteCount).withSelectorActivations
          selectorActivations) =
      (ofColumns columns rowCount constantSiteCount).withSelectorActivations
        selectorActivations :=
  empty_combine _ (unionColumns_nodup [] columns (by simp))

private theorem foldr_ofColumns_eq_repeatColumns_combine
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent lookupActivationCount : ℕ)
    (accumulator : RegionSynthesisSummary) (haccumulator : accumulator.columns.Nodup) :
    (List.ofFn fun i : Fin count =>
      ofColumns columns (offset + stride * i.val + rowCount) constantSiteCount
        instanceRowExtent lookupActivationCount).foldr
        combine accumulator =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).combine
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
            · simp [repeatColumns, combine, ofColumns, Nat.add_mul,
                Nat.add_assoc]
              omega
            · simp [repeatColumns, combine, ofColumns]
      · exact unionColumns_nodup _ _
          (unionColumns_nodup [] columns (by simp))

/-- Folding repeated identical region shapes reduces to a constant-size summary. -/
@[synthesis_summary_norm]
theorem foldr_ofColumns_eq_repeatColumns
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (List.ofFn fun i : Fin count =>
      ofColumns columns (offset + stride * i.val + rowCount) constantSiteCount
        instanceRowExtent lookupActivationCount).foldr
        combine {} =
      repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount := by
  rw [foldr_ofColumns_eq_repeatColumns_combine]
  · exact combine_empty _
  · simp

private theorem foldr_ofColumnsWithSelector_eq_repeatColumnsWithSelector_combine
    (selector selectorOffset : ℕ) (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent lookupActivationCount : ℕ)
    (accumulator : RegionSynthesisSummary)
    (haccumulator : accumulator.columns.Nodup) :
    (List.ofFn fun i : Fin count =>
      (ofColumns columns (offset + stride * i.val + rowCount)
        constantSiteCount instanceRowExtent
        lookupActivationCount).withSelectorActivations
          [(selector, selectorOffset + stride * i.val)]).foldr combine accumulator =
      (repeatColumnsWithSelectorAt selector selectorOffset columns offset stride rowCount
        constantSiteCount count instanceRowExtent lookupActivationCount).combine
        accumulator := by
  induction count generalizing accumulator with
  | zero =>
      simpa [repeatColumnsWithSelectorAt, repeatColumns,
        withSelectorActivations, repeatedSelectorActivations] using
        (empty_combine accumulator haccumulator).symm
  | succ count inductionHypothesis =>
      rw [List.ofFn_succ']
      simp only [List.concat_eq_append, List.foldr_append, List.foldr,
        Fin.val_castSucc]
      rw [inductionHypothesis]
      · cases count with
        | zero =>
            apply RegionSynthesisSummary.ext
            · simp only [repeatColumnsWithSelectorAt, repeatColumns,
                Nat.succ_ne_zero, if_false, combine_columns,
                withSelectorActivations_columns]
              exact unionColumns_empty_left _
                (unionColumns_nodup _ _
                  (unionColumns_nodup [] columns (by simp)))
            · simp [repeatColumnsWithSelectorAt, repeatColumns, combine, ofColumns,
                withSelectorActivations, repeatedSelectorActivations]
            · simp [repeatColumnsWithSelectorAt, repeatColumns, combine, ofColumns,
                withSelectorActivations, repeatedSelectorActivations]
            · simp [repeatColumnsWithSelectorAt, repeatColumns, combine, ofColumns,
                withSelectorActivations, repeatedSelectorActivations]
            · simp [repeatColumnsWithSelectorAt, repeatColumns, combine, ofColumns,
                withSelectorActivations, repeatedSelectorActivations]
            · simp [repeatColumnsWithSelectorAt, repeatColumns, combine, ofColumns,
                withSelectorActivations, repeatedSelectorActivations]
        | succ count =>
            apply RegionSynthesisSummary.ext
            · simp only [repeatColumnsWithSelectorAt, repeatColumns,
                Nat.succ_ne_zero, if_false, combine_columns,
                withSelectorActivations_columns, ofColumns_columns,
                Nat.add_one_sub_one]
              rw [← unionColumns_assoc, unionColumns_self]
            · simp only [repeatColumnsWithSelectorAt, repeatColumns,
                Nat.succ_ne_zero, if_false, combine_rowCount,
                withSelectorActivations_rowCount, ofColumns_rowCount,
                Fin.val_last, Nat.add_one_sub_one]
              rw [Nat.max_eq_right]
              exact (Nat.add_le_add_right
                (Nat.add_le_add_left
                  (Nat.mul_le_mul_left stride (Nat.le_succ count)) offset)
                  rowCount).trans (Nat.le_max_left _ _)
            · simp [repeatColumnsWithSelectorAt, repeatColumns, combine, ofColumns,
                withSelectorActivations,
                Nat.add_mul]
              omega
            · simp [repeatColumnsWithSelectorAt, repeatColumns, combine, ofColumns,
                withSelectorActivations]
            · simp [repeatColumnsWithSelectorAt, repeatColumns, combine, ofColumns,
                withSelectorActivations,
                Nat.add_mul]
              omega
            · simp [repeatColumnsWithSelectorAt, repeatColumns, combine, ofColumns,
                withSelectorActivations, repeatedSelectorActivations,
                List.append_assoc]
      · exact unionColumns_nodup _ _
          (unionColumns_nodup [] columns (by simp))

/-- Folding repeated footprints with a fixed selector-row offset retains the exact
compact activation list. -/
@[synthesis_summary_norm]
theorem foldr_ofColumnsWithSelectorAt_eq_repeatColumnsWithSelectorAt
    (selector selectorOffset : ℕ) (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (List.ofFn fun i : Fin count =>
      (ofColumns columns (offset + stride * i.val + rowCount)
        constantSiteCount instanceRowExtent
        lookupActivationCount).withSelectorActivations
          [(selector, selectorOffset + stride * i.val)]).foldr combine {} =
      repeatColumnsWithSelectorAt selector selectorOffset columns offset stride rowCount
        constantSiteCount count instanceRowExtent lookupActivationCount := by
  rw [foldr_ofColumnsWithSelector_eq_repeatColumnsWithSelector_combine]
  · exact combine_empty _
  · simp

/-- Folding repeated one-selector rows retains the exact compact activation list. -/
@[synthesis_summary_norm]
theorem foldr_ofColumnsWithSelector_eq_repeatColumnsWithSelector
    (selector : ℕ) (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (List.ofFn fun i : Fin count =>
      (ofColumns columns (offset + stride * i.val + rowCount)
        constantSiteCount instanceRowExtent
        lookupActivationCount).withSelectorActivations
          [(selector, offset + stride * i.val)]).foldr combine {} =
      repeatColumnsWithSelector selector columns offset stride rowCount
        constantSiteCount count instanceRowExtent lookupActivationCount := by
  rw [foldr_ofColumnsWithSelector_eq_repeatColumnsWithSelector_combine selector offset]
  · exact combine_empty _
  · simp

private theorem foldr_ofColumnsWithSelectorPattern_combine
    (pattern : List (ℕ × ℕ)) (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent lookupActivationCount : ℕ)
    (accumulator : RegionSynthesisSummary)
    (haccumulator : accumulator.columns.Nodup) :
    (List.ofFn fun i : Fin count =>
      (ofColumns columns (offset + stride * i.val + rowCount)
        constantSiteCount instanceRowExtent
        lookupActivationCount).withSelectorActivations
          (pattern.map fun (selector, row) =>
            (selector, offset + stride * i.val + row))).foldr combine accumulator =
      (repeatColumnsWithSelectorPattern pattern columns offset stride rowCount
        constantSiteCount count instanceRowExtent lookupActivationCount).combine
        accumulator := by
  induction count generalizing accumulator with
  | zero =>
      simpa [repeatColumnsWithSelectorPattern, repeatColumns,
        withSelectorActivations, repeatedSelectorPattern] using
        (empty_combine accumulator haccumulator).symm
  | succ count inductionHypothesis =>
      rw [List.ofFn_succ']
      simp only [List.concat_eq_append, List.foldr_append, List.foldr,
        Fin.val_castSucc]
      rw [inductionHypothesis]
      · cases count with
        | zero =>
            apply RegionSynthesisSummary.ext
            · simp only [repeatColumnsWithSelectorPattern, repeatColumns,
                Nat.succ_ne_zero, if_false, combine_columns,
                withSelectorActivations_columns]
              exact unionColumns_empty_left _
                (unionColumns_nodup _ _
                  (unionColumns_nodup [] columns (by simp)))
            · simp [repeatColumnsWithSelectorPattern, repeatColumns, combine, ofColumns,
                withSelectorActivations, repeatedSelectorPattern]
            · simp [repeatColumnsWithSelectorPattern, repeatColumns, combine, ofColumns,
                withSelectorActivations, repeatedSelectorPattern]
            · simp [repeatColumnsWithSelectorPattern, repeatColumns, combine, ofColumns,
                withSelectorActivations, repeatedSelectorPattern]
            · simp [repeatColumnsWithSelectorPattern, repeatColumns, combine, ofColumns,
                withSelectorActivations, repeatedSelectorPattern]
            · simp [repeatColumnsWithSelectorPattern, repeatColumns, combine, ofColumns,
                withSelectorActivations, repeatedSelectorPattern]
        | succ count =>
            apply RegionSynthesisSummary.ext
            · simp only [repeatColumnsWithSelectorPattern, repeatColumns,
                Nat.succ_ne_zero, if_false, combine_columns,
                withSelectorActivations_columns, ofColumns_columns,
                Nat.add_one_sub_one]
              rw [← unionColumns_assoc, unionColumns_self]
            · simp only [repeatColumnsWithSelectorPattern, repeatColumns,
                Nat.succ_ne_zero, if_false, combine_rowCount,
                withSelectorActivations_rowCount, ofColumns_rowCount,
                Fin.val_last, Nat.add_one_sub_one]
              rw [Nat.max_eq_right]
              exact (Nat.add_le_add_right
                (Nat.add_le_add_left
                  (Nat.mul_le_mul_left stride (Nat.le_succ count)) offset)
                  rowCount).trans (Nat.le_max_left _ _)
            · simp [repeatColumnsWithSelectorPattern, repeatColumns, combine, ofColumns,
                withSelectorActivations, Nat.add_mul]
              omega
            · simp [repeatColumnsWithSelectorPattern, repeatColumns, combine, ofColumns,
                withSelectorActivations]
            · simp [repeatColumnsWithSelectorPattern, repeatColumns, combine, ofColumns,
                withSelectorActivations, Nat.add_mul]
              omega
            · simp [repeatColumnsWithSelectorPattern, repeatColumns, combine, ofColumns,
                withSelectorActivations, repeatedSelectorPattern,
                List.append_assoc]
      · exact unionColumns_nodup _ _
          (unionColumns_nodup [] columns (by simp))

/-- Folding repeated fixed selector patterns retains their compact exact summary. -/
@[synthesis_summary_norm]
theorem foldr_ofColumnsWithSelectorPattern_eq_repeatColumnsWithSelectorPattern
    (pattern : List (ℕ × ℕ)) (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (List.ofFn fun i : Fin count =>
      (ofColumns columns (offset + stride * i.val + rowCount)
        constantSiteCount instanceRowExtent
        lookupActivationCount).withSelectorActivations
          (pattern.map fun (selector, row) =>
            (selector, offset + stride * i.val + row))).foldr combine {} =
      repeatColumnsWithSelectorPattern pattern columns offset stride rowCount
        constantSiteCount count instanceRowExtent lookupActivationCount := by
  rw [foldr_ofColumnsWithSelectorPattern_combine]
  · exact combine_empty _
  · simp

def ofOperation (operation : RegionOperation F) : RegionSynthesisSummary where
  columns := unionColumns [] (regionOperationShapeColumns operation)
  rowCount := regionOperationRowExtent operation
  constantSiteCount := regionOperationConstantSiteCount operation
  lookupActivationCount := regionOperationLookupActivationCount operation
  instanceRowExtent := regionOperationInstanceRowExtent operation
  selectorActivations := regionOperationSelectorActivations operation

@[circuit_norm] theorem ofOperation_columns (operation : RegionOperation F) :
    (ofOperation operation).columns =
      unionColumns [] (regionOperationShapeColumns operation) := rfl

@[circuit_norm] theorem ofOperation_rowCount (operation : RegionOperation F) :
    (ofOperation operation).rowCount = regionOperationRowExtent operation := rfl

@[circuit_norm] theorem ofOperation_constantSiteCount
    (operation : RegionOperation F) :
    (ofOperation operation).constantSiteCount =
      regionOperationConstantSiteCount operation := rfl

@[circuit_norm] theorem ofOperation_lookupActivationCount
    (operation : RegionOperation F) :
    (ofOperation operation).lookupActivationCount =
      regionOperationLookupActivationCount operation := rfl

@[circuit_norm] theorem ofOperation_instanceRowExtent
    (operation : RegionOperation F) :
    (ofOperation operation).instanceRowExtent =
      regionOperationInstanceRowExtent operation := rfl

@[circuit_norm] theorem ofOperation_selectorActivations
    (operation : RegionOperation F) :
    (ofOperation operation).selectorActivations =
      regionOperationSelectorActivations operation := rfl

end RegionSynthesisSummary

/-- The operation-independent portion of one V1 region measurement. Region indices
are supplied later by the enclosing layouter sequence. -/
@[ext] structure RegionShapeSummary where
  columns : List RegionColumn
  rowCount : ℕ
deriving Inhabited, DecidableEq, Repr, BEq, ReflBEq, LawfulBEq

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

@[circuit_norm, synthesis_summary_norm]
theorem RegionSynthesisSummary.withSelectorActivations_toRegionShapeSummary
    (summary : RegionSynthesisSummary) (activations : List (ℕ × ℕ)) :
    (summary.withSelectorActivations activations).toRegionShapeSummary =
      summary.toRegionShapeSummary := rfl

@[circuit_norm, synthesis_summary_norm]
theorem RegionSynthesisSummary.repeatColumnsWithSelectorPattern_toRegionShapeSummary
    (pattern : List (ℕ × ℕ)) (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorPattern pattern columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).toRegionShapeSummary =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).toRegionShapeSummary := rfl

@[circuit_norm, synthesis_summary_norm]
theorem RegionSynthesisSummary.repeatColumnsWithSelectorAt_toRegionShapeSummary
    (selector selectorOffset : ℕ) (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorAt selector selectorOffset columns offset stride rowCount
      constantSiteCount count instanceRowExtent lookupActivationCount).toRegionShapeSummary =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).toRegionShapeSummary := rfl

@[circuit_norm, synthesis_summary_norm]
theorem RegionSynthesisSummary.repeatColumnsWithSelector_toRegionShapeSummary
    (selector : ℕ) (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelector selector columns offset stride rowCount constantSiteCount
      count instanceRowExtent lookupActivationCount).toRegionShapeSummary =
      (repeatColumns columns offset stride rowCount constantSiteCount count
        instanceRowExtent lookupActivationCount).toRegionShapeSummary := rfl

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

@[circuit_norm] theorem regionSynthesisSummary_nil_lookupActivationCount :
    (regionSynthesisSummary ([] : RegionOperations F)).lookupActivationCount = 0 := rfl

@[circuit_norm] theorem regionSynthesisSummary_nil_instanceRowExtent :
    (regionSynthesisSummary ([] : RegionOperations F)).instanceRowExtent = 0 := rfl

@[circuit_norm] theorem regionSynthesisSummary_nil_selectorActivations :
    (regionSynthesisSummary ([] : RegionOperations F)).selectorActivations = [] := rfl

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

/-- The reduced selector-activation list is exactly the concatenation of the
activation contributions of the region operations. -/
theorem regionSynthesisSummary_selectorActivations_eq_flatMap
    (operations : RegionOperations F) :
    (regionSynthesisSummary operations).selectorActivations =
      operations.flatMap regionOperationSelectorActivations := by
  induction operations with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      simp only [regionSynthesisSummary, RegionSynthesisSummary.combine,
        RegionSynthesisSummary.ofOperation, List.flatMap_cons,
        inductionHypothesis]

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

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_cons_lookupActivationCount
    (operation : RegionOperation F) (rest : RegionOperations F) :
    (regionSynthesisSummary (operation :: rest)).lookupActivationCount =
      regionOperationLookupActivationCount operation +
        (regionSynthesisSummary rest).lookupActivationCount := rfl

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_cons_instanceRowExtent
    (operation : RegionOperation F) (rest : RegionOperations F) :
    (regionSynthesisSummary (operation :: rest)).instanceRowExtent =
      max (regionOperationInstanceRowExtent operation)
        (regionSynthesisSummary rest).instanceRowExtent := rfl

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_cons_selectorActivations
    (operation : RegionOperation F) (rest : RegionOperations F) :
    (regionSynthesisSummary (operation :: rest)).selectorActivations =
      regionOperationSelectorActivations operation ++
        (regionSynthesisSummary rest).selectorActivations := rfl

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
  · simp [regionSynthesisSummary_cons_lookupActivationCount,
      regionOperationLookupActivationCount]
  · simp [regionSynthesisSummary_cons_selectorActivations,
      regionOperationSelectorActivations]

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
theorem regionSynthesisSummary_enableLookup_cons_lookupActivationCount
    (lookup : LookupArgument F) (enabled : List Selector) (row : ℕ)
    (rest : RegionOperations F) :
    (regionSynthesisSummary
      (.enableLookup lookup enabled row :: rest)).lookupActivationCount =
        1 + (regionSynthesisSummary rest).lookupActivationCount := by
  rw [regionSynthesisSummary_cons_lookupActivationCount]
  rfl

@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_constrainConstant_cons_constantSiteCount
    (cell : Cell) (constant : F) (rest : RegionOperations F) :
    (regionSynthesisSummary
      (.constrainConstant cell constant :: rest)).constantSiteCount =
        1 + (regionSynthesisSummary rest).constantSiteCount := by
  rw [regionSynthesisSummary_cons_constantSiteCount]
  rfl

/-- An advice assignment contributes its concrete one-column summary before the
remaining operations. -/
@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_assignAdvice_cons
    (column : Column .advice) (row : ℕ) (value : WitgenIR F 1)
    (rest : RegionOperations F) :
    regionSynthesisSummary (.assignAdvice column row value :: rest) =
      (RegionSynthesisSummary.ofColumns
        [.column .advice column.index] (row + 1) 0).combine
          (regionSynthesisSummary rest) := rfl

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
  · rfl
  · rfl

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
  · rfl
  · rfl

/-- A single gate enable reduces to its selector-column summary. -/
@[circuit_norm, synthesis_summary_norm]
theorem regionSynthesisSummary_single_enableGate
    (gate : Gate F) (row : ℕ) :
    regionSynthesisSummary [.enableGate gate row] =
      (RegionSynthesisSummary.ofColumns
        [.selector gate.selector.index] (row + 1) 0).withSelectorActivations
          [(gate.selector.index, row)] := by
  apply RegionSynthesisSummary.ext
  · simp only [RegionSynthesisSummary.withSelectorActivations,
      regionSynthesisSummary_enableGate_cons_columns,
      regionSynthesisSummary_nil_columns,
      RegionSynthesisSummary.ofColumns_columns, unionColumns_nil_right]
  · simp only [RegionSynthesisSummary.withSelectorActivations,
      regionSynthesisSummary_enableGate_cons_rowCount,
      regionSynthesisSummary_nil_rowCount,
      RegionSynthesisSummary.ofColumns_rowCount, Nat.max_zero]
  · simp only [RegionSynthesisSummary.withSelectorActivations,
      regionSynthesisSummary_enableGate_cons_constantSiteCount,
      regionSynthesisSummary_nil_constantSiteCount,
      RegionSynthesisSummary.ofColumns_constantSiteCount]
  · simp [RegionSynthesisSummary.withSelectorActivations,
      regionSynthesisSummary, RegionSynthesisSummary.combine,
      RegionSynthesisSummary.ofOperation, regionOperationInstanceRowExtent,
      RegionSynthesisSummary.ofColumns_instanceRowExtent]
  · rfl
  · rfl

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

/-- An advice assignment records its physical column in the region's reduced
synthesis footprint. -/
theorem adviceColumn_mem_physicalColumns_regionSynthesisSummary_of_assignAdvice_mem
    (operations : RegionOperations F) (column : Column .advice)
    (row : ℕ) (value : WitgenIR F 1)
    (hoperation : .assignAdvice column row value ∈ operations) :
    RegionColumn.column .advice column.index ∈
      physicalColumns (regionSynthesisSummary operations).columns := by
  rw [physicalColumns, List.mem_filter]
  constructor
  · apply mem_regionSynthesisSummary_columns_of_mem operations
      (.assignAdvice column row value) hoperation
    simp [regionOperationShapeColumns]
  · trivial

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
  fixedColumns : ∀ input, configLawful input → List (Column .fixed) := fun _ _ => []
  constantColumns : ∀ input, configLawful input → List (Column .fixed) := fun _ _ => []
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
  fixedColumns_eq : self.fixedColumns input configLawful = []
  constantColumns_eq : self.constantColumns input configLawful = []
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

def RegionOperations.CopyCellsCovered (operations : RegionOperations F)
    (region : RegionIndex) (inputCells : List Cell) : Prop :=
  ∀ cell ∈ operations.copiedCells,
    cell ∈ inputCells ++ operations.assignedCells region

/-- Execution-order-sensitive copy provenance inside one region. -/
inductive RegionOperations.CopyCellsAssignedFrom (region : RegionIndex) :
    List Cell → RegionOperations F → Prop where
  | nil available : CopyCellsAssignedFrom region available []
  | assignAdvice available column row compute rest :
      CopyCellsAssignedFrom region (.of region row column :: available) rest →
        CopyCellsAssignedFrom region available
          (.assignAdvice column row compute :: rest)
  | assignFixed available column row value rest :
      CopyCellsAssignedFrom region (.of region row column :: available) rest →
        CopyCellsAssignedFrom region available (.assignFixed column row value :: rest)
  | enableGate available gate row rest :
      CopyCellsAssignedFrom region available rest →
        CopyCellsAssignedFrom region available (.enableGate gate row :: rest)
  | enableLookup available lookup selectors row rest :
      CopyCellsAssignedFrom region available rest →
        CopyCellsAssignedFrom region available
          (.enableLookup lookup selectors row :: rest)
  | constrainEqual available left right rest :
      left ∈ available → right ∈ available →
        CopyCellsAssignedFrom region available rest →
          CopyCellsAssignedFrom region available (.constrainEqual left right :: rest)
  | constrainConstant available cell value rest :
      cell ∈ available → CopyCellsAssignedFrom region available rest →
        CopyCellsAssignedFrom region available (.constrainConstant cell value :: rest)
  | constrainInstance available cell column row rest :
      cell ∈ available → CopyCellsAssignedFrom region available rest →
        CopyCellsAssignedFrom region available
          (.constrainInstance cell column row :: rest)

def RegionOperations.CopyCellsAssigned (operations : RegionOperations F)
    (region : RegionIndex) (inputCells : List Cell) : Prop :=
  CopyCellsAssignedFrom region inputCells operations

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_nil_iff
    (region : RegionIndex) (available : List Cell) :
    CopyCellsAssignedFrom (F := F) region available [] ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact .nil available

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_assignAdvice_iff
    (region : RegionIndex) (available : List Cell) (column : Column .advice)
    (row : ℕ) (compute : WitgenIR F 1) (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available (.assignAdvice column row compute :: rest) ↔
      CopyCellsAssignedFrom region (.of region row column :: available) rest := by
  constructor
  · intro h
    cases h with | assignAdvice _ _ _ _ _ hrest => exact hrest
  · exact CopyCellsAssignedFrom.assignAdvice available column row compute rest

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_assignFixed_iff
    (region : RegionIndex) (available : List Cell) (column : Column .fixed)
    (row : ℕ) (value : F) (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available (.assignFixed column row value :: rest) ↔
      CopyCellsAssignedFrom region (.of region row column :: available) rest := by
  constructor
  · intro h
    cases h with | assignFixed _ _ _ _ _ hrest => exact hrest
  · exact CopyCellsAssignedFrom.assignFixed available column row value rest

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_enableGate_iff
    (region : RegionIndex) (available : List Cell) (gate : Gate F)
    (row : ℕ) (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available (.enableGate gate row :: rest) ↔
      CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | enableGate _ _ _ _ hrest => exact hrest
  · exact CopyCellsAssignedFrom.enableGate available gate row rest

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_enableLookup_iff
    (region : RegionIndex) (available : List Cell) (lookup : LookupArgument F)
    (selectors : List Selector) (row : ℕ) (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available
        (.enableLookup lookup selectors row :: rest) ↔
      CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | enableLookup _ _ _ _ _ hrest => exact hrest
  · exact CopyCellsAssignedFrom.enableLookup available lookup selectors row rest

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_constrainEqual_iff
    (region : RegionIndex) (available : List Cell) (left right : Cell)
    (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available (.constrainEqual left right :: rest) ↔
      left ∈ available ∧ right ∈ available ∧
        CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | constrainEqual _ _ _ _ hleft hright hrest =>
      exact ⟨hleft, hright, hrest⟩
  · rintro ⟨hleft, hright, hrest⟩
    exact .constrainEqual available left right rest hleft hright hrest

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_constrainConstant_iff
    (region : RegionIndex) (available : List Cell) (cell : Cell)
    (value : F) (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available (.constrainConstant cell value :: rest) ↔
      cell ∈ available ∧ CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | constrainConstant _ _ _ _ hcell hrest => exact ⟨hcell, hrest⟩
  · rintro ⟨hcell, hrest⟩
    exact .constrainConstant available cell value rest hcell hrest

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_constrainInstance_iff
    (region : RegionIndex) (available : List Cell) (cell : Cell)
    (column : Column .instance) (row : ℕ) (rest : RegionOperations F) :
    CopyCellsAssignedFrom region available
        (.constrainInstance cell column row :: rest) ↔
      cell ∈ available ∧ CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | constrainInstance _ _ _ _ _ hcell hrest => exact ⟨hcell, hrest⟩
  · rintro ⟨hcell, hrest⟩
    exact .constrainInstance available cell column row rest hcell hrest

/-- Available cells after executing one region body. -/
def RegionOperations.assignedCellsAfter (region : RegionIndex)
    (available : List Cell) (operations : RegionOperations F) : List Cell :=
  operations.foldl (fun cells operation =>
    operation.assignedCells region ++ cells) available

theorem RegionOperations.assignedCellsAfter_append
    (left right : RegionOperations F) (region : RegionIndex)
    (available : List Cell) :
    (left ++ right).assignedCellsAfter region available =
      right.assignedCellsAfter region
        (left.assignedCellsAfter region available) := by
  simp only [assignedCellsAfter, List.foldl_append]

@[keygen_norm, keygen_spine]
theorem RegionOperations.copyCellsAssignedFrom_append_iff
    (region : RegionIndex) (available : List Cell)
    (left right : RegionOperations F) :
    CopyCellsAssignedFrom region available (left ++ right) ↔
      CopyCellsAssignedFrom region available left ∧
        CopyCellsAssignedFrom region
          (left.assignedCellsAfter region available) right := by
  induction left generalizing available with
  | nil =>
      simp only [List.nil_append, assignedCellsAfter, List.foldl_nil,
        copyCellsAssignedFrom_nil_iff, true_and]
  | cons operation rest inductionHypothesis =>
      cases operation <;>
        simp only [List.cons_append, assignedCellsAfter, List.foldl_cons,
          RegionOperation.assignedCells,
          copyCellsAssignedFrom_assignAdvice_iff,
          copyCellsAssignedFrom_assignFixed_iff,
          copyCellsAssignedFrom_enableGate_iff,
          copyCellsAssignedFrom_enableLookup_iff,
          copyCellsAssignedFrom_constrainEqual_iff,
          copyCellsAssignedFrom_constrainConstant_iff,
          copyCellsAssignedFrom_constrainInstance_iff,
          inductionHypothesis, List.nil_append, and_assoc]

/-- Copy provenance remains valid when the caller makes more cells available. -/
theorem RegionOperations.CopyCellsAssignedFrom.mono
    {operations : RegionOperations F} {region : RegionIndex}
    {available larger : List Cell}
    (hassigned : operations.CopyCellsAssignedFrom region available)
    (havailable : ∀ cell, cell ∈ available → cell ∈ larger) :
    operations.CopyCellsAssignedFrom region larger := by
  induction hassigned generalizing larger with
  | nil => exact .nil larger
  | assignAdvice available column row compute rest hassigned inductionHypothesis =>
      exact .assignAdvice larger column row compute rest
        (inductionHypothesis fun cell hcell => by
          simp only [List.mem_cons] at hcell ⊢
          rcases hcell with rfl | hcell
          · exact Or.inl rfl
          · exact Or.inr (havailable cell hcell))
  | assignFixed available column row value rest hassigned inductionHypothesis =>
      exact .assignFixed larger column row value rest
        (inductionHypothesis fun cell hcell => by
          simp only [List.mem_cons] at hcell ⊢
          rcases hcell with rfl | hcell
          · exact Or.inl rfl
          · exact Or.inr (havailable cell hcell))
  | enableGate available gate row rest hassigned inductionHypothesis =>
      exact .enableGate larger gate row rest
        (inductionHypothesis havailable)
  | enableLookup available lookup selectors row rest hassigned inductionHypothesis =>
      exact .enableLookup larger lookup selectors row rest
        (inductionHypothesis havailable)
  | constrainEqual available left right rest hleft hright hassigned
      inductionHypothesis =>
      exact .constrainEqual larger left right rest
        (havailable left hleft) (havailable right hright)
        (inductionHypothesis havailable)
  | constrainConstant available cell value rest hcell hassigned inductionHypothesis =>
      exact .constrainConstant larger cell value rest
        (havailable cell hcell) (inductionHypothesis havailable)
  | constrainInstance available cell column row rest hcell hassigned
      inductionHypothesis =>
      exact .constrainInstance larger cell column row rest
        (havailable cell hcell) (inductionHypothesis havailable)

/-- A region fragment containing no copy-like operation is lawful for every incoming
cell state. -/
@[keygen_helper]
theorem RegionOperations.copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
    (operations : RegionOperations F) (region : RegionIndex)
    (available : List Cell)
    (hoperations : operations.Forall fun operation =>
      operation.copiedCells = []) :
    operations.CopyCellsAssignedFrom region available := by
  induction operations generalizing available with
  | nil => exact .nil available
  | cons operation rest inductionHypothesis =>
      rw [List.forall_cons] at hoperations
      cases operation with
      | assignAdvice column row compute =>
          exact .assignAdvice available column row compute rest
            (inductionHypothesis _ hoperations.2)
      | assignFixed column row value =>
          exact .assignFixed available column row value rest
            (inductionHypothesis _ hoperations.2)
      | enableGate gate row =>
          exact .enableGate available gate row rest
            (inductionHypothesis _ hoperations.2)
      | enableLookup lookup selectors row =>
          exact .enableLookup available lookup selectors row rest
            (inductionHypothesis _ hoperations.2)
      | constrainEqual left right =>
          cases hoperations.1
      | constrainConstant cell value =>
          cases hoperations.1
      | constrainInstance cell column row =>
          cases hoperations.1

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

/-- Execution-order-sensitive copy provenance through the layouter stream. -/
inductive Operations.CopyCellsAssignedFrom :
    RegionIndex → List Cell → Operations F → Prop where
  | nil region available : CopyCellsAssignedFrom region available []
  | region region available name body rest :
      body.CopyCellsAssignedFrom region available →
        CopyCellsAssignedFrom (region + 1)
          (body.assignedCellsAfter region available) rest →
            CopyCellsAssignedFrom region available (.region name body :: rest)
  | constrainInstance region available cell column row rest :
      cell ∈ available → CopyCellsAssignedFrom region available rest →
        CopyCellsAssignedFrom region available
          (.constrainInstance cell column row :: rest)
  | loadTable region available column values rest :
      CopyCellsAssignedFrom region available rest →
        CopyCellsAssignedFrom region available (.loadTable column values :: rest)

@[keygen_norm, keygen_spine]
theorem Operations.copyCellsAssignedFrom_nil_iff
    (region : RegionIndex) (available : List Cell) :
    CopyCellsAssignedFrom (F := F) region available [] ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact .nil region available

@[keygen_norm, keygen_spine]
theorem Operations.copyCellsAssignedFrom_region_iff
    (region : RegionIndex) (available : List Cell) (name : String)
    (body : RegionOperations F) (rest : Operations F) :
    CopyCellsAssignedFrom region available (.region name body :: rest) ↔
      body.CopyCellsAssignedFrom region available ∧
        CopyCellsAssignedFrom (region + 1)
          (body.assignedCellsAfter region available) rest := by
  constructor
  · intro h
    cases h with | region _ _ _ _ _ hbody hrest => exact ⟨hbody, hrest⟩
  · rintro ⟨hbody, hrest⟩
    exact .region region available name body rest hbody hrest

@[keygen_norm, keygen_spine]
theorem Operations.copyCellsAssignedFrom_constrainInstance_iff
    (region : RegionIndex) (available : List Cell) (cell : Cell)
    (column : Column .instance) (row : ℕ) (rest : Operations F) :
    CopyCellsAssignedFrom region available
        (.constrainInstance cell column row :: rest) ↔
      cell ∈ available ∧ CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | constrainInstance _ _ _ _ _ _ hcell hrest => exact ⟨hcell, hrest⟩
  · rintro ⟨hcell, hrest⟩
    exact .constrainInstance region available cell column row rest hcell hrest

@[keygen_norm, keygen_spine]
theorem Operations.copyCellsAssignedFrom_loadTable_iff
    (region : RegionIndex) (available : List Cell) (column : TableColumn)
    (values : List F) (rest : Operations F) :
    CopyCellsAssignedFrom region available (.loadTable column values :: rest) ↔
      CopyCellsAssignedFrom region available rest := by
  constructor
  · intro h
    cases h with | loadTable _ _ _ _ _ hrest => exact hrest
  · exact CopyCellsAssignedFrom.loadTable region available column values rest

/-- A layouter stream containing no copy-like operation is lawful for every incoming
cell state. -/
@[keygen_helper]
theorem Operations.copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
    (operations : Operations F) (region : RegionIndex)
    (available : List Cell)
    (hoperations : operations.Forall fun operation =>
      operation.copiedCells = []) :
    operations.CopyCellsAssignedFrom region available := by
  induction operations generalizing region available with
  | nil => exact .nil region available
  | cons operation rest inductionHypothesis =>
      rw [List.forall_cons] at hoperations
      cases operation with
      | region name body =>
          apply Operations.CopyCellsAssignedFrom.region region available name body rest
          · apply RegionOperations.copyCellsAssignedFrom_of_forall_copiedCells_eq_nil
            rw [List.forall_iff_forall_mem]
            simpa only [Operation.copiedCells, RegionOperations.copiedCells,
              List.flatMap_eq_nil_iff] using hoperations.1
          · exact inductionHypothesis (region := region + 1)
              (available := body.assignedCellsAfter region available) hoperations.2
      | constrainInstance cell column row =>
          simp only [Operation.copiedCells, List.cons_ne_nil] at hoperations
          exact False.elim hoperations.1
      | loadTable column values =>
          exact .loadTable region available column values rest
            (inductionHypothesis (region := region) (available := available)
              hoperations.2)

def Operations.CopyCellsAssigned (operations : Operations F)
    (initialRegion : RegionIndex) (inputCells : List Cell) : Prop :=
  CopyCellsAssignedFrom initialRegion inputCells operations

/-- Set-level consequence used by compiler proofs. -/
def Operations.CopyCellsCovered (operations : Operations F)
    (initialRegion : RegionIndex) (inputCells : List Cell) : Prop :=
  ∀ cell ∈ operations.copiedCells,
    cell ∈ inputCells ++ operations.assignedCellsFrom initialRegion

theorem RegionOperations.mem_assignedCellsAfter_iff
    (operations : RegionOperations F) (region : RegionIndex)
    (available : List Cell) (cell : Cell) :
    cell ∈ operations.assignedCellsAfter region available ↔
      cell ∈ available ++ operations.assignedCells region := by
  unfold assignedCellsAfter assignedCells
  induction operations generalizing available with
  | nil => simp
  | cons operation rest inductionHypothesis =>
      simp only [List.foldl_cons, List.flatMap_cons]
      rw [inductionHypothesis]
      cases operation <;> simp [RegionOperation.assignedCells, or_left_comm]

theorem RegionOperations.mem_assignedCellsAfter_of_mem
    (operations : RegionOperations F) (region : RegionIndex)
    (available : List Cell) (cell : Cell) (hcell : cell ∈ available) :
    cell ∈ operations.assignedCellsAfter region available := by
  rw [mem_assignedCellsAfter_iff, List.mem_append]
  exact Or.inl hcell

/-- Layouter-level copy provenance remains valid when the caller makes more cells
available. -/
theorem Operations.CopyCellsAssignedFrom.mono
    {operations : Operations F} {region : RegionIndex}
    {available larger : List Cell}
    (hassigned : operations.CopyCellsAssignedFrom region available)
    (havailable : ∀ cell, cell ∈ available → cell ∈ larger) :
    operations.CopyCellsAssignedFrom region larger := by
  induction hassigned generalizing larger with
  | nil currentRegion => exact .nil currentRegion larger
  | region region available name body rest hbody hrest restInduction =>
      apply Operations.CopyCellsAssignedFrom.region region larger name body rest
      · exact hbody.mono havailable
      · apply restInduction
        intro cell hcell
        rw [RegionOperations.mem_assignedCellsAfter_iff] at hcell ⊢
        simp only [List.mem_append] at hcell ⊢
        rcases hcell with hcell | hcell
        · exact Or.inl (havailable cell hcell)
        · exact Or.inr hcell
  | constrainInstance region available cell column row rest hcell hassigned
      inductionHypothesis =>
      exact .constrainInstance region larger cell column row rest
        (havailable cell hcell) (inductionHypothesis havailable)
  | loadTable region available column values rest hassigned inductionHypothesis =>
      exact .loadTable region larger column values rest
        (inductionHypothesis havailable)

theorem RegionOperations.copyCellsCovered_of_assignedFrom
    (operations : RegionOperations F) (region : RegionIndex)
    (available : List Cell)
    (hassigned : operations.CopyCellsAssignedFrom region available) :
    operations.CopyCellsCovered region available := by
  induction operations generalizing available with
  | nil => simp [CopyCellsCovered, copiedCells]
  | cons operation rest inductionHypothesis =>
      intro cell hcell
      cases operation with
      | assignAdvice column row value =>
          cases hassigned with
          | assignAdvice _ _ _ _ _ hassignedRest =>
          have hrest := inductionHypothesis
            (.of region row column :: available) hassignedRest cell hcell
          simp only [List.mem_append, List.mem_cons,
            assignedCells, List.flatMap_cons, RegionOperation.assignedCells,
            List.singleton_append] at hrest ⊢
          tauto
      | assignFixed column row value =>
          cases hassigned with
          | assignFixed _ _ _ _ _ hassignedRest =>
          have hrest := inductionHypothesis
            (.of region row column :: available) hassignedRest cell hcell
          simp only [List.mem_append, List.mem_cons,
            assignedCells, List.flatMap_cons, RegionOperation.assignedCells,
            List.singleton_append] at hrest ⊢
          tauto
      | enableGate gate row =>
          cases hassigned with
          | enableGate _ _ _ _ hassignedRest =>
            exact inductionHypothesis available hassignedRest cell hcell
      | enableLookup lookup selectors row =>
          cases hassigned with
          | enableLookup _ _ _ _ _ hassignedRest =>
            exact inductionHypothesis available hassignedRest cell hcell
      | constrainEqual left right =>
          rw [copyCellsAssignedFrom_constrainEqual_iff] at hassigned
          simp only [copiedCells, List.flatMap_cons,
            RegionOperation.copiedCells, List.mem_append] at hcell
          simp only [assignedCells, List.flatMap_cons,
            RegionOperation.assignedCells, List.nil_append]
          rcases hcell with hcurrent | hrest
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcurrent
            rcases hcurrent with rfl | rfl
            · exact List.mem_append_left _ hassigned.1
            · exact List.mem_append_left _ hassigned.2.1
          · exact inductionHypothesis available hassigned.2.2 cell hrest
      | constrainConstant copied value =>
          rw [copyCellsAssignedFrom_constrainConstant_iff] at hassigned
          simp only [copiedCells, List.flatMap_cons,
            RegionOperation.copiedCells, List.mem_append] at hcell
          simp only [assignedCells, List.flatMap_cons,
            RegionOperation.assignedCells, List.nil_append]
          rcases hcell with hcurrent | hrest
          · rw [List.mem_singleton] at hcurrent
            subst cell
            exact List.mem_append_left _ hassigned.1
          · exact inductionHypothesis available hassigned.2 cell hrest
      | constrainInstance copied column row =>
          rw [RegionOperations.copyCellsAssignedFrom_constrainInstance_iff] at hassigned
          simp only [copiedCells, List.flatMap_cons,
            RegionOperation.copiedCells, List.mem_append] at hcell
          simp only [assignedCells, List.flatMap_cons,
            RegionOperation.assignedCells, List.nil_append]
          rcases hcell with hcurrent | hrest
          · rw [List.mem_singleton] at hcurrent
            subst cell
            exact List.mem_append_left _ hassigned.1
          · exact inductionHypothesis available hassigned.2 cell hrest

theorem Operations.copyCellsCovered_of_assignedFrom
    (operations : Operations F) (initialRegion : RegionIndex)
    (available : List Cell)
    (hassigned : CopyCellsAssignedFrom initialRegion available operations) :
    operations.CopyCellsCovered initialRegion available := by
  induction operations generalizing initialRegion available with
  | nil => simp [CopyCellsCovered, Operations.copiedCells]
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body =>
          intro cell hcell
          rw [copyCellsAssignedFrom_region_iff] at hassigned
          rw [Operations.copiedCells, List.mem_flatMap] at hcell
          rcases hcell with ⟨candidate, hcandidate, hcell⟩
          rw [List.mem_cons] at hcandidate
          rcases hcandidate with rfl | hrest
          · have hcovered := body.copyCellsCovered_of_assignedFrom
              initialRegion available hassigned.1 cell hcell
            rw [List.mem_append] at hcovered
            rw [Operations.assignedCellsFrom, List.mem_append]
            exact Or.imp_right (fun hbody => List.mem_append_left _ hbody) hcovered
          · have hcovered := inductionHypothesis (initialRegion + 1)
              (body.assignedCellsAfter initialRegion available)
              hassigned.2 cell (List.mem_flatMap.mpr ⟨candidate, hrest, hcell⟩)
            rw [List.mem_append] at hcovered
            rw [Operations.assignedCellsFrom, List.mem_append]
            rcases hcovered with hafter | hrestAssigned
            · rw [body.mem_assignedCellsAfter_iff] at hafter
              rw [List.mem_append] at hafter
              exact Or.imp_right (List.mem_append_left _) hafter
            · exact Or.inr (List.mem_append_right _ hrestAssigned)
      | constrainInstance copied column row =>
          intro cell hcell
          rw [Operations.copyCellsAssignedFrom_constrainInstance_iff] at hassigned
          rw [Operations.copiedCells, List.mem_flatMap] at hcell
          rcases hcell with ⟨candidate, hcandidate, hcell⟩
          rw [List.mem_cons] at hcandidate
          rcases hcandidate with rfl | hrest
          · simp only [Operation.copiedCells, List.mem_singleton] at hcell
            subst cell
            exact List.mem_append_left _ hassigned.1
          · exact inductionHypothesis initialRegion available hassigned.2 cell
              (List.mem_flatMap.mpr ⟨candidate, hrest, hcell⟩)
      | loadTable column values =>
          cases hassigned with
          | loadTable _ _ _ _ _ hassignedRest =>
            exact inductionHypothesis initialRegion available hassignedRest

theorem Operations.copyCellsCovered_of_assigned
    (operations : Operations F) (initialRegion : RegionIndex)
    (inputCells : List Cell)
    (hassigned : operations.CopyCellsAssigned initialRegion inputCells) :
    operations.CopyCellsCovered initialRegion inputCells :=
  operations.copyCellsCovered_of_assignedFrom initialRegion inputCells hassigned

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
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    RegionOperation F → Prop
  | .assignFixed column _ _ => column ∈ fixedColumns
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
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    Operation F → Prop
  | .region _ body =>
      body.Forall (RegionOperation.KeygenRegistered gates lookups fixedColumns
        permutationColumns)
  | .constrainInstance cell column _ =>
      cell.column ∈ permutationColumns ∧ column.toAny ∈ permutationColumns
  | .loadTable table _ => table.inner ∈ fixedColumns

/--
Every gate, lookup, and equality-dependent operation emitted by synthesis is covered
by the supplied configure-produced capabilities.
-/
def Operations.KeygenRegistered
    (operations : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) : Prop :=
  operations.Forall (Operation.KeygenRegistered gates lookups fixedColumns
    permutationColumns)

@[circuit_norm]
theorem Operations.KeygenRegistered.nil
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered [] gates lookups fixedColumns permutationColumns := by
  simp [Operations.KeygenRegistered]

@[circuit_norm]
theorem Operations.KeygenRegistered.append
    (left right : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered (left ++ right) gates lookups fixedColumns
        permutationColumns ↔
      Operations.KeygenRegistered left gates lookups fixedColumns permutationColumns ∧
        Operations.KeygenRegistered right gates lookups fixedColumns permutationColumns := by
  simp [Operations.KeygenRegistered]

@[circuit_norm]
theorem Operations.KeygenRegistered.region_cons
    (name : String) (body : RegionOperations F) (rest : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered (.region name body :: rest) gates lookups fixedColumns
        permutationColumns ↔
      body.Forall (RegionOperation.KeygenRegistered gates lookups fixedColumns
        permutationColumns) ∧
        Operations.KeygenRegistered rest gates lookups fixedColumns permutationColumns := by
  simp [Operations.KeygenRegistered, Operation.KeygenRegistered]

@[circuit_norm]
theorem Operations.KeygenRegistered.constrainInstance_cons
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered
        (.constrainInstance cell column row :: rest) gates lookups fixedColumns
          permutationColumns ↔
      cell.column ∈ permutationColumns ∧ column.toAny ∈ permutationColumns ∧
        Operations.KeygenRegistered rest gates lookups fixedColumns permutationColumns := by
  simp [Operations.KeygenRegistered, Operation.KeygenRegistered, and_assoc]

@[circuit_norm]
theorem Operations.KeygenRegistered.loadTable_cons
    (table : TableColumn) (values : List F) (rest : Operations F)
    (gates : List (Gate F)) (lookups : List (LookupArgument F))
    (fixedColumns : List (Column .fixed))
    (permutationColumns : List AnyColumn) :
    Operations.KeygenRegistered
        (.loadTable table values :: rest) gates lookups fixedColumns permutationColumns ↔
      table.inner ∈ fixedColumns ∧
        Operations.KeygenRegistered rest gates lookups fixedColumns permutationColumns := by
  simp [Operations.KeygenRegistered, Operation.KeygenRegistered]

/-- Registration is monotone in both configure-produced argument lists. -/
theorem Operations.KeygenRegistered.mono
    {operations : Operations F}
    {sourceGates targetGates : List (Gate F)}
    {sourceLookups targetLookups : List (LookupArgument F)}
    {sourceFixedColumns targetFixedColumns : List (Column .fixed)}
    {sourcePermutationColumns targetPermutationColumns : List AnyColumn}
    (hregistered :
      operations.KeygenRegistered sourceGates sourceLookups sourceFixedColumns
        sourcePermutationColumns)
    (hgates : ∀ gate, gate ∈ sourceGates → gate ∈ targetGates)
    (hlookups :
      ∀ argument, argument ∈ sourceLookups → argument ∈ targetLookups)
    (hfixedColumns : ∀ column,
      column ∈ sourceFixedColumns → column ∈ targetFixedColumns)
    (hpermutationColumns : ∀ column,
      column ∈ sourcePermutationColumns → column ∈ targetPermutationColumns) :
    operations.KeygenRegistered targetGates targetLookups targetFixedColumns
      targetPermutationColumns := by
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
          =>
          trivial
      | assignFixed column row value =>
          exact hfixedColumns column hregionRegistered
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
      exact hfixedColumns _ hoperationRegistered

/-- Region-operation registration is monotone in both available argument lists. -/
theorem RegionOperations.keygenRegistered_mono
    {operations : RegionOperations F}
    {sourceGates targetGates : List (Gate F)}
    {sourceLookups targetLookups : List (LookupArgument F)}
    {sourceFixedColumns targetFixedColumns : List (Column .fixed)}
    {sourcePermutationColumns targetPermutationColumns : List AnyColumn}
    (hregistered :
      operations.Forall
        (RegionOperation.KeygenRegistered sourceGates sourceLookups
          sourceFixedColumns sourcePermutationColumns))
    (hgates : ∀ gate, gate ∈ sourceGates → gate ∈ targetGates)
    (hlookups :
      ∀ argument, argument ∈ sourceLookups → argument ∈ targetLookups)
    (hfixedColumns : ∀ column,
      column ∈ sourceFixedColumns → column ∈ targetFixedColumns)
    (hpermutationColumns : ∀ column,
      column ∈ sourcePermutationColumns → column ∈ targetPermutationColumns) :
    operations.Forall
      (RegionOperation.KeygenRegistered targetGates targetLookups
        targetFixedColumns targetPermutationColumns) := by
  rw [List.forall_iff_forall_mem] at hregistered ⊢
  intro operation hoperation
  have hoperationRegistered := hregistered operation hoperation
  cases operation with
  | enableGate gate row =>
      exact hgates gate hoperationRegistered
  | enableLookup argument selectors row =>
      exact hlookups argument hoperationRegistered
  | assignAdvice
      =>
      trivial
  | assignFixed column row value =>
      exact hfixedColumns column hoperationRegistered
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
    {fixedColumns : List (Column .fixed)}
    (initial : ConstraintSystem F) (counts : ConfigureCounts)
    (hregistered :
      operations.KeygenRegistered delta.gates delta.lookups
        fixedColumns delta.permutationRequests)
    (hfixedColumns : ∀ column ∈ fixedColumns,
      column.index < counts.numFixedColumns) :
    operations.KeygenRegistered
      (delta.apply initial counts).gates
      (delta.apply initial counts).lookups
      (delta.apply initial counts).fixedColumns
      (delta.apply initial counts).permutationColumns := by
  apply hregistered.mono
  · intro gate hgate
    exact List.mem_append_right initial.gates hgate
  · intro argument hargument
    exact List.mem_append_right initial.lookups hargument
  · intro column hcolumn
    rw [ConstraintSystem.mem_fixedColumns_iff]
    exact hfixedColumns column hcolumn
  · intro column hcolumn
    rw [ConfigureDelta.apply, mem_appendFirstEncounters]
    exact Or.inr hcolumn

/-- Existing constraint-system spelling of configure/synthesis registration. -/
@[circuit_norm]
def RegionOperation.KeygenCoherent
    (cs : ConstraintSystem F) : RegionOperation F → Prop :=
  RegionOperation.KeygenRegistered cs.gates cs.lookups cs.fixedColumns
    cs.permutationColumns

/-- Existing constraint-system spelling of configure/synthesis registration. -/
@[circuit_norm]
def Operation.KeygenCoherent
    (cs : ConstraintSystem F) : Operation F → Prop :=
  Operation.KeygenRegistered cs.gates cs.lookups cs.fixedColumns
    cs.permutationColumns

/-- Every synthesis-enabled argument was registered in a constraint system. -/
def OperationsKeygenCoherent
    (cs : ConstraintSystem F) (operations : Operations F) : Prop :=
  operations.KeygenRegistered cs.gates cs.lookups cs.fixedColumns
    cs.permutationColumns

@[circuit_norm]
theorem OperationsKeygenCoherent.nil
    (cs : ConstraintSystem F) :
    OperationsKeygenCoherent cs [] := by
  exact Operations.KeygenRegistered.nil cs.gates cs.lookups cs.fixedColumns
    cs.permutationColumns

/-- Configure/synthesis coherence composes across operation-stream append. -/
@[circuit_norm]
theorem OperationsKeygenCoherent.append
    (cs : ConstraintSystem F) (left right : Operations F) :
    OperationsKeygenCoherent cs (left ++ right) ↔
      OperationsKeygenCoherent cs left ∧
        OperationsKeygenCoherent cs right := by
  exact Operations.KeygenRegistered.append
    left right cs.gates cs.lookups cs.fixedColumns cs.permutationColumns

/-- A region is coherent exactly when each operation in its body is coherent. -/
@[circuit_norm]
theorem OperationsKeygenCoherent.region_cons
    (cs : ConstraintSystem F) (name : String)
    (body : RegionOperations F) (rest : Operations F) :
    OperationsKeygenCoherent cs (.region name body :: rest) ↔
      body.Forall (RegionOperation.KeygenCoherent cs) ∧
        OperationsKeygenCoherent cs rest := by
  exact Operations.KeygenRegistered.region_cons
    name body rest cs.gates cs.lookups cs.fixedColumns cs.permutationColumns

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
    cell column row rest cs.gates cs.lookups cs.fixedColumns cs.permutationColumns

@[circuit_norm]
theorem OperationsKeygenCoherent.loadTable_cons
    (cs : ConstraintSystem F) (table : TableColumn)
    (values : List F) (rest : Operations F) :
    OperationsKeygenCoherent cs (.loadTable table values :: rest) ↔
      table.inner ∈ cs.fixedColumns ∧ OperationsKeygenCoherent cs rest := by
  exact Operations.KeygenRegistered.loadTable_cons
    table values rest cs.gates cs.lookups cs.fixedColumns cs.permutationColumns

/-- Delta registration supplies coherence in every interpreted configure result. -/
theorem Operations.KeygenRegistered.operationsKeygenCoherent_apply
    {operations : Operations F} {delta : ConfigureDelta F}
    {fixedColumns : List (Column .fixed)}
    (initial : ConstraintSystem F) (counts : ConfigureCounts)
    (hregistered :
      operations.KeygenRegistered delta.gates delta.lookups
        fixedColumns delta.permutationRequests)
    (hfixedColumns : ∀ column ∈ fixedColumns,
      column.index < counts.numFixedColumns) :
    OperationsKeygenCoherent (delta.apply initial counts) operations :=
  hregistered.applyConfigureDelta initial counts hfixedColumns

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

/-- A lookup operation, rather than a gate, activates `selector` at `row`. Gate
activations are already ruled out for lookup auxiliary selectors by
`LookupSelectorsLawful`. -/
@[circuit_norm]
def RegionOperation.ActivatesLookupSelectorAt
    (selector row : ℕ) : RegionOperation F → Prop
  | .enableLookup _ enabled operationRow =>
      SelectorEnabledAtIndex enabled selector ∧ operationRow = row
  | _ => False

/-- A lookup operation's local selector valuation agrees with every activation in the
surrounding region at the lookup's row. Non-lookup operations impose no condition. -/
@[circuit_norm]
def RegionOperation.LookupSelectorAssignmentsAgreeWith
    (operations : RegionOperations F) : RegionOperation F → Prop
  | .enableLookup argument enabled row =>
      argument.auxiliarySelectorIndices.Forall fun selector =>
        operations.Forall fun operation =>
          operation.ActivatesLookupSelectorAt selector row →
            SelectorEnabledAtIndex enabled selector
  | _ => True

/-- Every lookup operation agrees with the region-wide selector activations. The
`List.Forall` presentation follows the operation stream compositionally. -/
@[circuit_norm]
def RegionOperations.LookupSelectorAssignmentsAgree
    (operations : RegionOperations F) : Prop :=
  operations.Forall (RegionOperation.LookupSelectorAssignmentsAgreeWith operations)

/-- A local sufficient condition for selector agreement: every lookup activation
enables all of the auxiliary selectors used by its own lookup expression. -/
@[circuit_norm]
def RegionOperation.EnablesLookupAuxiliarySelectors : RegionOperation F → Prop
  | .enableLookup argument enabled _ =>
      argument.auxiliarySelectorIndices.Forall
        (SelectorEnabledAtIndex enabled)
  | _ => True

/-- Whether an operation is not a lookup activation. -/
@[circuit_norm]
def RegionOperation.IsNotLookup : RegionOperation F → Prop
  | .enableLookup _ _ _ => False
  | _ => True

/-- A non-lookup prefix is invisible to every lookup operation's agreement check. -/
@[keygen_norm]
theorem RegionOperation.lookupSelectorAssignmentsAgreeWith_cons_iff
    {leading current : RegionOperation F} {operations : RegionOperations F}
    (hleading : leading.IsNotLookup) :
    current.LookupSelectorAssignmentsAgreeWith (leading :: operations) ↔
      current.LookupSelectorAssignmentsAgreeWith operations := by
  have hnoActivation : ∀ selector row,
      ¬leading.ActivatesLookupSelectorAt selector row := by
    intro selector row
    cases leading <;>
      simp_all [RegionOperation.IsNotLookup,
        RegionOperation.ActivatesLookupSelectorAt]
  cases current <;>
    simp [RegionOperation.LookupSelectorAssignmentsAgreeWith, hnoActivation]

/-- Pointwise agreement for a tail is likewise unchanged by a non-lookup prefix. -/
@[keygen_norm]
theorem RegionOperations.forall_lookupSelectorAssignmentsAgreeWith_cons_iff
    {leading : RegionOperation F} {operations : RegionOperations F}
    (hleading : leading.IsNotLookup) :
    operations.Forall
        (RegionOperation.LookupSelectorAssignmentsAgreeWith (leading :: operations)) ↔
      operations.LookupSelectorAssignmentsAgree := by
  constructor <;> intro hagrees <;>
    apply List.forall_iff_forall_mem.mpr <;>
    intro operation hoperation
  · exact (RegionOperation.lookupSelectorAssignmentsAgreeWith_cons_iff
      hleading).mp (List.forall_iff_forall_mem.mp hagrees operation hoperation)
  · exact (RegionOperation.lookupSelectorAssignmentsAgreeWith_cons_iff
      hleading).mpr (List.forall_iff_forall_mem.mp hagrees operation hoperation)

/-- Prepending a non-lookup operation does not change lookup-selector agreement. -/
@[keygen_norm]
theorem RegionOperations.lookupSelectorAssignmentsAgree_cons_iff
    {operation : RegionOperation F} {operations : RegionOperations F}
    (hoperation : operation.IsNotLookup) :
    RegionOperations.LookupSelectorAssignmentsAgree (operation :: operations) ↔
      operations.LookupSelectorAssignmentsAgree := by
  have hnoActivation : ∀ selector row,
      ¬operation.ActivatesLookupSelectorAt selector row := by
    intro selector row
    cases operation <;>
      simp_all [RegionOperation.IsNotLookup,
        RegionOperation.ActivatesLookupSelectorAt]
  constructor
  · intro hagrees
    apply List.forall_iff_forall_mem.mpr
    intro current hcurrent
    have hcurrentAgreement := List.forall_iff_forall_mem.mp hagrees current
      (by simp [hcurrent])
    cases current with
    | enableLookup argument enabled row =>
        apply List.forall_iff_forall_mem.mpr
        intro selector hselector
        have hselectorAgreement :=
          List.forall_iff_forall_mem.mp hcurrentAgreement selector hselector
        apply List.forall_iff_forall_mem.mpr
        intro other hother
        exact List.forall_iff_forall_mem.mp hselectorAgreement other
          (List.mem_cons_of_mem operation hother)
    | _ => trivial
  · intro hagrees
    rw [RegionOperations.LookupSelectorAssignmentsAgree, List.forall_cons]
    constructor
    · cases operation <;>
        simp_all [RegionOperation.IsNotLookup,
          RegionOperation.LookupSelectorAssignmentsAgreeWith]
    · apply List.forall_iff_forall_mem.mpr
      intro current hcurrent
      have hcurrentAgreement :=
        List.forall_iff_forall_mem.mp hagrees current hcurrent
      cases current with
      | enableLookup argument enabled row =>
          apply List.forall_iff_forall_mem.mpr
          intro selector hselector
          rw [List.forall_cons]
          exact ⟨fun hactivation => False.elim
            (hnoActivation selector row hactivation),
            List.forall_iff_forall_mem.mp hcurrentAgreement selector hselector⟩
      | _ => trivial

/-- A region containing no lookup operations satisfies lookup-selector agreement. -/
theorem RegionOperations.lookupSelectorAssignmentsAgree_of_forall_isNotLookup
    {operations : RegionOperations F}
    (hoperations : operations.Forall RegionOperation.IsNotLookup) :
    operations.LookupSelectorAssignmentsAgree := by
  induction operations with
  | nil => simp [RegionOperations.LookupSelectorAssignmentsAgree]
  | cons operation operations inductionHypothesis =>
      rw [List.forall_cons] at hoperations
      exact (RegionOperations.lookupSelectorAssignmentsAgree_cons_iff
        hoperations.1).mpr (inductionHypothesis hoperations.2)

/-- Enabling every lookup's own auxiliary selectors makes agreement with surrounding
activations immediate. This is useful for uniform-mode lookup loops; circuits that
deliberately leave an auxiliary selector off can prove agreement from row separation. -/
theorem RegionOperations.lookupSelectorAssignmentsAgree_of_enablesLookupAuxiliarySelectors
    {operations : RegionOperations F}
    (henabled : operations.Forall
      RegionOperation.EnablesLookupAuxiliarySelectors) :
    operations.LookupSelectorAssignmentsAgree := by
  apply List.forall_iff_forall_mem.mpr
  intro operation hoperation
  have henabledOperation :=
    List.forall_iff_forall_mem.mp henabled operation hoperation
  cases operation with
  | enableLookup argument enabled row =>
      apply List.forall_iff_forall_mem.mpr
      intro selector hselector
      have hselectorEnabled :=
        List.forall_iff_forall_mem.mp henabledOperation selector hselector
      apply List.forall_iff_forall_mem.mpr
      intro _ _ _
      exact hselectorEnabled
  | _ => trivial

@[keygen_norm, keygen_spine]
theorem RegionOperations.lookupSelectorAssignmentsAgree_nil :
    RegionOperations.LookupSelectorAssignmentsAgree ([] : RegionOperations F) := by
  simp [RegionOperations.LookupSelectorAssignmentsAgree]

/-- Layouter-level lift of lookup-selector assignment agreement. -/
@[circuit_norm]
def Operation.LookupSelectorAssignmentsAgree : Operation F → Prop
  | .region _ body => body.LookupSelectorAssignmentsAgree
  | _ => True

/-- Every synthesized region has lookup-selector assignments consistent with its
operation-local lookup semantics. -/
@[circuit_norm]
def Operations.LookupSelectorAssignmentsAgree
    (operations : Operations F) : Prop :=
  operations.Forall Operation.LookupSelectorAssignmentsAgree

@[keygen_norm, keygen_spine]
theorem Operations.lookupSelectorAssignmentsAgree_nil :
    Operations.LookupSelectorAssignmentsAgree ([] : Operations F) := by
  simp [Operations.LookupSelectorAssignmentsAgree]

@[keygen_norm, keygen_spine]
theorem Operations.lookupSelectorAssignmentsAgree_append
    (left right : Operations F) :
    Operations.LookupSelectorAssignmentsAgree (left ++ right) ↔
      left.LookupSelectorAssignmentsAgree ∧ right.LookupSelectorAssignmentsAgree := by
  simp [Operations.LookupSelectorAssignmentsAgree]

@[keygen_norm, keygen_spine]
theorem Operations.lookupSelectorAssignmentsAgree_region_cons
    (name : String) (body : RegionOperations F) (rest : Operations F) :
    Operations.LookupSelectorAssignmentsAgree (.region name body :: rest) ↔
      body.LookupSelectorAssignmentsAgree ∧ rest.LookupSelectorAssignmentsAgree := by
  simp [Operations.LookupSelectorAssignmentsAgree,
    Operation.LookupSelectorAssignmentsAgree]

@[keygen_norm, keygen_spine]
theorem Operations.lookupSelectorAssignmentsAgree_constrainInstance_cons
    (cell : Cell) (column : Column .instance) (row : ℕ) (rest : Operations F) :
    Operations.LookupSelectorAssignmentsAgree
        (.constrainInstance cell column row :: rest) ↔
      rest.LookupSelectorAssignmentsAgree := by
  simp [Operations.LookupSelectorAssignmentsAgree,
    Operation.LookupSelectorAssignmentsAgree]

@[keygen_norm, keygen_spine]
theorem Operations.lookupSelectorAssignmentsAgree_loadTable_cons
    (column : TableColumn) (values : List F) (rest : Operations F) :
    Operations.LookupSelectorAssignmentsAgree (.loadTable column values :: rest) ↔
      rest.LookupSelectorAssignmentsAgree := by
  simp [Operations.LookupSelectorAssignmentsAgree,
    Operation.LookupSelectorAssignmentsAgree]

/-- Under assignment agreement, an auxiliary selector is enabled by a lookup exactly
when some operation activates it at the same region-local row. -/
theorem RegionOperations.selectorEnabledAtIndex_iff_exists_activatesLookupSelectorAt
    {operations : RegionOperations F}
    (hagrees : operations.LookupSelectorAssignmentsAgree)
    {argument : LookupArgument F} {enabled : List Selector} {row selector : ℕ}
    (hlookup : .enableLookup argument enabled row ∈ operations)
    (hselector : selector ∈ argument.auxiliarySelectorIndices) :
    SelectorEnabledAtIndex enabled selector ↔
      ∃ operation ∈ operations,
        operation.ActivatesLookupSelectorAt selector row := by
  constructor
  · intro henabled
    exact ⟨.enableLookup argument enabled row, hlookup, henabled, rfl⟩
  · rintro ⟨operation, hoperation, hactivation⟩
    have hlookupAgreement :=
      List.forall_iff_forall_mem.mp hagrees _ hlookup
    have hselectorAgreement :=
      List.forall_iff_forall_mem.mp hlookupAgreement _ hselector
    exact List.forall_iff_forall_mem.mp hselectorAgreement
      operation hoperation hactivation

/-- A region registered against no lookup arguments cannot contain a lookup
activation, so lookup-selector assignment agreement is automatic. -/
theorem RegionOperations.lookupSelectorAssignmentsAgree_of_keygenRegistered_noLookups
    {operations : RegionOperations F} {gates : List (Gate F)}
    {fixedColumns : List (Column .fixed)} {permutationColumns : List AnyColumn}
    (hregistered : operations.Forall
      (RegionOperation.KeygenRegistered gates [] fixedColumns permutationColumns)) :
    operations.LookupSelectorAssignmentsAgree := by
  apply List.forall_iff_forall_mem.mpr
  intro operation hoperation
  have hregisteredOperation :=
    List.forall_iff_forall_mem.mp hregistered operation hoperation
  cases operation <;>
    simp_all [RegionOperation.KeygenRegistered,
      RegionOperation.LookupSelectorAssignmentsAgreeWith]

/-- A region whose registered lookup arguments have no auxiliary selectors satisfies
lookup-selector assignment agreement automatically. -/
theorem RegionOperations.lookupSelectorAssignmentsAgree_of_keygenRegistered_auxiliarySelectors_nil
    {operations : RegionOperations F} {gates : List (Gate F)}
    {lookups : List (LookupArgument F)}
    {fixedColumns : List (Column .fixed)} {permutationColumns : List AnyColumn}
    (hregistered : operations.Forall
      (RegionOperation.KeygenRegistered gates lookups fixedColumns permutationColumns))
    (hlookups : lookups.Forall fun argument => argument.auxiliarySelectorIndices = []) :
    operations.LookupSelectorAssignmentsAgree := by
  apply List.forall_iff_forall_mem.mpr
  intro operation hoperation
  have hregisteredOperation :=
    List.forall_iff_forall_mem.mp hregistered operation hoperation
  cases operation with
  | enableLookup argument enabled row =>
      have hnil := List.forall_iff_forall_mem.mp hlookups argument hregisteredOperation
      simp [RegionOperation.LookupSelectorAssignmentsAgreeWith, hnil]
  | _ => trivial

/-- Layouter operations registered against no lookup arguments satisfy lookup-selector
assignment agreement region by region. -/
theorem Operations.lookupSelectorAssignmentsAgree_of_keygenRegistered_noLookups
    {operations : Operations F} {gates : List (Gate F)}
    {fixedColumns : List (Column .fixed)} {permutationColumns : List AnyColumn}
    (hregistered : operations.KeygenRegistered
      gates [] fixedColumns permutationColumns) :
    operations.LookupSelectorAssignmentsAgree := by
  apply List.forall_iff_forall_mem.mpr
  intro operation hoperation
  have hregisteredOperation :=
    List.forall_iff_forall_mem.mp hregistered operation hoperation
  cases operation with
  | region name body =>
      exact RegionOperations.lookupSelectorAssignmentsAgree_of_keygenRegistered_noLookups
        hregisteredOperation
  | constrainInstance | loadTable => trivial

/-- Layouter-level lift of the auxiliary-selector-free registration criterion. -/
theorem Operations.lookupSelectorAssignmentsAgree_of_keygenRegistered_auxiliarySelectors_nil
    {operations : Operations F} {gates : List (Gate F)}
    {lookups : List (LookupArgument F)}
    {fixedColumns : List (Column .fixed)} {permutationColumns : List AnyColumn}
    (hregistered : operations.KeygenRegistered gates lookups fixedColumns permutationColumns)
    (hlookups : lookups.Forall fun argument => argument.auxiliarySelectorIndices = []) :
    operations.LookupSelectorAssignmentsAgree := by
  apply List.forall_iff_forall_mem.mpr
  intro operation hoperation
  have hregisteredOperation :=
    List.forall_iff_forall_mem.mp hregistered operation hoperation
  cases operation with
  | region name body =>
      exact RegionOperations.lookupSelectorAssignmentsAgree_of_keygenRegistered_auxiliarySelectors_nil
        hregisteredOperation hlookups
  | constrainInstance | loadTable => trivial

/-! ## Physical lookup-selector anchoring -/

/-- Every auxiliary selector read by a lookup is physically anchored in the
lookup's region. Unlike selector activation anchoring, this also covers selectors
which that particular lookup deliberately leaves disabled. -/
@[keygen_norm]
def RegionOperations.LookupSelectorsAnchoredBy
    (operations : RegionOperations F)
    (anchor : ℕ → FloorPlanner.RegionColumn) : Prop :=
  ∀ argument enabled row,
    .enableLookup argument enabled row ∈ operations →
      ∀ selector ∈ argument.auxiliarySelectorIndices,
        anchor selector ∈ FloorPlanner.physicalColumns
          (FloorPlanner.regionSynthesisSummary operations).columns

/-- Every lookup region in a layouter operation stream physically anchors the
auxiliary selectors read by its lookup expressions. -/
@[keygen_norm]
def Operations.LookupSelectorsAnchoredBy
    (operations : Operations F)
    (anchor : ℕ → FloorPlanner.RegionColumn) : Prop :=
  operations.Forall fun operation =>
    match operation with
    | .region _ body => body.LookupSelectorsAnchoredBy anchor
    | _ => True

/-- A concrete selector-to-column requirement is satisfied by an anchor map. -/
@[keygen_norm]
def SelectorAnchorRequirementsSatisfied
    (requirements : List (ℕ × FloorPlanner.RegionColumn))
    (anchor : ℕ → FloorPlanner.RegionColumn) : Prop :=
  requirements.Forall fun requirement =>
    anchor requirement.1 = requirement.2

@[keygen_norm]
theorem SelectorAnchorRequirementsSatisfied.append
    (left right : List (ℕ × FloorPlanner.RegionColumn))
    (anchor : ℕ → FloorPlanner.RegionColumn) :
    SelectorAnchorRequirementsSatisfied (left ++ right) anchor ↔
      SelectorAnchorRequirementsSatisfied left anchor ∧
        SelectorAnchorRequirementsSatisfied right anchor := by
  simp [SelectorAnchorRequirementsSatisfied, List.forall_append]

theorem RegionOperations.LookupSelectorsAnchoredBy.of_registered_auxiliarySelectors_nil
    {operations : RegionOperations F}
    {gates : List (Gate F)} {lookups : List (LookupArgument F)}
    {fixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (hregistered : operations.Forall
      (RegionOperation.KeygenRegistered gates lookups fixedColumns
        permutationColumns))
    (hlookups : lookups.Forall fun argument =>
      argument.auxiliarySelectorIndices = [])
    (anchor : ℕ → FloorPlanner.RegionColumn) :
    operations.LookupSelectorsAnchoredBy anchor := by
  intro argument enabled row hoperation selector hselector
  have hregisteredOperation :=
    List.forall_iff_forall_mem.mp hregistered _ hoperation
  have hnil := List.forall_iff_forall_mem.mp hlookups
    argument hregisteredOperation
  rw [hnil] at hselector
  exact (List.not_mem_nil hselector).elim

/-- A region registered against no lookups has no selector reads to anchor. -/
theorem RegionOperations.LookupSelectorsAnchoredBy.of_registered_noLookups
    {operations : RegionOperations F}
    {gates : List (Gate F)} {fixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (hregistered : operations.Forall
      (RegionOperation.KeygenRegistered gates [] fixedColumns
        permutationColumns))
    (anchor : ℕ → FloorPlanner.RegionColumn) :
    operations.LookupSelectorsAnchoredBy anchor := by
  intro argument enabled row hoperation
  have hregisteredOperation :=
    List.forall_iff_forall_mem.mp hregistered _ hoperation
  exact (List.not_mem_nil hregisteredOperation).elim

/-- A region containing no lookup activations has no lookup-selector reads to
anchor, independently of its configured lookup capabilities. -/
theorem RegionOperations.LookupSelectorsAnchoredBy.of_forall_isNotLookup
    {operations : RegionOperations F}
    (hoperations : operations.Forall RegionOperation.IsNotLookup)
    (anchor : ℕ → FloorPlanner.RegionColumn) :
    operations.LookupSelectorsAnchoredBy anchor := by
  intro argument enabled row hoperation
  have hnotLookup := List.forall_iff_forall_mem.mp hoperations _ hoperation
  simp [RegionOperation.IsNotLookup] at hnotLookup

/-- Physical lookup-selector anchoring is preserved when two operation fragments
share a region: either fragment's physical footprint is included in the combined
footprint. -/
theorem RegionOperations.LookupSelectorsAnchoredBy.append
    {left right : RegionOperations F}
    {anchor : ℕ → FloorPlanner.RegionColumn}
    (hleft : left.LookupSelectorsAnchoredBy anchor)
    (hright : right.LookupSelectorsAnchoredBy anchor) :
    (left ++ right).LookupSelectorsAnchoredBy anchor := by
  intro argument enabled row hlookup selector hselector
  rw [List.mem_append] at hlookup
  have liftPhysical
      (source other : RegionOperations F)
      (hsource : anchor selector ∈
        FloorPlanner.physicalColumns
          (FloorPlanner.regionSynthesisSummary source).columns) :
      anchor selector ∈ FloorPlanner.physicalColumns
        (FloorPlanner.regionSynthesisSummary (source ++ other)).columns := by
    rw [FloorPlanner.physicalColumns, List.mem_filter] at hsource ⊢
    constructor
    · rw [FloorPlanner.regionSynthesisSummary_append,
        FloorPlanner.RegionSynthesisSummary.combine_columns,
        FloorPlanner.mem_unionColumns_iff]
      exact .inl hsource.1
    · exact hsource.2
  rcases hlookup with hlookup | hlookup
  · exact liftPhysical left right
      (hleft argument enabled row hlookup selector hselector)
  · rw [FloorPlanner.regionSynthesisSummary_append]
    rw [FloorPlanner.physicalColumns, List.mem_filter]
    have hsource := hright argument enabled row hlookup selector hselector
    rw [FloorPlanner.physicalColumns, List.mem_filter] at hsource
    constructor
    · rw [FloorPlanner.RegionSynthesisSummary.combine_columns,
        FloorPlanner.mem_unionColumns_iff]
      exact .inr hsource.1
    · exact hsource.2

theorem Operations.LookupSelectorsAnchoredBy.of_registered_auxiliarySelectors_nil
    {operations : Operations F}
    {gates : List (Gate F)} {lookups : List (LookupArgument F)}
    {fixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (hregistered : operations.KeygenRegistered
      gates lookups fixedColumns permutationColumns)
    (hlookups : lookups.Forall fun argument =>
      argument.auxiliarySelectorIndices = [])
    (anchor : ℕ → FloorPlanner.RegionColumn) :
    operations.LookupSelectorsAnchoredBy anchor := by
  rw [Operations.LookupSelectorsAnchoredBy, List.forall_iff_forall_mem]
  intro operation hoperation
  have hregisteredOperation :=
    List.forall_iff_forall_mem.mp hregistered operation hoperation
  cases operation with
  | region name body =>
      exact RegionOperations.LookupSelectorsAnchoredBy.of_registered_auxiliarySelectors_nil
        hregisteredOperation hlookups anchor
  | constrainInstance | loadTable => trivial

/-- Layouter operations registered against no lookups have no selector reads to
anchor. -/
theorem Operations.LookupSelectorsAnchoredBy.of_registered_noLookups
    {operations : Operations F}
    {gates : List (Gate F)} {fixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (hregistered : operations.KeygenRegistered gates [] fixedColumns
      permutationColumns)
    (anchor : ℕ → FloorPlanner.RegionColumn) :
    operations.LookupSelectorsAnchoredBy anchor := by
  rw [Operations.LookupSelectorsAnchoredBy, List.forall_iff_forall_mem]
  intro operation hoperation
  have hregisteredOperation :=
    List.forall_iff_forall_mem.mp hregistered operation hoperation
  cases operation with
  | region name body =>
      exact RegionOperations.LookupSelectorsAnchoredBy.of_registered_noLookups
        hregisteredOperation anchor
  | constrainInstance | loadTable => trivial

theorem Operations.LookupSelectorsAnchoredBy.nil
    (anchor : ℕ → FloorPlanner.RegionColumn) :
    Operations.LookupSelectorsAnchoredBy ([] : Operations F) anchor := by
  simp [Operations.LookupSelectorsAnchoredBy]

@[keygen_norm, keygen_spine]
theorem Operations.lookupSelectorsAnchoredBy_append_iff
    (left right : Operations F) (anchor : ℕ → FloorPlanner.RegionColumn) :
    (left ++ right).LookupSelectorsAnchoredBy anchor ↔
      left.LookupSelectorsAnchoredBy anchor ∧
        right.LookupSelectorsAnchoredBy anchor := by
  simp [Operations.LookupSelectorsAnchoredBy, List.forall_append]

@[keygen_norm, keygen_spine]
theorem Operations.lookupSelectorsAnchoredBy_region_cons_iff
    (name : String) (body : RegionOperations F) (rest : Operations F)
    (anchor : ℕ → FloorPlanner.RegionColumn) :
    Operations.LookupSelectorsAnchoredBy ((.region name body) :: rest) anchor ↔
      body.LookupSelectorsAnchoredBy anchor ∧
        rest.LookupSelectorsAnchoredBy anchor := by
  simp [Operations.LookupSelectorsAnchoredBy]

@[keygen_norm, keygen_spine]
theorem Operations.lookupSelectorsAnchoredBy_constrainInstance_cons_iff
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (rest : Operations F) (anchor : ℕ → FloorPlanner.RegionColumn) :
    Operations.LookupSelectorsAnchoredBy
        ((.constrainInstance cell column row) :: rest) anchor ↔
      rest.LookupSelectorsAnchoredBy anchor := by
  simp [Operations.LookupSelectorsAnchoredBy]

@[keygen_norm, keygen_spine]
theorem Operations.lookupSelectorsAnchoredBy_loadTable_cons_iff
    (column : TableColumn) (values : List F) (rest : Operations F)
    (anchor : ℕ → FloorPlanner.RegionColumn) :
    Operations.LookupSelectorsAnchoredBy
        ((.loadTable column values) :: rest) anchor ↔
      rest.LookupSelectorsAnchoredBy anchor := by
  simp [Operations.LookupSelectorsAnchoredBy]

theorem Operations.LookupSelectorsAnchoredBy.append
    {left right : Operations F}
    {anchor : ℕ → FloorPlanner.RegionColumn}
    (hleft : left.LookupSelectorsAnchoredBy anchor)
    (hright : right.LookupSelectorsAnchoredBy anchor) :
    (left ++ right).LookupSelectorsAnchoredBy anchor := by
  simpa [Operations.LookupSelectorsAnchoredBy, List.forall_append] using
    And.intro hleft hright

theorem Operations.LookupSelectorsAnchoredBy.region_cons
    {name : String} {body : RegionOperations F} {rest : Operations F}
    {anchor : ℕ → FloorPlanner.RegionColumn}
    (hbody : body.LookupSelectorsAnchoredBy anchor)
    (hrest : rest.LookupSelectorsAnchoredBy anchor) :
    Operations.LookupSelectorsAnchoredBy
      ((.region name body : Operation F) :: rest) anchor := by
  simpa [Operations.LookupSelectorsAnchoredBy] using And.intro hbody hrest

theorem Operations.LookupSelectorsAnchoredBy.constrainInstance_cons
    {cell : Cell} {column : Column .instance} {row : ℕ}
    {rest : Operations F} {anchor : ℕ → FloorPlanner.RegionColumn}
    (hrest : rest.LookupSelectorsAnchoredBy anchor) :
    Operations.LookupSelectorsAnchoredBy
      ((.constrainInstance cell column row : Operation F) :: rest) anchor := by
  simpa [Operations.LookupSelectorsAnchoredBy] using hrest

theorem Operations.LookupSelectorsAnchoredBy.loadTable_cons
    {column : TableColumn} {values : List F}
    {rest : Operations F} {anchor : ℕ → FloorPlanner.RegionColumn}
    (hrest : rest.LookupSelectorsAnchoredBy anchor) :
    Operations.LookupSelectorsAnchoredBy
      ((.loadTable column values : Operation F) :: rest) anchor := by
  simpa [Operations.LookupSelectorsAnchoredBy] using hrest

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

/-- Lookup-activation well-formedness composes over sequential operation fragments. -/
theorem Operations.LookupActivationsWellFormed.append
    {left right : Operations F}
    (hleft : left.LookupActivationsWellFormed)
    (hright : right.LookupActivationsWellFormed) :
    (left ++ right).LookupActivationsWellFormed :=
  List.forall_append.mpr ⟨hleft, hright⟩

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
    {fixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (hregistered : operation.KeygenRegistered
      gates lookups fixedColumns permutationColumns)
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
    {fixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (hregistered : operations.Forall
      (RegionOperation.KeygenRegistered gates lookups fixedColumns
        permutationColumns))
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
    {fixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (hregistered : operation.KeygenRegistered
      gates lookups fixedColumns permutationColumns)
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
    {fixedColumns : List (Column .fixed)}
    {permutationColumns : List AnyColumn}
    (hregistered : operations.KeygenRegistered
      gates lookups fixedColumns permutationColumns)
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

theorem Operations.assignedCellsFrom_append
    (left right : Operations F) (region : RegionIndex) :
    (left ++ right).assignedCellsFrom region =
      left.assignedCellsFrom region ++
        right.assignedCellsFrom (region + left.regionCount) := by
  induction left generalizing region with
  | nil => simp only [List.nil_append, assignedCellsFrom, regionCount, Nat.add_zero,
      List.nil_append]
  | cons operation rest ih =>
      cases operation <;>
        simp only [List.cons_append, assignedCellsFrom, regionCount, ih,
          List.append_assoc, Nat.add_assoc]

theorem Operations.mem_assignedCellsFrom_append_left
    {left right : Operations F} {region : RegionIndex} {cell : Cell}
    (hcell : cell ∈ left.assignedCellsFrom region) :
    cell ∈ (left ++ right).assignedCellsFrom region := by
  rw [Operations.assignedCellsFrom_append]
  exact List.mem_append_left _ hcell

theorem Operations.mem_assignedCellsFrom_append_right
    {left right : Operations F} {region : RegionIndex} {cell : Cell}
    (hcell : cell ∈ right.assignedCellsFrom (region + left.regionCount)) :
    cell ∈ (left ++ right).assignedCellsFrom region := by
  rw [Operations.assignedCellsFrom_append]
  exact List.mem_append_right _ hcell

/-- Copy provenance composes across appended layouter streams. The second stream may
use every caller cell and every cell assigned by the first stream. -/
theorem Operations.CopyCellsAssignedFrom.append
    {left right : Operations F} {region : RegionIndex} {available : List Cell}
    (hleft : left.CopyCellsAssignedFrom region available)
    (hright : right.CopyCellsAssignedFrom (region + left.regionCount)
      (available ++ left.assignedCellsFrom region)) :
    (left ++ right).CopyCellsAssignedFrom region available := by
  induction hleft with
  | nil => simpa [Operations.regionCount, Operations.assignedCellsFrom] using hright
  | region current available name body rest hbody hrest ih =>
      rw [List.cons_append, Operations.copyCellsAssignedFrom_region_iff]
      refine ⟨hbody, ih ?_⟩
      have h := hright.mono (larger :=
          body.assignedCellsAfter current available ++
            rest.assignedCellsFrom (current + 1)) (by
        intro cell hcell
        simp only [Operations.assignedCellsFrom, List.mem_append] at hcell ⊢
        rcases hcell with hcell | hcell
        · left
          rw [RegionOperations.mem_assignedCellsAfter_iff, List.mem_append]
          exact Or.inl hcell
        · rcases hcell with hbodyCell | hrestCell
          · left
            rw [RegionOperations.mem_assignedCellsAfter_iff, List.mem_append]
            exact Or.inr hbodyCell
          · exact Or.inr hrestCell)
      simpa only [Operations.regionCount, Nat.add_assoc] using h
  | constrainInstance current available cell column row rest hcell hrest ih =>
      rw [List.cons_append, Operations.copyCellsAssignedFrom_constrainInstance_iff]
      refine ⟨hcell, ih ?_⟩
      simpa [Operations.regionCount, Operations.assignedCellsFrom] using hright
  | loadTable current available column values rest hrest ih =>
      rw [List.cons_append, Operations.copyCellsAssignedFrom_loadTable_iff]
      apply ih
      simpa [Operations.regionCount, Operations.assignedCellsFrom] using hright

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
