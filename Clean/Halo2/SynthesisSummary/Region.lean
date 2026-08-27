import Clean.Halo2.Operations

namespace Halo2

variable {F : Type}

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

theorem mem_repeatedSelectorActivations_iff
    (sourceSelector row selector offset stride count : ℕ) :
    (sourceSelector, row) ∈
        repeatedSelectorActivations selector offset stride count ↔
      sourceSelector = selector ∧
        ∃ index < count, row = offset + stride * index := by
  induction count with
  | zero => simp [repeatedSelectorActivations]
  | succ count inductionHypothesis =>
      simp only [repeatedSelectorActivations, List.mem_append,
        inductionHypothesis, List.mem_singleton, Prod.mk.injEq]
      constructor
      · rintro (⟨hselector, index, hindex, hrow⟩ | ⟨hselector, hrow⟩)
        · exact ⟨hselector, index, Nat.lt_succ_of_lt hindex, hrow⟩
        · exact ⟨hselector, count, Nat.lt_succ_self count, hrow⟩
      · rintro ⟨hselector, index, hindex, hrow⟩
        by_cases hlast : index = count
        · exact Or.inr ⟨hselector, by simpa only [hlast] using hrow⟩
        · exact Or.inl ⟨hselector, index, Nat.lt_of_le_of_ne
            (Nat.le_of_lt_succ hindex) hlast, hrow⟩

/-- Compact selector rows for a repeated fixed pattern. Each pair contains a selector
index and its row offset within one repetition. -/
def repeatedSelectorPattern (pattern : List (ℕ × ℕ)) (offset stride : ℕ) :
    ℕ → List (ℕ × ℕ)
  | 0 => []
  | count + 1 =>
      repeatedSelectorPattern pattern offset stride count ++
        pattern.map fun (selector, row) =>
          (selector, offset + stride * count + row)

theorem mem_repeatedSelectorPattern_iff
    (activation : ℕ × ℕ) (pattern : List (ℕ × ℕ))
    (offset stride count : ℕ) :
    activation ∈ repeatedSelectorPattern pattern offset stride count ↔
      ∃ index < count, ∃ source ∈ pattern,
        activation = (source.1, offset + stride * index + source.2) := by
  induction count with
  | zero => simp [repeatedSelectorPattern]
  | succ count inductionHypothesis =>
      simp only [repeatedSelectorPattern, List.mem_append,
        inductionHypothesis, List.mem_map]
      constructor
      · rintro (⟨index, hindex, source, hsource, hactivation⟩ |
          ⟨source, hsource, hactivation⟩)
        · exact ⟨index, Nat.lt_succ_of_lt hindex, source, hsource,
            hactivation⟩
        · exact ⟨count, Nat.lt_succ_self count, source, hsource,
            hactivation.symm⟩
      · rintro ⟨index, hindex, source, hsource, hactivation⟩
        by_cases hlast : index = count
        · exact Or.inr ⟨source, hsource, by simpa only [hlast] using
            hactivation.symm⟩
        · exact Or.inl ⟨index, Nat.lt_of_le_of_ne
            (Nat.le_of_lt_succ hindex) hlast, source, hsource, hactivation⟩

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

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelectorAt_selectorActivations
    (selector selectorOffset : ℕ) (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelectorAt selector selectorOffset columns offset stride
      rowCount constantSiteCount count instanceRowExtent
      lookupActivationCount).selectorActivations =
        repeatedSelectorActivations selector selectorOffset stride count := rfl

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

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumnsWithSelector_selectorActivations (selector : ℕ)
    (columns : List RegionColumn) (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumnsWithSelector selector columns offset stride rowCount
      constantSiteCount count instanceRowExtent
      lookupActivationCount).selectorActivations =
        repeatedSelectorActivations selector offset stride count := rfl

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

@[circuit_norm, synthesis_summary_norm]
theorem repeatColumns_selectorActivations (columns : List RegionColumn)
    (offset stride rowCount constantSiteCount count : ℕ)
    (instanceRowExtent : ℕ := 0) (lookupActivationCount : ℕ := 0) :
    (repeatColumns columns offset stride rowCount constantSiteCount count
      instanceRowExtent lookupActivationCount).selectorActivations = [] := by
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

end FloorPlanner
end Halo2
