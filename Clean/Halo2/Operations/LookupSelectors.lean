import Clean.Halo2.Operations.Keygen

namespace Halo2

variable {F : Type}

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

end Halo2
