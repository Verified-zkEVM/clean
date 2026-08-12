import Clean.Halo2.Keygen.Projection
import Clean.Halo2.Keygen.FloorPlanner
import Clean.Halo2.Formal

/-!
# `PinnedConstraintSystem` — the pinned constraint system, derived from a circuit

halo2's `PinnedConstraintSystem` is the canonical view of the constraint system a
verifying key pins (and hashes into `transcript_repr`): counts, flattened gate
polynomials, query lists, permutation columns, lookups, constants. The Lean record
mirrors every field of the Rust pinned record (`circuit.rs:966-979`).

`PinnedConstraintSystem.derive` computes it from a Clean `ConstraintSystem` and the
`compress_selectors` packing `map`. The query-registration order needs no input: Clean's
configure-time query registration records it in `cs.{advice,fixed,instance}Queries`, and the
packed columns' fixed queries are appended by the projection (`queryWalkInit`).

`PinnedConstraintSystem.derive` closes the loop — the
circuit-side half of halo2's `keygen_vk`: floor plan → activations → minimal fitting
domain → compress_selectors → pinned record.
-/

namespace Halo2

variable {F : Type}

/-- Every selector in a configured lookup input lies below the allocated count. -/
def ConstraintSystem.LookupSelectorsAllocated
    (cs : ConstraintSystem F) : Prop :=
  lookupInputSelectorBound cs.lookups ≤ cs.numSelectors

/-- Allocating the configured lookup selectors bounds every lookup-input expression. -/
theorem ConstraintSystem.LookupSelectorsAllocated.lookupInputsAllocated
    {cs : ConstraintSystem F} (hallocated : cs.LookupSelectorsAllocated) :
    ∀ argument ∈ cs.lookups, ∀ expression ∈ argument.inputs,
      expression.selectorBound ≤ cs.numSelectors := by
  intro argument hargument expression hexpression
  exact le_trans
    (Expression.selectorBound_le_lookupInputSelectorBound
      hargument hexpression)
    hallocated

/-! ## Constraint-system derived scalars

halo2 quantities that are pure functions of the `ConstraintSystem` — computable since
the configure-time query registration records `adviceQueries`. -/

/-- halo2 `ConstraintSystem::blinding_factors` (`circuit.rs:1652-1675`):
`max(3, max per-column advice-query count) + 1 + 1`. The per-column counts are Rust's
`num_advice_queries`, recovered by counting the recorded `adviceQueries`. -/
def ConstraintSystem.blindingFactors (cs : ConstraintSystem F) : ℕ :=
  let factors := (List.range cs.numAdviceColumns).foldl
    (fun m c => max m (cs.adviceQueries.countP (fun q => q.1.index = c))) 1
  max 3 factors + 1 + 1

/-- halo2 `ConstraintSystem::minimum_rows` (`circuit.rs:1678-1689`):
blinding factors + l_last + l_0 breathing room + one row. -/
def ConstraintSystem.minimumRows (cs : ConstraintSystem F) : ℕ :=
  cs.blindingFactors + 3

/-- The permutation argument's chunk length, `cs.degree() - 2`
(`permutation/verifier.rs:43`). -/
def ConstraintSystem.chunkLen (cs : ConstraintSystem F) : ℕ :=
  csDegree cs - 2

/-- The Lean mirror of halo2's `PinnedConstraintSystem` (`circuit.rs:966-979`): column
counts, gate polynomials, query layouts, the permutation argument's columns, lookup
argument expressions, constants columns, and the minimum-degree override — every field
of the Rust pinned record. -/
structure PinnedConstraintSystem (F : Type) where
  numFixedColumns : ℕ
  numAdviceColumns : ℕ
  numInstanceColumns : ℕ
  numSelectors : ℕ
  gates : List (RichExpression F)
  adviceQueryLayout : List (ℕ × ℤ)
  fixedQueryLayout : List (ℕ × ℤ)
  instanceQueryLayout : List (ℕ × ℤ)
  /-- The permutation argument's columns (`permutation::Argument`), in `enable_equality`
  call order — recorded in `cs.permutationColumns`. -/
  permutationColumns : List AnyColumn
  lookupInputExprs : List (List (RichExpression F))
  lookupTableExprs : List (List (RichExpression F))
  constants : List ℕ
  minimumDegree : Option ℕ
deriving DecidableEq, Repr

/-- Derive the pinned CS data from a Clean constraint system and the (circuit-derived)
selector-compression map; the query layouts come from the CS's configure-recorded
queries (see the module docstring). -/
def PinnedConstraintSystem.derive [Field F] [DecidableEq F] (cs : ConstraintSystem F)
    (map : SelCompressMap) : PinnedConstraintSystem F :=
  -- single let: the projection (selector substitution + query walk) runs once per
  -- `derive` evaluation, not once per field
  let proj := projectCS map cs
  { numFixedColumns := proj.numFixedColumns
    numAdviceColumns := proj.numAdviceColumns
    numInstanceColumns := proj.numInstanceColumns
    numSelectors := proj.numSelectors
    gates := proj.gates
    adviceQueryLayout := proj.adviceQueryLayout
    fixedQueryLayout := proj.fixedQueryLayout
    instanceQueryLayout := proj.instanceQueryLayout
    permutationColumns := cs.permutationColumns
    lookupInputExprs := proj.lookups.map (·.inputs)
    lookupTableExprs := proj.lookups.map (·.tables)
    -- Clean's constraint system does not model `set_minimum_degree`; Orchard never calls it.
    constants := cs.constants.map (·.index)
    minimumDegree := none }

/-- Lookup inputs in the pinned constraint system are the selector-substituted source
inputs erased against the authoritative configure-derived query layout. -/
theorem PinnedConstraintSystem.derive_lookupInputExprs_getD
    [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap)
    (index : ℕ) (hindex : index < cs.lookups.length) :
    (PinnedConstraintSystem.derive cs map).lookupInputExprs.getD index [] =
      eraseGates
        (cs.lookups[index].inputs.map (substSelectorMap map.lookup))
        (queryWalkInit map cs) := by
  simp [PinnedConstraintSystem.derive, projectCS, eraseLookups, eraseLookup,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hindex]

/-- Lookup tables in the pinned constraint system are the selector-substituted source
tables erased against the authoritative configure-derived query layout. -/
theorem PinnedConstraintSystem.derive_lookupTableExprs_getD
    [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap)
    (index : ℕ) (hindex : index < cs.lookups.length) :
    (PinnedConstraintSystem.derive cs map).lookupTableExprs.getD index [] =
      eraseGates
        (cs.lookups[index].tables.map (substSelectorMap map.lookup))
        (queryWalkInit map cs) := by
  simp [PinnedConstraintSystem.derive, projectCS, eraseLookups, eraseLookup,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hindex]

/-! ## The domain exponent `k`, derived

Rust does not compute `k` — orchard pins `const K: u32 = 11` and keygen *asserts* the
circuit fits: every assignment row must lie in `usable_rows = 0..n − (blinding_factors + 1)`
and `n ≥ cs.minimum_rows()` (`keygen.rs:200`). The minimal `k` satisfying those asserts is
the faithful derived value. -/

/-- One past the absolute row of a placed cell. -/
def Cell.rowExtent (starts : List ℕ) (cell : Cell) : ℕ :=
  starts.getD cell.regionIndex 0 + cell.rowOffset + 1

/-- One past every copy endpoint used by a region operation. -/
def RegionOperation.copyRowExtent
    (starts : List ℕ) : RegionOperation F → ℕ
  | .constrainEqual left right =>
      max (left.rowExtent starts) (right.rowExtent starts)
  | .constrainConstant cell _ =>
      cell.rowExtent starts
  | .constrainInstance cell _ row =>
      max (cell.rowExtent starts) (row + 1)
  | _ => 0

/-- One past every copy endpoint used by a layouter operation. -/
def Operation.copyRowExtent
    (starts : List ℕ) : Operation F → ℕ
  | .region _ body =>
      (body.map (RegionOperation.copyRowExtent starts)).foldl max 0
  | .constrainInstance cell _ row =>
      max (cell.rowExtent starts) (row + 1)
  | .loadTable _ _ => 0

/--
One past every row checked while loading a table. A nonempty table assigns its explicit
prefix and then calls `fill_from_row` at `values.length`; Halo 2 checks that boundary
itself against `usable_rows`.
-/
def Operation.tableRowExtent : Operation F → ℕ
  | .loadTable _ [] => 0
  | .loadTable _ values => values.length + 1
  | _ => 0

/-- One past every absolute instance row named by an operation. -/
def Operation.instanceRowExtent : Operation F → ℕ
  | .region _ body =>
      (body.map FloorPlanner.regionOperationInstanceRowExtent).foldl max 0
  | .constrainInstance _ _ row => row + 1
  | .loadTable _ _ => 0

private theorem foldl_max_eq_max_foldl_max_zero
    (values : List ℕ) (initial : ℕ) :
    values.foldl max initial = max initial (values.foldl max 0) := by
  induction values generalizing initial with
  | nil => simp
  | cons value rest inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis (max initial value),
        List.foldl_cons]
      simp only [Nat.zero_max]
      rw [inductionHypothesis value]
      ac_rfl

/-- The exact table endpoint is part of the reduced synthesis summary. -/
theorem synthesisSummary_tableRowExtent_eq
    (operations : Operations F) :
    (FloorPlanner.synthesisSummary operations).tableRowExtent =
      (operations.map Operation.tableRowExtent).foldl max 0 := by
  induction operations with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      cases operation <;>
        simp only [FloorPlanner.synthesisSummary,
          FloorPlanner.SynthesisSummary.combine_tableRowExtent,
          FloorPlanner.SynthesisSummary.ofRegion_tableRowExtent,
          FloorPlanner.SynthesisSummary.ofInstanceRow_tableRowExtent,
          FloorPlanner.SynthesisSummary.ofTableValues,
          Operation.tableRowExtent, List.map_cons, List.foldl_cons,
          inductionHypothesis, Nat.zero_max]
      split <;> simp_all [← foldl_max_eq_max_foldl_max_zero]

/-- The exact absolute-instance endpoint is part of the reduced synthesis summary. -/
theorem synthesisSummary_instanceRowExtent_eq
    (operations : Operations F) :
    (FloorPlanner.synthesisSummary operations).instanceRowExtent =
      (operations.map Operation.instanceRowExtent).foldl max 0 := by
  have regionSummary : ∀ (body : RegionOperations F),
      (FloorPlanner.regionSynthesisSummary body).instanceRowExtent =
        (body.map FloorPlanner.regionOperationInstanceRowExtent).foldl max 0 := by
    intro body
    induction body with
    | nil => rfl
    | cons operation rest inductionHypothesis =>
        simp only [FloorPlanner.regionSynthesisSummary,
          FloorPlanner.RegionSynthesisSummary.combine_instanceRowExtent,
          FloorPlanner.RegionSynthesisSummary.ofOperation_instanceRowExtent,
          List.map_cons, List.foldl_cons, inductionHypothesis]
        exact (foldl_max_eq_max_foldl_max_zero
          (rest.map FloorPlanner.regionOperationInstanceRowExtent)
          (FloorPlanner.regionOperationInstanceRowExtent operation)).symm
  induction operations with
  | nil => rfl
  | cons operation rest inductionHypothesis =>
      cases operation <;>
        simp only [FloorPlanner.synthesisSummary,
          FloorPlanner.SynthesisSummary.combine_instanceRowExtent,
          FloorPlanner.SynthesisSummary.ofRegion_instanceRowExtent,
          FloorPlanner.SynthesisSummary.ofInstanceRow_instanceRowExtent,
          FloorPlanner.SynthesisSummary.ofTableValues_instanceRowExtent,
          Operation.instanceRowExtent, List.map_cons, List.foldl_cons,
          inductionHypothesis, regionSummary, Nat.zero_max]
      all_goals exact (foldl_max_eq_max_foldl_max_zero
        (rest.map Operation.instanceRowExtent) _).symm

/--
The rows guarded by Halo 2's `usable_rows` checks during key generation or proving:
floor-planned assignments and selector activations, loaded-table assignments and fill
boundary, and both endpoints of every copy.

In particular, an absolute `constrainInstance` row contributes even though the copy
consumes no region-local space.
-/
def usedRows (ops : Operations F) : ℕ :=
  let starts := FloorPlanner.V1.starts ops
  let regionEnd := FloorPlanner.V1.placementEnd ops
  let tableEnd :=
    (ops.map Operation.tableRowExtent).foldl max 0
  let copyEnd :=
    (ops.map (Operation.copyRowExtent starts)).foldl max 0
  max (max regionEnd tableEnd) copyEnd

/-- Membership in the assignment summary identifies a measured local row. -/
theorem RegionOperations.rowOffset_succ_le_regionSynthesisSummary_of_mem_assignedCells
    (body : RegionOperations F) (region : RegionIndex) (cell : Cell)
    (hcell : cell ∈ body.assignedCells region) :
    cell.regionIndex = region ∧
      cell.rowOffset + 1 ≤ (FloorPlanner.regionSynthesisSummary body).rowCount := by
  rw [RegionOperations.assignedCells, List.mem_flatMap] at hcell
  obtain ⟨operation, hoperation, hcell⟩ := hcell
  cases operation with
  | assignAdvice column row compute =>
      simp only [RegionOperation.assignedCells, List.mem_singleton] at hcell
      subst cell
      exact ⟨Cell.of_regionIndex region row column, by
        simpa only [Cell.of_rowOffset] using
          FloorPlanner.regionOperationRowExtent_le_synthesisSummary_of_mem
            body (.assignAdvice column row compute) hoperation⟩
  | assignFixed column row value =>
      simp only [RegionOperation.assignedCells, List.mem_singleton] at hcell
      subst cell
      exact ⟨Cell.of_regionIndex region row column, by
        simpa only [Cell.of_rowOffset] using
          FloorPlanner.regionOperationRowExtent_le_synthesisSummary_of_mem
            body (.assignFixed column row value) hoperation⟩
  | enableGate gate row =>
      simp only [RegionOperation.assignedCells, List.not_mem_nil] at hcell
  | enableLookup argument selectors row =>
      simp only [RegionOperation.assignedCells, List.not_mem_nil] at hcell
  | constrainEqual left right =>
      simp only [RegionOperation.assignedCells, List.not_mem_nil] at hcell
  | constrainConstant assigned value =>
      simp only [RegionOperation.assignedCells, List.not_mem_nil] at hcell
  | constrainInstance assigned column row =>
      simp only [RegionOperation.assignedCells, List.not_mem_nil] at hcell

/-- The assignment summary uses precisely the same region-index walk as V1. -/
theorem Operations.indexedRegion_of_mem_assignedCellsFrom
    (operations : Operations F) (initial : RegionIndex) (cell : Cell)
    (hcell : cell ∈ operations.assignedCellsFrom initial) :
    ∃ region body,
      (region, body) ∈ (indexedRegions operations initial).1 ∧
        cell ∈ body.assignedCells region := by
  induction operations generalizing initial with
  | nil => simp [Operations.assignedCellsFrom] at hcell
  | cons operation rest inductionHypothesis =>
      cases operation with
      | region name body =>
          rw [Operations.assignedCellsFrom, List.mem_append] at hcell
          rcases hcell with hbody | hrest
          · exact ⟨initial, body, by simp [indexedRegions], hbody⟩
          · obtain ⟨region, assignedBody, hregion, hassigned⟩ :=
              inductionHypothesis (initial + 1) hrest
            exact ⟨region, assignedBody, by simp [indexedRegions, hregion], hassigned⟩
      | constrainInstance cell column row =>
          exact inductionHypothesis initial hcell
      | loadTable column values =>
          exact inductionHypothesis initial hcell

/-- Every cell recorded as assigned by synthesis lies within V1's placed regions. -/
theorem Operations.assignedCell_rowExtent_le_placementEnd
    (operations : Operations F) (cell : Cell)
    (hcell : cell ∈ operations.assignedCells) :
    cell.rowExtent (FloorPlanner.V1.starts operations) ≤
      FloorPlanner.V1.placementEnd operations := by
  obtain ⟨region, body, hregion, hassigned⟩ :=
    Operations.indexedRegion_of_mem_assignedCellsFrom operations 0 cell hcell
  obtain ⟨hcellRegion, hrow⟩ :=
    RegionOperations.rowOffset_succ_le_regionSynthesisSummary_of_mem_assignedCells
      body region cell hassigned
  have hshape : FloorPlanner.measureRegion region body ∈
      FloorPlanner.measureRegions operations := by
    exact List.mem_map.mpr ⟨(region, body), hregion, rfl⟩
  rw [FloorPlanner.V1.placementEnd]
  rw [Cell.rowExtent, hcellRegion, Nat.add_assoc]
  exact (Nat.add_le_add_left hrow
    ((FloorPlanner.V1.starts operations).getD region 0)).trans (by
      simpa only [FloorPlanner.measureRegion_rowCount] using
        FloorPlanner.V1.shape_end_le_placementEndFrom_of_mem
          (FloorPlanner.measureRegions operations)
          (FloorPlanner.V1.starts operations)
          (FloorPlanner.measureRegion region body) hshape)

private theorem foldl_max_le
    (values : List ℕ) (bound : ℕ)
    (hvalues : ∀ value ∈ values, value ≤ bound) :
    values.foldl max 0 ≤ bound := by
  induction values with
  | nil => exact Nat.zero_le bound
  | cons value rest inductionHypothesis =>
      rw [List.foldl_cons, foldl_max_eq_max_foldl_max_zero]
      exact Nat.max_le.mpr ⟨hvalues value (by simp),
        inductionHypothesis (by
          intro candidate hcandidate
          exact hvalues candidate (by simp [hcandidate]))⟩

/-- Every operation's absolute-instance endpoint is covered by the exact reduced
synthesis summary. -/
theorem Operation.instanceRowExtent_le_synthesisSummary_of_mem
    (operations : Operations F) (operation : Operation F)
    (hoperation : operation ∈ operations) :
    operation.instanceRowExtent ≤
      (FloorPlanner.synthesisSummary operations).instanceRowExtent := by
  rw [synthesisSummary_instanceRowExtent_eq]
  exact FloorPlanner.value_le_foldl_max_of_mem
    (operations.map Operation.instanceRowExtent) id 0
    operation.instanceRowExtent
    (List.mem_map.mpr ⟨operation, hoperation, rfl⟩)

/-- Every copied cell covered by the compiler law lies inside V1's region endpoint. -/
theorem Operations.copiedCell_rowExtent_le_placementEnd
    (operations : Operations F)
    (hassigned : operations.CopyCellsCovered 0 [])
    (cell : Cell) (hcell : cell ∈ operations.copiedCells) :
    cell.rowExtent (FloorPlanner.V1.starts operations) ≤
      FloorPlanner.V1.placementEnd operations := by
  have hassignedCell := hassigned cell hcell
  simp only [List.nil_append] at hassignedCell
  exact operations.assignedCell_rowExtent_le_placementEnd cell hassignedCell

/-- Under copy-cell provenance, one operation's complete copy footprint is bounded by
the placed regions and exact absolute-instance summary. -/
theorem Operation.copyRowExtent_le_placementEnd_max_instanceRowExtent
    (operations : Operations F)
    (hassigned : operations.CopyCellsCovered 0 [])
    (operation : Operation F) (hoperation : operation ∈ operations) :
    operation.copyRowExtent (FloorPlanner.V1.starts operations) ≤
      max (FloorPlanner.V1.placementEnd operations)
        (FloorPlanner.synthesisSummary operations).instanceRowExtent := by
  have copiedCellBound (cell : Cell)
      (hcell : cell ∈ operation.copiedCells) :
      cell.rowExtent (FloorPlanner.V1.starts operations) ≤
        FloorPlanner.V1.placementEnd operations := by
    apply operations.copiedCell_rowExtent_le_placementEnd hassigned cell
    exact List.mem_flatMap.mpr ⟨operation, hoperation, hcell⟩
  have instanceBound :=
    Operation.instanceRowExtent_le_synthesisSummary_of_mem
      operations operation hoperation
  cases operation with
  | region name body =>
      apply foldl_max_le
      intro extent hextent
      obtain ⟨regionOperation, hregionOperation, rfl⟩ := List.mem_map.mp hextent
      have copiedInRegion {candidate : Cell}
          (hcandidate : candidate ∈ regionOperation.copiedCells) :
          candidate ∈ (Operation.region name body).copiedCells := by
        rw [Operation.copiedCells, RegionOperations.copiedCells,
          List.mem_flatMap]
        exact ⟨regionOperation, hregionOperation, hcandidate⟩
      cases regionOperation with
      | assignAdvice => simp [RegionOperation.copyRowExtent]
      | assignFixed => simp [RegionOperation.copyRowExtent]
      | enableGate => simp [RegionOperation.copyRowExtent]
      | enableLookup => simp [RegionOperation.copyRowExtent]
      | constrainEqual left right =>
          simp only [RegionOperation.copyRowExtent, Nat.max_le]
          exact ⟨(copiedCellBound left (copiedInRegion (by
            simp [RegionOperation.copiedCells]))).trans
              (Nat.le_max_left _ _),
            (copiedCellBound right (copiedInRegion (by
              simp [RegionOperation.copiedCells]))).trans
              (Nat.le_max_left _ _)⟩
      | constrainConstant cell value =>
          exact (copiedCellBound cell (copiedInRegion (by
            simp [RegionOperation.copiedCells]))).trans
                (Nat.le_max_left _ _)
      | constrainInstance cell column row =>
          simp only [RegionOperation.copyRowExtent, Nat.max_le]
          refine ⟨(copiedCellBound cell (copiedInRegion (by
            simp [RegionOperation.copiedCells]))).trans
                (Nat.le_max_left _ _), ?_⟩
          apply (FloorPlanner.value_le_foldl_max_of_mem
            (body.map FloorPlanner.regionOperationInstanceRowExtent) id 0
            (row + 1) (List.mem_map.mpr
              ⟨.constrainInstance cell column row, hregionOperation, rfl⟩)).trans
          exact instanceBound.trans (Nat.le_max_right _ _)
  | constrainInstance cell column row =>
      simp only [Operation.copyRowExtent, Nat.max_le]
      exact ⟨(copiedCellBound cell (by
          simp [Operation.copiedCells])).trans (Nat.le_max_left _ _),
        instanceBound.trans (Nat.le_max_right _ _)⟩
  | loadTable column values =>
      simp [Operation.copyRowExtent]

/-- Copy provenance removes the copy stream as an independent source of row growth. -/
theorem Operations.copyRowExtent_le_placementEnd_max_instanceRowExtent
    (operations : Operations F)
    (hassigned : operations.CopyCellsCovered 0 []) :
    (operations.map (Operation.copyRowExtent
      (FloorPlanner.V1.starts operations))).foldl max 0 ≤
      max (FloorPlanner.V1.placementEnd operations)
        (FloorPlanner.synthesisSummary operations).instanceRowExtent := by
  apply foldl_max_le
  intro extent hextent
  obtain ⟨operation, hoperation, rfl⟩ := List.mem_map.mp hextent
  exact Operation.copyRowExtent_le_placementEnd_max_instanceRowExtent
    operations hassigned operation hoperation

/-- The exact generic compiler bound: under copy provenance, all Halo 2 usable-row
checks are covered by V1 placement plus the reduced table and instance summaries. -/
theorem usedRows_le_summaryExtents
    (operations : Operations F)
    (hassigned : operations.CopyCellsAssigned 0 []) :
    usedRows operations ≤
      max (FloorPlanner.V1.placementEnd operations)
        (max (FloorPlanner.synthesisSummary operations).tableRowExtent
          (FloorPlanner.synthesisSummary operations).instanceRowExtent) := by
  have hcovered := operations.copyCellsCovered_of_assigned 0 [] hassigned
  unfold usedRows
  rw [← synthesisSummary_tableRowExtent_eq]
  apply Nat.max_le.mpr
  constructor
  · exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
      (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)⟩
  · exact (Operations.copyRowExtent_le_placementEnd_max_instanceRowExtent
      operations hcovered).trans (by
        exact Nat.max_le.mpr ⟨Nat.le_max_left _ _,
          (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)⟩)

/-- A region operation's copy footprint is bounded by its enclosing region's
copy footprint. -/
theorem RegionOperation.copyRowExtent_le_operation
    (starts : List ℕ) (body : RegionOperations F)
    (operation : RegionOperation F) (hoperation : operation ∈ body) :
    operation.copyRowExtent starts ≤
      (Operation.region "" body).copyRowExtent starts := by
  exact FloorPlanner.value_le_foldl_max_of_mem
    (body.map (RegionOperation.copyRowExtent starts)) id 0
    (operation.copyRowExtent starts)
    (List.mem_map.mpr ⟨operation, hoperation, rfl⟩)

/-- An operation's copy footprint is bounded by the complete operation stream's
usable-row footprint. -/
theorem Operation.copyRowExtent_le_usedRows
    (ops : Operations F) (operation : Operation F)
    (hoperation : operation ∈ ops) :
    operation.copyRowExtent (FloorPlanner.V1.starts ops) ≤ usedRows ops := by
  let starts := FloorPlanner.V1.starts ops
  let copyEnd :=
    (ops.map (Operation.copyRowExtent starts)).foldl max 0
  have hcopy : operation.copyRowExtent starts ≤ copyEnd :=
    FloorPlanner.value_le_foldl_max_of_mem
      (ops.map (Operation.copyRowExtent starts)) id 0
      (operation.copyRowExtent starts)
      (List.mem_map.mpr ⟨operation, hoperation, rfl⟩)
  unfold usedRows
  dsimp only
  exact hcopy.trans (Nat.le_max_right _ _)

/-- The complete operation footprint includes V1's constant-allocation frontier. -/
theorem V1_placementEnd_le_usedRows (ops : Operations F) :
    FloorPlanner.V1.placementEnd ops ≤
      usedRows ops := by
  unfold FloorPlanner.V1.placementEnd usedRows
  dsimp only
  exact Nat.le_max_left _ _ |>.trans (Nat.le_max_left _ _)

/-- Every V1 deferred constant allocation lies below the complete operation
footprint. -/
theorem V1_constantAssignments_row_lt_usedRows
    (ops : Operations F) (constantColumns : List ℕ)
    {value : F} {column row : ℕ}
    (hassignment :
      (value, column, row) ∈
        FloorPlanner.V1.constantAssignments ops constantColumns) :
    row < usedRows ops :=
  (FloorPlanner.V1.constantAssignments_row_lt_placementEnd
    ops constantColumns hassignment).trans_le
      (V1_placementEnd_le_usedRows ops)

/-- Both cells constrained equal lie below the operation stream's row footprint. -/
theorem cells_row_lt_usedRows_of_constrainEqual_mem
    (ops : Operations F) (name : String) (body : RegionOperations F)
    (hregion : Operation.region name body ∈ ops)
    (left right : Cell)
    (hcopy : RegionOperation.constrainEqual left right ∈ body) :
    (FloorPlanner.V1.starts ops).getD left.regionIndex 0 + left.rowOffset <
        usedRows ops ∧
      (FloorPlanner.V1.starts ops).getD right.regionIndex 0 + right.rowOffset <
        usedRows ops := by
  have hbody := RegionOperation.copyRowExtent_le_operation
    (FloorPlanner.V1.starts ops) body (.constrainEqual left right) hcopy
  have hstream := Operation.copyRowExtent_le_usedRows
    ops (.region name body) hregion
  simp only [Operation.copyRowExtent] at hbody hstream
  simp only [RegionOperation.copyRowExtent, Cell.rowExtent] at hbody
  omega

/-- A cell constrained to a constant lies below the operation stream's row
footprint. -/
theorem cell_row_lt_usedRows_of_constrainConstant_mem
    (ops : Operations F) (name : String) (body : RegionOperations F)
    (hregion : Operation.region name body ∈ ops)
    (cell : Cell) (value : F)
    (hcopy : RegionOperation.constrainConstant cell value ∈ body) :
    (FloorPlanner.V1.starts ops).getD cell.regionIndex 0 + cell.rowOffset <
      usedRows ops := by
  have hbody := RegionOperation.copyRowExtent_le_operation
    (FloorPlanner.V1.starts ops) body (.constrainConstant cell value) hcopy
  have hstream := Operation.copyRowExtent_le_usedRows
    ops (.region name body) hregion
  simp only [Operation.copyRowExtent] at hbody hstream
  simp only [RegionOperation.copyRowExtent, Cell.rowExtent] at hbody
  omega

/-- Both endpoints of a region-level instance copy lie below the operation stream's
row footprint. -/
theorem rows_lt_usedRows_of_region_constrainInstance_mem
    (ops : Operations F) (name : String) (body : RegionOperations F)
    (hregion : Operation.region name body ∈ ops)
    (cell : Cell) (column : Column .instance) (row : ℕ)
    (hcopy : RegionOperation.constrainInstance cell column row ∈ body) :
    (FloorPlanner.V1.starts ops).getD cell.regionIndex 0 + cell.rowOffset <
        usedRows ops ∧
      row < usedRows ops := by
  have hbody := RegionOperation.copyRowExtent_le_operation
    (FloorPlanner.V1.starts ops) body (.constrainInstance cell column row) hcopy
  have hstream := Operation.copyRowExtent_le_usedRows
    ops (.region name body) hregion
  simp only [Operation.copyRowExtent] at hbody hstream
  simp only [RegionOperation.copyRowExtent, Cell.rowExtent] at hbody
  omega

/-- Both endpoints of a layouter-level instance copy lie below the operation stream's
row footprint. -/
theorem rows_lt_usedRows_of_constrainInstance_mem
    (ops : Operations F) (cell : Cell) (column : Column .instance) (row : ℕ)
    (hcopy : Operation.constrainInstance cell column row ∈ ops) :
    (FloorPlanner.V1.starts ops).getD cell.regionIndex 0 + cell.rowOffset <
        usedRows ops ∧
      row < usedRows ops := by
  have hstream := Operation.copyRowExtent_le_usedRows
    ops (.constrainInstance cell column row) hcopy
  simp only [Operation.copyRowExtent, Cell.rowExtent] at hstream
  omega

/--
Every lookup operation inside an indexed region lies below the operation stream's
keygen row footprint after V1 placement.
-/
theorem absoluteRow_lt_usedRows_of_enableLookup_mem
    (ops : Operations F) (region : RegionIndex)
    (body : RegionOperations F)
    (hregion : (region, body) ∈ (indexedRegions ops 0).1)
    (argument : LookupArgument F) (enabled : List Selector) (row : ℕ)
    (hlookup : RegionOperation.enableLookup argument enabled row ∈ body) :
    (FloorPlanner.V1.starts ops).getD region 0 + row < usedRows ops := by
  let regions := (indexedRegions ops 0).1
  let starts := FloorPlanner.V1.starts ops
  let regionEnd :=
    (regions.map fun (index, currentBody) =>
      starts.getD index 0 +
        (FloorPlanner.measureRegion index currentBody).rowCount).foldl max 0
  have hrow :
      row < (FloorPlanner.measureRegion region body).rowCount :=
    FloorPlanner.row_lt_measureRegion_of_enableLookup_mem
      region body argument enabled row hlookup
  have hentry :
      starts.getD region 0 +
          (FloorPlanner.measureRegion region body).rowCount ∈
        regions.map fun (index, currentBody) =>
          starts.getD index 0 +
            (FloorPlanner.measureRegion index currentBody).rowCount :=
    List.mem_map.mpr ⟨(region, body), hregion, rfl⟩
  have hend :
      starts.getD region 0 +
          (FloorPlanner.measureRegion region body).rowCount ≤
        regionEnd :=
    FloorPlanner.value_le_foldl_max_of_mem
      (regions.map fun (index, currentBody) =>
        starts.getD index 0 +
          (FloorPlanner.measureRegion index currentBody).rowCount)
      id 0
      (starts.getD region 0 +
        (FloorPlanner.measureRegion region body).rowCount)
      hentry
  have habsolute :
      starts.getD region 0 + row < regionEnd :=
    (Nat.add_lt_add_left hrow _).trans_le hend
  have habsolute' :
      starts.getD region 0 + row <
        FloorPlanner.V1.placementEnd ops := by
    simpa only [regionEnd, FloorPlanner.V1.placementEnd,
      FloorPlanner.V1.placementEndFrom, FloorPlanner.measureRegions,
      List.map_map, Function.comp_apply] using habsolute
  unfold usedRows
  dsimp only
  exact habsolute'.trans_le
    ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _))

/-- The minimal domain exponent fitting an already-derived usable-row requirement. -/
def minimalKForRows (cs : ConstraintSystem F) (requiredRows : ℕ) : ℕ :=
  let blinding := cs.blindingFactors
  -- `blinding + 3 = cs.minimumRows`, without recomputing the blinding count
  let need := max (requiredRows + blinding + 1) (blinding + 3)
  Nat.clog 2 need

/-- Identify an exact minimal domain exponent from the two adjacent power-of-two
bounds on Halo 2's complete row requirement. -/
theorem minimalKForRows_eq_succ_of
    (cs : ConstraintSystem F) (requiredRows k : ℕ)
    (hlower :
      2 ^ k <
        max (requiredRows + cs.blindingFactors + 1) cs.minimumRows)
    (hupper :
      max (requiredRows + cs.blindingFactors + 1) cs.minimumRows ≤
        2 ^ (k + 1)) :
    minimalKForRows cs requiredRows = k + 1 := by
  unfold minimalKForRows
  dsimp only
  apply Nat.le_antisymm
  · apply (Nat.clog_le_iff_le_pow (by omega)).2
    simpa only [ConstraintSystem.minimumRows] using hupper
  · rw [← Nat.lt_iff_add_one_le]
    apply (Nat.lt_clog_iff_pow_lt (by omega)).2
    simpa only [ConstraintSystem.minimumRows] using hlower

/-- The derived domain fits the requested usable rows and minimum-row requirement. -/
theorem minimalKForRows_fits
    (cs : ConstraintSystem F) (requiredRows : ℕ) :
    max (requiredRows + cs.blindingFactors + 1) cs.minimumRows ≤
      2 ^ minimalKForRows cs requiredRows := by
  simpa [minimalKForRows, ConstraintSystem.minimumRows] using
    Nat.le_pow_clog (by omega : 1 < 2)
      (max (requiredRows + cs.blindingFactors + 1)
        (cs.blindingFactors + 3))

/--
The minimal domain exponent for which the circuit's synthesis fits Halo 2's checks.

This is an unbounded derivation. Concrete backends may impose their own supported-domain
limit after compilation, but the semantic compiler never returns a sentinel exponent
that fails its own fit condition.
-/
def minimalK (cs : ConstraintSystem F) (ops : Operations F) : ℕ :=
  minimalKForRows cs (usedRows ops)

/-- The total domain derivation always fits the circuit and minimum-row requirements. -/
theorem minimalK_fits (cs : ConstraintSystem F) (ops : Operations F) :
    max (usedRows ops + cs.blindingFactors + 1) cs.minimumRows ≤
      2 ^ minimalK cs ops :=
  minimalKForRows_fits cs (usedRows ops)

section FormalCircuit
variable [FiniteField F] {ConfigInput Config : Type} {Input Output : TypeMap}
  [CircuitType Input] [CircuitType Output]

/-- A circuit with no caller requirements registers synthesis in its configure result. -/
theorem FormalCircuit.operationsKeygenCoherent
    (c : FormalCircuit F ConfigInput Config Input Output)
    (ci : ConfigInput) (input : Var Input F)
    (hrequirements : KeygenRequirements.EmptyAt
      (self := FormalCircuit.keygenRequirements
        (Input := Input) (Output := Output) c) ci) :
    OperationsKeygenCoherent
      (c.configure ci {}).2
      ((c.synthesize (c.configure ci {}).1 input).operations) := by
  rcases hrequirements with
    ⟨hconfig, hgates, hlookups, hpermutationColumns,
      hinputCells⟩
  let program := c.configure ci
  let counts :=
    ConfigureCounts.ofConstraintSystem ({} : ConstraintSystem F)
  have hregistered :=
    c.elaborated.registered ci counts hconfig input 0
  simp only [hgates, hlookups, hpermutationColumns,
    KeygenRequirements.inputPermutationColumns, hinputCells input,
    List.map_nil, List.nil_append, List.append_nil] at hregistered
  have happlied :=
    hregistered.applyConfigureDelta
      ({} : ConstraintSystem F)
      (program.finalCounts counts)
  simpa only [program, counts, Configure.run,
    ConfigureCounts.ofConstraintSystem] using happlied

/-- A circuit with no caller requirements assigns every copied cell before use. -/
theorem FormalCircuit.operationsCopyCellsAssigned
    (c : FormalCircuit F ConfigInput Config Input Output)
    (ci : ConfigInput) (input : Var Input F)
    (hrequirements : KeygenRequirements.EmptyAt
      (self := FormalCircuit.keygenRequirements
        (Input := Input) (Output := Output) c) ci) :
    ((c.synthesize (c.configure ci {}).1 input).operations).CopyCellsAssigned 0 [] := by
  rcases hrequirements with
    ⟨hconfig, _, _, _, hinputCells⟩
  let counts :=
    ConfigureCounts.ofConstraintSystem ({} : ConstraintSystem F)
  have hassigned :=
    c.elaborated.copyCellsAssigned ci counts hconfig input 0
  simpa only [counts, Configure.run, ConfigureCounts.ofConstraintSystem,
    hinputCells input] using hassigned

/-- A circuit meeting its configure requirements allocates every lookup-input selector. -/
theorem FormalCircuit.lookupSelectorsAllocated
    (c : FormalCircuit F ConfigInput Config Input Output)
    (ci : ConfigInput)
    (hrequirements : c.selectorRequirements ci
      (ConfigureCounts.ofConstraintSystem ({} : ConstraintSystem F))) :
    (c.configure ci {}).2.LookupSelectorsAllocated := by
  let program := c.configure ci
  let counts :=
    ConfigureCounts.ofConstraintSystem ({} : ConstraintSystem F)
  have hallocated :=
    (c.selectorsAllocated ci counts hrequirements).lookups
  simpa only [ConstraintSystem.LookupSelectorsAllocated, program, counts,
    Configure.run, ConfigureCounts.ofConstraintSystem,
    ConfigureDelta.apply, List.nil_append] using hallocated

end FormalCircuit

end Halo2
