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

/--
The rows guarded by Halo 2's `usable_rows` checks during key generation or proving:
floor-planned assignments and selector activations, loaded-table assignments and fill
boundary, and both endpoints of every copy.

In particular, an absolute `constrainInstance` row contributes even though the copy
consumes no region-local space.
-/
def usedRows (ops : Operations F) : ℕ :=
  let regions := (indexedRegions ops 0).1
  let starts := FloorPlanner.V1.starts ops
  let regionEnd :=
    (regions.map fun (index, body) =>
      starts.getD index 0 +
        (FloorPlanner.measureRegion index body).rowCount).foldl max 0
  let tableEnd :=
    (ops.map Operation.tableRowExtent).foldl max 0
  let copyEnd :=
    (ops.map (Operation.copyRowExtent starts)).foldl max 0
  max (max regionEnd tableEnd) copyEnd

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
  unfold usedRows
  dsimp only
  exact habsolute.trans_le
    ((Nat.le_max_left _ _).trans (Nat.le_max_left _ _))

/-- The minimal domain exponent fitting an already-derived usable-row requirement. -/
def minimalKForRows (cs : ConstraintSystem F) (requiredRows : ℕ) : ℕ :=
  let blinding := cs.blindingFactors
  -- `blinding + 3 = cs.minimumRows`, without recomputing the blinding count
  let need := max (requiredRows + blinding + 1) (blinding + 3)
  Nat.clog 2 need

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
    (hrequirements : c.keygenRequirements.EmptyAt ci) :
    OperationsKeygenCoherent
      (c.configure ci {}).2
      ((c.synthesize (c.configure ci {}).1 input).operations) := by
  rcases hrequirements with ⟨hconfig, hgates, hlookups⟩
  let program := c.configure ci
  let counts :=
    ConfigureCounts.ofConstraintSystem ({} : ConstraintSystem F)
  have hregistered :=
    c.elaborated.registered ci counts hconfig input 0
  simp only [hgates, hlookups, List.nil_append] at hregistered
  have happlied :=
    hregistered.applyConfigureDelta
      ({} : ConstraintSystem F)
      (program.finalCounts counts)
  simpa only [program, counts, Configure.run,
    ConfigureCounts.ofConstraintSystem] using happlied

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
