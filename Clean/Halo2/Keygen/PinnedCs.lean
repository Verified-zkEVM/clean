import Clean.Halo2.Keygen.Projection
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
    ⟨hconfig, hgates, hlookups, hfixedColumns, hconstantColumns,
      hpermutationColumns, hinputCells⟩
  let program := c.configure ci
  let counts :=
    ConfigureCounts.ofConstraintSystem ({} : ConstraintSystem F)
  have hregistered :=
    c.elaborated.registered ci counts hconfig input 0
  simp only [hgates, hlookups, hfixedColumns, hpermutationColumns,
    KeygenRequirements.inputPermutationColumns, hinputCells input,
    List.map_nil, List.nil_append, List.append_nil] at hregistered
  have happlied :=
    hregistered.applyConfigureDelta
      ({} : ConstraintSystem F)
      (program.finalCounts counts) (by
        intro column hcolumn
        exact (Configure.mem_fixedColumns_iff program counts column).mp hcolumn |>.2)
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
    ⟨hconfig, _, _, _, _, _, hinputCells⟩
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
