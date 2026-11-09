import Clean.Halo2.TopLevel
import Clean.Halo2.Keygen.Semantics

/-! # Compiled query layouts and their interpretation -/

namespace Halo2

/-- Repackage a pinned constraint system's three query layouts as a query state. -/
def pinnedQueryState
    {F : Type} (pinned : PinnedConstraintSystem F) : QueryState where
  advice := pinned.adviceQueryLayout.toArray
  fixed := pinned.fixedQueryLayout.toArray
  inst := pinned.instanceQueryLayout.toArray

namespace PinnedConstraintSystem

/--
The pinned query layouts are exactly the authoritative query state used by the
read-only expression projection.
-/
theorem derive_queryState_eq
    {F : Type} [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap) :
    pinnedQueryState (derive cs map) =
      queryWalkInit map cs := by
  apply QueryState.ext
  · apply Array.toList_inj.mp
    simp [pinnedQueryState, derive, projectCS]
  · apply Array.toList_inj.mp
    simp [pinnedQueryState, derive, projectCS]
  · apply Array.toList_inj.mp
    simp [pinnedQueryState, derive, projectCS]

/-- Every configure-registered fixed query remains present in the derived pinned
fixed-query layout. -/
theorem mem_fixedQueryLayout_derive_of_mem
    {F : Type} [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap)
    (column : Column .fixed) (rotation : Rotation)
    (hquery : (column, rotation) ∈ cs.fixedQueries) :
    (column.index, rotation) ∈
      (derive cs map).fixedQueryLayout := by
  have hresolved := queryWalkInit_resolves_fixed_of_mem map hquery
  have hstate := derive_queryState_eq cs map
  rw [← hstate] at hresolved
  simpa [QueryState.ResolvesQuery, pinnedQueryState] using hresolved

/-- Every configure-registered instance query remains present in the derived pinned
instance-query layout. -/
theorem mem_instanceQueryLayout_derive_of_mem
    {F : Type} [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap)
    (column : Column .instance) (rotation : Rotation)
    (hquery : (column, rotation) ∈ cs.instanceQueries) :
    (column.index, rotation) ∈
      (derive cs map).instanceQueryLayout := by
  have hregistered :
      (column.index, rotation) ∈
        cs.instanceQueries.map fun query => (query.1.index, query.2) :=
    List.mem_map.mpr ⟨(column, rotation), hquery, by simp⟩
  rw [← queryWalkInit_instance cs map] at hregistered
  have hstate := derive_queryState_eq cs map
  rw [← hstate] at hregistered
  simpa [pinnedQueryState] using hregistered

end PinnedConstraintSystem

namespace TopLevelCircuit

/-- The circuit-owned pinned layouts are its authoritative query state. -/
theorem pinnedQueryState_eq_gateQueryState
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top] :
    pinnedQueryState top.pinnedCS = top.gateQueryState := by
  simpa only [pinnedCS, gateQueryState] using
    PinnedConstraintSystem.derive_queryState_eq
      top.constraintSystem top.selectorMap

/-- Every top-level configured instance query remains in its circuit-owned layout. -/
theorem mem_instanceQueryLayout_of_mem_constraintSystem
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput)
    [TopLevelShape top]
    (column : Column .instance) (rotation : Rotation)
    (hquery : (column, rotation) ∈ top.constraintSystem.instanceQueries) :
    (column.index, rotation) ∈ top.instanceQueryLayout := by
  exact PinnedConstraintSystem.mem_instanceQueryLayout_derive_of_mem
    top.constraintSystem top.selectorMap column rotation hquery

end TopLevelCircuit

end Halo2

/-! ## Row semantics of compiled expressions

Query indices are read through the compiler's layouts. These definitions involve
only column values and integer rotations, not polynomials or commitments.
-/

namespace Halo2

namespace QueryState

variable {F : Type} [Field F]

/-- Read one indexed query at a row of an environment. -/
def queryValues (queries : Array (ℕ × ℤ)) (kind : ColumnKind)
    (env : Environment F) (row : ℤ) (index : ℕ) : F :=
  let query := queries[index]?.getD (0, 0)
  env.get ⟨kind, query.1⟩ (row + query.2)

/-- Evaluate a compiled expression using the column/rotation query layouts. -/
def eval (queries : QueryState) (env : Environment F) (row : ℤ)
    (expression : RichExpression F) : F :=
  expression.eval (queryValues queries.fixed .fixed env row)
    (queryValues queries.advice .advice env row)
    (queryValues queries.inst .instance env row)

/-- Reading registered coordinates interprets the corresponding source queries. -/
theorem queryValues_interprets (queries : QueryState) (env : Environment F) (row : ℤ) :
    Interprets queries (queryValues queries.fixed .fixed env row)
      (queryValues queries.advice .advice env row)
      (queryValues queries.inst .instance env row)
      (Query.eval env (fun _ => 0) row) := by
  constructor <;> intro index column rotation hentry <;>
    simp only [queryValues, hentry, Option.getD_some, Query.eval]
    <;> rfl

end QueryState

namespace TopLevelCircuit

variable {F : Type} [FiniteField F] {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]

/-- Compilation preserves the number of source gate constraints. -/
theorem pinnedCS_gates_length :
    top.pinnedCS.gates.length = (flatGates top.constraintSystem).length := by
  rw [top.pinnedCS_eq_derive]
  exact PinnedConstraintSystem.derive_gates_length _ _

/-- Compiled gate evaluation agrees with the selector-substituted source valuation. -/
theorem pinnedCS_gates_eval_subst (fixed advice instanceFeed : ℕ → F)
    (valuation : Query → F)
    (hcoverage : ∀ expression ∈ flatGates top.constraintSystem,
      expression.selectorsCovered (fun selector => (top.selectorMap.lookup selector).isSome) = true)
    (hinterprets : Interprets (pinnedQueryState top.pinnedCS)
      fixed advice instanceFeed valuation)
    (index : ℕ) (hcompiled : index < top.pinnedCS.gates.length)
    (hsource : index < (flatGates top.constraintSystem).length) :
    top.pinnedCS.gates[index].eval fixed advice instanceFeed =
      (flatGates top.constraintSystem)[index].eval
        (substValuation top.selectorMap.lookup valuation) := by
  rw [top.pinnedQueryState_eq_gateQueryState] at hinterprets
  exact PinnedConstraintSystem.derive_gates_eval top.constraintSystem top.selectorMap
    fixed advice instanceFeed valuation hcoverage top.gateQueriesResolved
    hinterprets index hcompiled hsource

/-- The row evaluation is the selector-substituted source evaluation. -/
theorem pinnedCS_gates_eval (env : Environment F) (row : ℤ)
    (hcoverage : ∀ expression ∈ flatGates top.constraintSystem,
      expression.selectorsCovered (fun selector => (top.selectorMap.lookup selector).isSome) = true)
    (index : ℕ) (hcompiled : index < top.pinnedCS.gates.length)
    (hsource : index < (flatGates top.constraintSystem).length) :
    (pinnedQueryState top.pinnedCS).eval env row top.pinnedCS.gates[index] =
      (flatGates top.constraintSystem)[index].eval
        (substValuation top.selectorMap.lookup (Query.eval env (fun _ => 0) row)) :=
  top.pinnedCS_gates_eval_subst _ _ _ _ hcoverage
    ((pinnedQueryState top.pinnedCS).queryValues_interprets env row) index hcompiled hsource

end TopLevelCircuit

end Halo2
