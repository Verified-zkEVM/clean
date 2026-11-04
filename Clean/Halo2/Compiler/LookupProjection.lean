import Clean.Halo2.Compiler.Queries

/-!
# Lookup projection across the Clean boundary

Key generation substitutes the circuit's virtual selectors, then resolves each
configured `LookupArgument` against the authoritative compiler-derived query layout.
This module proves the semantic part of that translation for one selected lookup.

The result deliberately stops at the selector-substitution valuation. A lookup
activation needs the stronger row fact that its complex selectors have their exact
zero/one values; unlike a custom gate, an arbitrary nonzero selector scale is not
enough for tuple membership.
-/

namespace Halo2

set_option maxHeartbeats 20000

/-- Query projection preserves evaluation of a selector-substituted expression list. -/
theorem eraseGates_substSelectorMap_eval
    {F : Type} [Field F] [DecidableEq F]
    (map : SelCompressMap) (queries : QueryState)
    (fixed advice instanceFeed : ℕ → F) (valuation : Query → F)
    (expressions : List (Expression F Query))
    (hcoverage : ∀ expression ∈ expressions,
      expression.selectorsCovered (fun selector => (map.lookup selector).isSome) = true)
    (hresolved : (expressions.map (substSelectorMap map.lookup)).Forall
      (·.QueriesResolved queries))
    (hinterprets : Interprets queries fixed advice instanceFeed valuation) :
    (eraseGates (expressions.map (substSelectorMap map.lookup)) queries).map
        (RichExpression.eval fixed advice instanceFeed) =
      expressions.map (Expression.eval (substValuation map.lookup valuation)) := by
  simp only [eraseGates, List.map_map]
  apply List.map_congr_left
  intro expression hmem
  exact eraseExpr_substSelectorMap_eval map.lookup fixed advice instanceFeed valuation
    expression queries (hcoverage expression hmem)
    (List.forall_iff_forall_mem.mp hresolved _ (List.mem_map.mpr ⟨expression, hmem, rfl⟩))
    hinterprets

/-- A selected pinned lookup evaluates like its selector-substituted source argument
whenever all of that argument's queries resolve against the compiler layout. -/
theorem PinnedConstraintSystem.derive_lookup_eval
    {F : Type} [Field F] [DecidableEq F]
    (cs : ConstraintSystem F) (map : SelCompressMap)
    (fixed advice instanceFeed : ℕ → F) (valuation : Query → F)
    (lookupIndex : ℕ) (hlookup : lookupIndex < cs.lookups.length)
    (hinputCoverage :
      ∀ expression ∈ cs.lookups[lookupIndex].inputs,
        expression.selectorsCovered
          (fun selector => (map.lookup selector).isSome) = true)
    (htableCoverage :
      ∀ expression ∈ cs.lookups[lookupIndex].tables,
        expression.selectorsCovered
          (fun selector => (map.lookup selector).isSome) = true)
    (hinputResolved :
      (cs.lookups[lookupIndex].inputs.map
        (substSelectorMap map.lookup)).Forall
          (·.QueriesResolved (queryWalkInit map cs)))
    (htableResolved :
      (cs.lookups[lookupIndex].tables.map
        (substSelectorMap map.lookup)).Forall
          (·.QueriesResolved (queryWalkInit map cs)))
    (hinterprets :
      Interprets
        (pinnedQueryState (PinnedConstraintSystem.derive cs map))
        fixed advice instanceFeed valuation) :
    (((PinnedConstraintSystem.derive cs map).lookupInputExprs.getD
        lookupIndex []).map
        (RichExpression.eval fixed advice instanceFeed) =
      cs.lookups[lookupIndex].inputs.map
        (Expression.eval
          (substValuation map.lookup valuation))) ∧
    (((PinnedConstraintSystem.derive cs map).lookupTableExprs.getD
        lookupIndex []).map
        (RichExpression.eval fixed advice instanceFeed) =
      cs.lookups[lookupIndex].tables.map
        (Expression.eval
          (substValuation map.lookup valuation))) := by
  have hinterpretsQueries : Interprets (queryWalkInit map cs)
      fixed advice instanceFeed valuation := by
    rwa [← PinnedConstraintSystem.derive_queryState_eq cs map]
  rw [PinnedConstraintSystem.derive_lookupInputExprs_getD cs map lookupIndex hlookup,
    PinnedConstraintSystem.derive_lookupTableExprs_getD cs map lookupIndex hlookup]
  exact ⟨eraseGates_substSelectorMap_eval map _ _ _ _ _ _
      hinputCoverage hinputResolved hinterpretsQueries,
    eraseGates_substSelectorMap_eval map _ _ _ _ _ _
      htableCoverage htableResolved hinterpretsQueries⟩

/-- Project one lookup directly through a top-level circuit's owned compilation. -/
theorem _root_.Halo2.TopLevelCircuit.lookup_eval
    {F : Type} [FiniteField F]
    {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput)
    [TopLevelShape top]
    (fixed advice instanceFeed : ℕ → F) (valuation : Query → F)
    (lookup : Fin top.lookupCount)
    (hinputCoverage :
      ∀ expression ∈ (top.lookupAt lookup).inputs,
        expression.selectorsCovered
          (fun selector => (top.selectorMap.lookup selector).isSome) = true)
    (htableCoverage :
      ∀ expression ∈ (top.lookupAt lookup).tables,
        expression.selectorsCovered
          (fun selector => (top.selectorMap.lookup selector).isSome) = true)
    (hinterprets :
      Interprets (pinnedQueryState top.pinnedCS)
        fixed advice instanceFeed valuation) :
    ((top.pinnedCS.lookupInputExprs.getD lookup.val []).map
        (RichExpression.eval fixed advice instanceFeed) =
      (top.lookupAt lookup).inputs.map
        (Expression.eval
          (substValuation top.selectorMap.lookup valuation))) ∧
    ((top.pinnedCS.lookupTableExprs.getD lookup.val []).map
        (RichExpression.eval fixed advice instanceFeed) =
      (top.lookupAt lookup).tables.map
        (Expression.eval
          (substValuation top.selectorMap.lookup valuation))) := by
  have hlookup : lookup.val < top.constraintSystem.lookups.length := by
    rw [← top.lookupCount_eq_constraintSystem]
    exact lookup.isLt
  let argument := top.lookupAt lookup
  have hargument : argument ∈ top.constraintSystem.lookups :=
    top.lookupAt_mem_constraintSystem lookup
  have hresolved := top.lookupQueriesResolved argument hargument
  exact PinnedConstraintSystem.derive_lookup_eval
    top.constraintSystem top.selectorMap fixed advice instanceFeed valuation
    lookup.val hlookup hinputCoverage htableCoverage hresolved.1 hresolved.2
    hinterprets

end Halo2
