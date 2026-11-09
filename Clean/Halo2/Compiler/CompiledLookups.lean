import Clean.Halo2.Compiler.LookupProjection
import Clean.Halo2.Compiler.LookupSelectors

/-! # Soundness of compiled lookup row semantics

The compiler exports configured lookup indices and their absolute activation rows.
Membership compares uncompressed tuples at these rows with a table tuple at any
usable row. Selector substitution and operation membership stay inside this layer.
-/

variable {F : Type} [FiniteField F]

namespace Halo2.TopLevelCircuit

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]

/-- The canonical environment uses the published circuit's usable-row prefix. -/
theorem environment_usableRows_eq (assignment : ProofAssignment F) :
    (top.environment assignment).usableRows = top.usableRowsAt top.domainExponent := by
  rw [top.environment_usableRows, ← top.domainExponent_eq_compiled,
    top.usableRowsAt_domainExponent, top.n_eq_two_pow_domainExponent]

/-- Lookup indices and absolute rows at which synthesis requests tuple membership. -/
def lookupActivationRows : List (Fin top.lookupCount × ℕ) :=
  (operationEnabledLookups top.operations 0).attach.map fun lookup =>
    ((lookup.val.topLevelRoute lookup.property).index,
      top.placement lookup.val.region + lookup.val.row)

/-- The compiled schedule preserves the compositional activation count. -/
theorem lookupActivationRows_length :
    top.lookupActivationRows.length = top.synthesisSummary.lookupActivationCount := by
  simp only [lookupActivationRows, List.length_map, List.length_attach,
    operationEnabledLookups_length, ← top.synthesisSummary_eq_operations]

/-- Query compilation does not change input tuple arity. -/
theorem lookupInputExprs_length
    {F : Type} [FiniteField F] (top : TopLevelCircuit F Config PublicInput)
    [TopLevelShape top] (index : Fin top.lookupCount) :
    (top.pinnedCS.lookupInputExprs.getD index []).length = (top.lookupAt index).inputs.length := by
  have hi : index.val < top.constraintSystem.lookups.length := by
    rw [← top.lookupCount_eq_constraintSystem]
    exact index.isLt
  rw [top.pinnedCS_eq_derive,
    PinnedConstraintSystem.derive_lookupInputExprs_getD _ _ _ hi,
    eraseGates_length, List.length_map, lookupAt]

/-- Every compiled activation is within the usable domain. -/
theorem lookupActivationRows_row_lt {activation : Fin top.lookupCount × ℕ}
    (h : activation ∈ top.lookupActivationRows) :
    activation.2 < top.usableRowsAt top.domainExponent := by
  obtain ⟨⟨lookup, henabled⟩, _, rfl⟩ := List.mem_map.mp h
  exact lookup.activationRow_lt_usableRows henabled

/-- Selector substitution and query indexing preserve lookup tuple arities. -/
theorem lookupInputExprs_length_eq_table
    {F : Type} [FiniteField F] (top : TopLevelCircuit F Config PublicInput)
    [TopLevelShape top] (index : Fin top.lookupCount) :
    (top.pinnedCS.lookupInputExprs.getD index []).length =
      (top.pinnedCS.lookupTableExprs.getD index []).length := by
  have hi : index.val < top.constraintSystem.lookups.length := by
    rw [← top.lookupCount_eq_constraintSystem]
    exact index.isLt
  rw [top.pinnedCS_eq_derive,
    PinnedConstraintSystem.derive_lookupInputExprs_getD _ _ _ hi,
    PinnedConstraintSystem.derive_lookupTableExprs_getD _ _ _ hi,
    eraseGates_length, eraseGates_length, List.length_map, List.length_map]
  exact top.constraintSystem.lookups[index.val].arity

/-- Every activated compiled input tuple occurs in its compiled table. -/
def LookupsCompiled (assignment : ProofAssignment F) : Prop :=
  ∀ activation ∈ top.lookupActivationRows,
    ∃ row < top.usableRowsAt top.domainExponent,
      (top.pinnedCS.lookupInputExprs.getD activation.1 []).map
          ((pinnedQueryState top.pinnedCS).eval (top.environment assignment) activation.2) =
        (top.pinnedCS.lookupTableExprs.getD activation.1 []).map
          ((pinnedQueryState top.pinnedCS).eval (top.environment assignment) row)

/-- Compiled lookup evaluation depends only on the interpreted query coordinates. -/
theorem pinnedCS_lookup_eval_of_interprets
    (env : Environment F) (row : ℤ) (fixed advice instanceFeed : ℕ → F)
    (hinterprets : Interprets (pinnedQueryState top.pinnedCS) fixed advice instanceFeed
      (Query.eval env (fun _ => 0) row)) (index : Fin top.lookupCount) :
    ((top.pinnedCS.lookupInputExprs.getD index []).map
        (RichExpression.eval fixed advice instanceFeed) =
      (top.pinnedCS.lookupInputExprs.getD index []).map
        ((pinnedQueryState top.pinnedCS).eval env row)) ∧
    ((top.pinnedCS.lookupTableExprs.getD index []).map
        (RichExpression.eval fixed advice instanceFeed) =
      (top.pinnedCS.lookupTableExprs.getD index []).map
        ((pinnedQueryState top.pinnedCS).eval env row)) := by
  have hcoverage := selectorsCovered_of_mem_lookup_inputs top (top.lookupAt index)
    (top.lookupAt_mem_constraintSystem index)
  have htables := LookupArgument.selectorsCovered_of_mem_tables (top := top) (top.lookupAt index)
  have hfeed := top.lookup_eval fixed advice instanceFeed _ index hcoverage htables hinterprets
  have hrow := top.lookup_eval _ _ _ _ index hcoverage htables
    ((pinnedQueryState top.pinnedCS).queryValues_interprets env row)
  exact ⟨hfeed.1.trans hrow.1.symm, hfeed.2.trans hrow.2.symm⟩

/-- At a synthesized activation, compiled tuples are the source input/table tuples.
The assignment carries no selector or fixed-column coherence hypothesis. -/
theorem lookup_values_eq (assignment : ProofAssignment F)
    (lookup : EnabledLookup F)
    (henabled : lookup ∈ operationEnabledLookups top.operations 0) :
    let index := (lookup.topLevelRoute henabled).index
    ((top.pinnedCS.lookupInputExprs.getD index []).map
        ((pinnedQueryState top.pinnedCS).eval (top.environment assignment)
          (top.placement lookup.region + lookup.row : ℕ)) =
      lookup.inputValues top.placement (top.environment assignment)) ∧
    (∀ row < top.usableRowsAt top.domainExponent,
      (top.pinnedCS.lookupTableExprs.getD index []).map
          ((pinnedQueryState top.pinnedCS).eval (top.environment assignment) row) =
        lookup.tableValues (top.environment assignment) row) := by
  let route := lookup.topLevelRoute henabled
  have project (row : ℤ) := top.lookup_eval _ _ _ _ route.index
    (selectorsCovered_of_mem_lookup_inputs top _ (top.lookupAt_mem_constraintSystem route.index))
    (LookupArgument.selectorsCovered_of_mem_tables (top := top) _)
    ((pinnedQueryState top.pinnedCS).queryValues_interprets (top.environment assignment) row)
  constructor
  · have hinput := (project (top.placement lookup.region + lookup.row : ℕ)).1
    rw [route.lookupAt_eq] at hinput
    exact hinput.trans (lookup.inputValues_eq henabled assignment)
  · intro row hrow
    have htable := (project row).2
    rw [route.lookupAt_eq] at htable
    apply htable.trans
    apply List.map_congr_left
    intro expression hexpression
    exact Expression.eval_substValuation_eq_queryEval_of_selectorFree
      top.selectorMap (top.environment assignment) lookup.selectorValue row expression
      (lookup.argument.tablesFree expression hexpression)

/-- Compiled tuple membership recovers every source lookup constraint. -/
theorem lookup_constraints_of_compiled
    (assignment : ProofAssignment F) (hlookups : top.LookupsCompiled assignment) :
    CircuitConstraintFamily.Constraints .lookup top.placement
      (top.environment assignment) top.operations 0 := by
  rw [CircuitConstraintFamily.lookup_constraints_iff_enabledLookups,
    List.forall_iff_forall_mem]
  intro lookup henabled
  have hactivation : ((lookup.topLevelRoute henabled).index,
      top.placement lookup.region + lookup.row) ∈ top.lookupActivationRows :=
    List.mem_map.mpr ⟨⟨lookup, henabled⟩, List.mem_attach _ _, rfl⟩
  obtain ⟨row, hrow, hvalues⟩ := hlookups _ hactivation
  have hprojection := top.lookup_values_eq assignment lookup henabled
  exact ⟨row, by rwa [top.environment_usableRows_eq],
    hprojection.1.symm.trans (hvalues.trans (hprojection.2 row hrow))⟩

end Halo2.TopLevelCircuit
