import Clean.Halo2.Compiler.FieldSupport
import Clean.Halo2.Compiler.Fixed
import Clean.Halo2.Compiler.Queries
import Clean.Halo2.Compiler.SelectorCompression

/-! # Soundness of compiled gate row semantics -/

variable {F : Type} [FiniteField F]

namespace Halo2.TopLevelCircuit

set_option maxHeartbeats 20000

variable {Config : Type} {PublicInput : TypeMap} [ProvableType PublicInput]
    (top : TopLevelCircuit F Config PublicInput) [TopLevelShape top]

/-- The circuit-derived selector map has the roots required by gate scaling. -/
theorem hasWellFormedSelectorRoots_selectorMap
    [FieldDomainParams F] [CircuitFieldSupport top] :
    HasWellFormedSelectorRoots F top.selectorMap := by
  simp only [selectorMap]
  exact hasWellFormedSelectorRoots_deriveSelCompressMap
    top.constraintSystem
    top.n
    top.selectorActivations (CircuitFieldSupport.csDegree_lt_ringChar top)

/-- Selector compression covers every configured gate expression. -/
theorem selectorsCovered_of_mem_flatGates :
    ∀ expression ∈ flatGates top.constraintSystem,
      expression.selectorsCovered
        (fun selector =>
          (top.selectorMap.lookup selector).isSome) = true := by
  simpa only [selectorMap] using
    selectorsCovered_of_mem_flatGates_deriveSelCompressMap
      top.constraintSystem
      top.n
      top.selectorActivations
      top.gateSelectorsAllocated

/-- The compiled gate polynomials vanish at every row of the evaluation domain. -/
def GatesCompiled (assignment : ProofAssignment F) : Prop :=
  ∀ expression ∈ top.pinnedCS.gates, ∀ row : ℕ, row < top.n →
    (pinnedQueryState top.pinnedCS).eval (top.environment assignment) row expression = 0

/-- Any query feeds interpreting the compiled layout give its row evaluation.
Consumers need not reason about selector substitution or expression erasure. -/
theorem pinnedCS_gates_eval_of_interprets
    (env : Environment F) (row : ℤ) (fixed advice instanceFeed : ℕ → F)
    (hinterprets : Interprets (pinnedQueryState top.pinnedCS) fixed advice instanceFeed
      (Query.eval env (fun _ => 0) row))
    (index : ℕ) (hindex : index < top.pinnedCS.gates.length) :
    top.pinnedCS.gates[index].eval fixed advice instanceFeed =
      (pinnedQueryState top.pinnedCS).eval env row top.pinnedCS.gates[index] := by
  have hsource : index < (flatGates top.constraintSystem).length := by
    rwa [← top.pinnedCS_gates_length]
  rw [top.pinnedCS_gates_eval env row top.selectorsCovered_of_mem_flatGates index hindex hsource]
  exact top.pinnedCS_gates_eval_subst fixed advice instanceFeed
    (Query.eval env (fun _ => 0) row) top.selectorsCovered_of_mem_flatGates
    hinterprets index hindex hsource

/-- Packed selector roots are realized without any hypothesis on the assignment. -/
theorem realizesSelectorActivations_environment (assignment : ProofAssignment F) :
    RealizesSelectorActivations top.selectorMap top.selectorActivations
      (top.environment assignment) := by
  apply realizesSelectorActivations_of_selectorAssignments
  intro entry hentry
  exact top.environment_fixed_of_mem_raw assignment (top.selectorAssignment_mem_raw hentry)

/-- Compiled gate vanishing implies all source gate constraints. Selector packing,
query indexing, and gate activation are internal to this compiler theorem. -/
theorem gate_constraints_of_compiled [FieldDomainParams F] [CircuitFieldSupport top]
    (assignment : ProofAssignment F) (hgates : top.GatesCompiled assignment) :
    CircuitConstraintFamily.Constraints .gate top.placement
      (top.environment assignment) top.operations 0 := by
  rw [CircuitConstraintFamily.gate_constraints_iff_enabledGates,
    List.forall_iff_forall_mem]
  intro enabled henabled
  have hgate := OperationsKeygenCoherent.mem_gates_of_mem_operationEnabledGates
    top.keygenCoherent henabled
  have hselector := List.forall_iff_forall_mem.mp top.gateSelectorsAllocated enabled.gate hgate
  have hsome : (top.selectorMap.lookup enabled.gate.selector.index).isSome := by
    simpa only [selectorMap] using
      deriveSelCompressMap_lookup_isSome_of_lt top.constraintSystem top.n
        top.selectorActivations hselector
  obtain ⟨compressed, hcompressed⟩ := Option.isSome_iff_exists.mp hsome
  have hactivation := mem_activations_of_mem_operationEnabledGate top.regionStarts henabled
  have hentry := Layout.mem_selectorAssignments_of_activation (F := F)
    top.selectorMap top.selectorActivations hactivation hcompressed
  have hrow := (top.fixedAssignment_bounds_of_mem_raw _
    (top.selectorAssignment_mem_raw hentry)).2
  rw [EnabledGate.IsSatisfied, List.forall_iff_forall_mem]
  intro constraint hconstraint
  have hflat : constraint.poly ∈ flatGates top.constraintSystem := by
    rw [flatGates, List.mem_flatMap]
    exact ⟨enabled.gate, hgate, List.mem_map.mpr ⟨constraint, hconstraint, rfl⟩⟩
  obtain ⟨index, hindex, hsource⟩ := List.mem_iff_getElem.mp hflat
  have hcompiled : index < top.pinnedCS.gates.length := by
    rw [top.pinnedCS_gates_length]
    exact hindex
  have hzero := hgates _ (List.getElem_mem hcompiled)
    (top.placement enabled.region + enabled.row) (by
      simpa only [placement_apply] using hrow)
  rw [top.pinnedCS_gates_eval _ _ top.selectorsCovered_of_mem_flatGates index hcompiled hindex,
    hsource] at hzero
  apply Expression.eval_substSelectorMap_zero_imp_queryEval_zero top.selectorMap.lookup
    (Query.eval (top.environment assignment) (fun _ => 0)
      (top.placement enabled.region + enabled.row : ℕ))
    (top.environment assignment) constraint.poly enabled.gate.selector compressed
    (top.placement enabled.region + enabled.row : ℕ)
    (enabled.gate.wellFormed.compressionSound constraint hconstraint) hcompressed
  · simpa only [placement_apply] using
      selectorScale_ne_zero_of_enabledGate top.selectorMap top.regionStarts top.operations 0
        (top.environment assignment) (fun _ => 0) top.hasWellFormedSelectorRoots_selectorMap
        (top.realizesSelectorActivations_environment assignment) henabled hcompressed
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · rw [substSelectorMap_eval]
    exact hzero

end Halo2.TopLevelCircuit
