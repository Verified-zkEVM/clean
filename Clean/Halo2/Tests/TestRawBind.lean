module

public import Clean.Halo2.Subcircuit
public import Clean.Halo2.Tactics.CircuitProofStart2
public import Clean.Ironwood.Ecc.Basic
public import Clean.Ironwood.Ecc.Add

@[expose] public section

/-! # Raw-used-bind shape pin for CPS v2

A layouter parent that witnesses a point in a RAW `assignRegion` (a non-call bind whose
value IS used) and feeds it twice into a child call. Pins the atomic-binds delivery for
this shape (design doc, "Raw binds, loops, and the mint gate"):

- the raw binder mints do-binder-named atoms (`p_x`/`p_y`) whose defining equations
  (`p_eq`) are the concrete boundary facts, reduced separately;
- the call is the terminal step (`let s ← call; pure s` lowers to the call itself), so its
  contract (`out_spec`) and the output equation (`output_eq`) spell those atoms — the
  concrete cell record never propagates;
- the raw step's region count folds (the child's index is the literal `i₀ + 1`);
- the content-free raw chunk (`region_0 : True`) is auto-cleared.

The proofs end in `sorry` deliberately: the circuit has no gate on the witnessed point,
so its `Spec` is not provable — the DELIVERED STATE is what this test pins (the
`guard_hyp`s), the established sorry-pin style. -/

namespace Zcash.Circuits.Ecc.TestRawBind

open Halo2

/-- Doubling a witnessed point: raw witness region + one `addFormal` call on `⟨p, p⟩`. -/
def double : FormalCircuit Fp
    ((Column .advice × Column .advice) × Add.Config)
    ((Column .advice × Column .advice) × Add.Config)
    (Unconstrained Point) Point where
  name := "raw-bind double"
  configure := fun ((x, y), acfg) => do
    enableEquality x.toAny
    enableEquality y.toAny
    pure ((x, y), acfg)

  synthesize | ((x, y), acfg), input => do
    let p ← assignRegion "witness p" (do
      let xVar ← assignAdvice x 0 (Witgen.MOver.toIRScalar (Point.x <$> input))
      let yVar ← assignAdvice y 0 (Witgen.MOver.toIRScalar (Point.y <$> input))
      pure ({ x := xVar, y := yVar } : Var Point Fp))
    let s ← Add.addFormal.call acfg { p := p, q := p }
    pure s

  elaborated := {
    keygenRequirements :=
      { configLawful input := Add.add.Configured input.2
        gates _ configured := (configured.toFormal (name := "complete point addition")).gates
        lookups _ configured := (configured.toFormal (name := "complete point addition")).lookups
        fixedColumns _ configured := (configured.toFormal (name := "complete point addition")).fixedColumns
        permutationColumns _ configured :=
          (configured.toFormal (name := "complete point addition")).permutationColumns
        readCells _ _ point :=
          (Witgen.valueBuilderReads (value := field) (Point.x <$> point) ++
            Witgen.valueBuilderReads (value := field) (Point.y <$> point)).map (·.cell) }
    adviceColumnRequirements cfg :=
      cfg.1.1 ≠ cfg.1.2 ∧ Add.addFormal.elaborated.adviceColumnRequirements cfg.2
    registered := by
      intro configInput counts hconfig input i
      simp only [Configure.output_bind,
        Configure.output_pure, Circuit.operations_bind,
        nextRegionIndex_assignRegion, output_assignRegion,
        RegionCircuit.output_bind, output_assignAdvice,
        RegionCircuit.output_pure]
      rw [Operations.KeygenRegistered.append]
      constructor
      · keygen_registration
      · apply Add.addFormal.call_keygenRegistered configInput.2 hconfig.toFormal
        · intro gate hgate
          apply List.mem_append_left
          exact hgate
        · intro lookup hlookup
          apply List.mem_append_left
          exact hlookup
        · intro column hcolumn
          apply List.mem_append_left
          exact hcolumn
        · intro column hcolumn
          apply List.mem_append_left
          apply List.mem_append_left
          exact hcolumn
        · simp only [Add.addFormal_inputCells, List.forall_cons,
            List.forall_nil, and_true]
          and_intros <;> keygen_registration
    consumedCellsAssigned := by
      intro configInput counts hconfig input i
      simp only [Configure.output_bind,
        Configure.output_pure, Circuit.operations_bind, operations_assignRegion,
        nextRegionIndex_assignRegion, output_assignRegion,
        RegionCircuit.output_bind, output_assignAdvice,
        RegionCircuit.output_pure, Operations.ConsumedCellsAssigned,
        KeygenRequirements.readRelativeCellsAt, List.nil_append, List.map_nil,
        List.append_nil]
      apply Operations.AssignedFrom.append
      · rw [Operations.assignedFrom_region_iff]
        refine ⟨?_, by simp [Operations.assignedFrom_nil_iff]⟩
        simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
          operations_assignAdvice, List.singleton_append, List.append_nil]
        apply RegionOperations.AssignedFrom.cons
        · exact ⟨[], rfl, (Witgen.valueBuilderReads (value := field) (Point.x <$> input)).map (·.cell),
            ⟨_, witnessFunctionSupport_scalarBuilder _, fun _ hc _ => List.mem_map_of_mem hc⟩, rfl⟩
        · intro c hc
          simp only [List.nil_append, List.mem_map] at hc
          obtain ⟨a, ha, rfl⟩ := hc
          exact List.mem_map.mpr ⟨a, List.mem_append_left _ ha, rfl⟩
        · apply RegionOperations.AssignedFrom.cons
          · exact ⟨[], rfl, (Witgen.valueBuilderReads (value := field) (Point.y <$> input)).map (·.cell),
              ⟨_, witnessFunctionSupport_scalarBuilder _, fun _ hc _ => List.mem_map_of_mem hc⟩, rfl⟩
          · intro c hc
            simp only [List.nil_append, List.mem_map] at hc
            obtain ⟨a, ha, rfl⟩ := hc
            exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨a, List.mem_append_right _ ha, rfl⟩)
          · exact RegionOperations.AssignedFrom.nil _
      · simp only [keygen_spine]
        apply Add.addFormal.call_consumedCellsAssignedFrom
          configInput.2 hconfig.toFormal _ _
        intro cell hcell
        rw [List.mem_append, List.mem_append, Add.addFormal_inputCells] at hcell
        rcases hcell with (hcell | hcell) | hcell
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hcell
          rcases hcell with hcell | hcell | hcell | hcell <;> simp_all [AssignedCell.of]
        · exact False.elim (List.not_mem_nil hcell)
        · exact False.elim (List.not_mem_nil hcell)
    adviceWritesConsistent := by
      intro configInput counts hconfig hadvice input i
      rcases hadvice with ⟨hxy, haddAdv⟩
      simp only [Configure.output_bind, Configure.output_pure, Circuit.operations_bind,
        operations_assignRegion, nextRegionIndex_assignRegion, output_assignRegion,
        RegionCircuit.output_bind, output_assignAdvice, RegionCircuit.output_pure,
        Operations.adviceWritesConsistentFrom_append, Operations.regionCount]
      refine ⟨?_, ?_⟩
      · rw [Operations.adviceWritesConsistentFrom_region_cons]
        refine ⟨?_, Operations.AdviceWritesConsistentFrom.nil _⟩
        simp only [RegionCircuit.operations_bind, RegionCircuit.operations_pure,
          operations_assignAdvice, List.singleton_append, List.append_nil]
        apply RegionOperations.adviceWritesConsistent_assignAdvice_of_not_mem
        · intro hmem
          have hmem' := RegionOperations.mem_adviceWrites_of_mem_nonSelfCopy i hmem
          simp only [RegionOperations.adviceWrites, List.flatMap_cons, List.flatMap_nil,
            RegionOperation.adviceWrites, List.append_nil, List.mem_singleton,
            Prod.mk.injEq] at hmem'
          exact hxy hmem'.1
        · apply RegionOperations.adviceWritesConsistent_assignAdvice_of_not_mem
          · simp [RegionOperations.nonSelfCopyAdviceWrites]
          · exact RegionOperations.AdviceWritesConsistent.nil
      · exact Add.addFormal.call_adviceWritesConsistent configInput.2 hconfig.toFormal haddAdv _ _
    fixedWritesLawful := by
      intro configInput counts hconfig input i
      apply Operations.HasNoFixedWrites.fixedWritesLawful
      simp only [Configure.output_bind, Configure.output_pure,
        Circuit.operations_bind, Operations.HasNoFixedWrites, List.forall_append]
      constructor
      · keygen_registration
      · apply Add.addFormal.call_hasNoFixedWrites
        simp only [Add.addFormal_synthesisSummary_eq, synthesis_summary_norm]
    lookupActivationsWellFormed := by keygen_registration [keygen_spine]
    synthesisSummary := fun config input i =>
      (FloorPlanner.SynthesisSummary.ofRegion
        (.ofColumns
          [.column .advice config.1.1.index,
            .column .advice config.1.2.index]
          1 0)).combine
        (Add.addFormal.elaborated.synthesisSummary config.2
          { p := { x := .of i 0 config.1.1, y := .of i 0 config.1.2 },
            q := { x := .of i 0 config.1.1, y := .of i 0 config.1.2 } }
          (i + 1))
    synthesisSummary_eq := by
      intro config input i
      simp only [Circuit.operations_bind, FloorPlanner.synthesisSummary_append,
        FormalCircuit.call_synthesisSummary]
      congr 1
    regionCount _ := 2 }

  Spec _ output _ := output.Valid

  ProverAssumptions input _ _ := input.Valid

  soundness := by
    circuit_proof_start2 [Add.addFormal]
    -- the minted boundary facts and the atom-spelled contract, pinned
    guard_hyp p_eq : AssignedCell.of i₀ 0 cfg_1.1 = p_x ∧ AssignedCell.of i₀ 0 cfg_1.2 = p_y
    guard_hyp output_eq : eval (⟨place, env⟩ : Placed Environment Fp)
        (Add.addFormal.output cfg
          { p := { x := p_x, y := p_y }, q := { x := p_x, y := p_y } } (i₀ + 1))
      = { x := output_x, y := output_y }
    guard_hyp out_spec :
      ({ x := AssignedCell.eval place env p_x, y := AssignedCell.eval place env p_y } :
          Point Fp).Valid →
        ({ x := output_x, y := output_y } : Point Fp).Valid ∧
          ({ x := output_x, y := output_y } : Point Fp) =
            { x := AssignedCell.eval place env p_x, y := AssignedCell.eval place env p_y } +
              { x := AssignedCell.eval place env p_x, y := AssignedCell.eval place env p_y }
    sorry

  completeness := by
    circuit_proof_start2 [Add.addFormal]
    sorry

end Zcash.Circuits.Ecc.TestRawBind
