import Clean.Ironwood.Action.Compilation

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

/-- The selector-free reduced input to Action's physical V1 placement. -/
def actionPlannerSummaries : List RegionShapeSummary :=
  actionSynthesisSummary.regionShapes.map
    RegionShapeSummary.withoutSelectors

theorem actionPlannerSummaries_eq_physicalRegionShapes :
    actionPlannerSummaries =
      actionSynthesisSummary.physicalRegionShapes := rfl

/-- Action's exact selector-free summary order after consensus pdqsort. -/
def actionSortedPlannerSummaries : List RegionShapeSummary :=
  (V1.sortedSummaryOrder actionOperations).map
    RegionShapeSummary.withoutSelectors

private theorem actionConfig_advice0 : (actionConfig.advices 0).index = 0 := by rfl
private theorem actionConfig_advice5 : (actionConfig.advices 5).index = 5 := by rfl
private theorem actionConfig_advice6 : (actionConfig.advices 6).index = 6 := by rfl
private theorem actionConfig_advice9 : (actionConfig.advices 9).index = 9 := by rfl
private theorem actionConfig_qRunning :
    actionConfig.lookupConfig.qRunning.index = 3 := by rfl
private theorem actionConfig_runningSum :
    actionConfig.lookupConfig.runningSum.index = 9 := by rfl
private theorem actionConfig_qPoint :
    actionConfig.eccConfig.witnessPoint.qPoint.index = 5 := by rfl
private theorem actionConfig_qPointNonId :
    actionConfig.eccConfig.witnessPoint.qPointNonId.index = 6 := by rfl
private theorem actionConfig_witnessX :
    actionConfig.eccConfig.witnessPoint.x.index = 0 := by rfl
private theorem actionConfig_witnessY :
    actionConfig.eccConfig.witnessPoint.y.index = 1 := by rfl
private theorem actionConfig_qMulLsb :
    actionConfig.eccConfig.mul.qMulLsb.index = 17 := by rfl
private theorem actionConfig_mulAddXP :
    actionConfig.eccConfig.mul.addConfig.xP.index = 0 := by rfl
private theorem actionConfig_qOrchard : actionConfig.qOrchard.index = 0 := by rfl

/-- Maps each Action selector to the advice column whose assignments determine that selector's
physical V1 placement. -/
def selectorAnchor (cfg : Circuit.Config) (selector : ℕ) : RegionColumn :=
  if selector = 2 ∨ selector = 3 ∨ selector = 4 then
    .column .advice (cfg.advices 9).index
  else if 29 ≤ selector ∧ selector ≤ 32 ∨ selector = 44 ∨ selector = 55 then
    .column .advice (cfg.advices 5).index
  else if selector = 1 ∨ selector = 16 ∨
      (21 ≤ selector ∧ selector ≤ 24) ∨
      (34 ≤ selector ∧ selector ≤ 43) ∨
      (45 ≤ selector ∧ selector ≤ 54) then
    .column .advice (cfg.advices 6).index
  else
    .column .advice (cfg.advices 0).index

/-- The concrete Action selector anchor solves its reduced lookup-anchor equations. -/
theorem actionLookupSelectorAnchorRequirements_satisfied :
    SelectorAnchorRequirementsSatisfied
      (LookupRangeCheck.lookupSelectorAnchorRequirements
        actionConfig.lookupConfig)
      (selectorAnchor actionConfig) := by
  simp only [LookupRangeCheck.lookupSelectorAnchorRequirements,
    SelectorAnchorRequirementsSatisfied, List.forall_cons,
    List.forall_nil, and_true]
  rw [actionConfig_qRunning, actionConfig_runningSum]
  simp [selectorAnchor, actionConfig_advice9]

private theorem hashPieceLoop_selectorAnchored
    (n offset : ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (anchor : ℕ → RegionColumn)
    (hq : anchor cfg.qS1.index = .column .advice cfg.xA.index) :
    V1.SummarySelectorsAnchoredBy
      (Sinsemilla.HashPiece.loopSynthesisSummary n cfg offset
        |>.toRegionShapeSummary)
      anchor := by
  unfold Sinsemilla.HashPiece.loopSynthesisSummary
  rw [RegionSynthesisSummary.repeatColumnsWithSelectorPattern_toRegionShapeSummary
    (instanceRowExtent := 0) (lookupActivationCount := 1)]
  cases n with
  | zero =>
      intro selector hselector
      exfalso
      simp [RegionSynthesisSummary.repeatColumns,
        RegionSynthesisSummary.toRegionShapeSummary] at hselector
  | succ n =>
      simp only [RegionSynthesisSummary.repeatColumns, Nat.succ_ne_zero,
        ↓reduceIte]
      apply V1.SummarySelectorsAnchoredBy.ofColumns
      intro selector hselector
      simp only [Sinsemilla.HashPiece.roundColumns] at hselector ⊢
      simp_all [physicalColumns]

private theorem hashPieceCircuit_selectorAnchored
    (w offset : ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (anchor : ℕ → RegionColumn)
    (hq : anchor cfg.qS1.index = .column .advice cfg.xA.index) :
    V1.SummarySelectorsAnchoredBy
      (Sinsemilla.HashPiece.circuitSynthesisSummary w cfg offset
        |>.toRegionShapeSummary)
      anchor := by
  unfold Sinsemilla.HashPiece.circuitSynthesisSummary
  apply V1.SummarySelectorsAnchoredBy.combine
  · apply V1.SummarySelectorsAnchoredBy.ofColumns
    simp
  · apply V1.SummarySelectorsAnchoredBy.combine
    · exact hashPieceLoop_selectorAnchored w offset cfg anchor hq
    · apply V1.SummarySelectorsAnchoredBy.ofColumns
      intro selector hselector
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hselector
      rcases hselector with hselector | hselector | hselector
      all_goals try simp at hselector
      cases hselector
      rw [hq]
      simp [physicalColumns]

private theorem hashPieceCircuit_xA_mem
    (w offset : ℕ) (cfg : Sinsemilla.HashPiece.Config) :
    .column .advice cfg.xA.index ∈
      (Sinsemilla.HashPiece.circuitSynthesisSummary w cfg offset).columns := by
  rw [Sinsemilla.HashPiece.circuitSynthesisSummary,
    RegionSynthesisSummary.combine_columns,
    FloorPlanner.mem_unionColumns_iff,
    RegionSynthesisSummary.combine_columns,
    FloorPlanner.mem_unionColumns_iff]
  apply Or.inr
  apply Or.inr
  rw [RegionSynthesisSummary.ofColumns_columns,
    FloorPlanner.mem_unionColumns_iff]
  exact Or.inr (by simp)

private theorem chainSlotSummary_selectorAnchored
    (ns : List ℕ) (i : ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (base : ℕ) (anchor : ℕ → RegionColumn)
    (hq : anchor cfg.qS1.index = .column .advice cfg.xA.index) :
    V1.SummarySelectorsAnchoredBy
      (Sinsemilla.Chain.slotSynthesisSummary ns i cfg base
        |>.toRegionShapeSummary)
      anchor := by
  rw [Sinsemilla.Chain.slotSynthesisSummary]
  exact hashPieceCircuit_selectorAnchored (ns.getD i 0) base cfg anchor hq

private theorem chainSlot_selectorAnchored
    (ns : List ℕ) (i : ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (base : ℕ) (anchor : ℕ → RegionColumn)
    (hq : anchor cfg.qS1.index = .column .advice cfg.xA.index) :
    V1.SummarySelectorsAnchoredBy
      (Sinsemilla.Chain.slotIterationSynthesisSummary ns i cfg base
        |>.toRegionShapeSummary)
      anchor := by
  intro selector hselector
  rw [Sinsemilla.Chain.slotIterationSynthesisSummary,
    RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.combine_columns,
    FloorPlanner.mem_unionColumns_iff] at hselector
  rcases hselector with hselector | hselector
  · have hanchor := chainSlotSummary_selectorAnchored ns i cfg base anchor hq
      selector (by simpa only [RegionSynthesisSummary.toRegionShapeSummary_columns]
        using hselector)
    obtain ⟨kind, index, heq⟩ := V1.exists_column_of_mem_physicalColumns hanchor
    have hphysical : .column kind index ∈
        physicalColumns
          (Sinsemilla.Chain.slotSynthesisSummary ns i cfg base).columns := by
      simpa only [RegionSynthesisSummary.toRegionShapeSummary_columns, ← heq]
        using hanchor
    rw [heq, Sinsemilla.Chain.slotIterationSynthesisSummary,
      RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns,
      V1.column_mem_physicalColumns_iff,
      FloorPlanner.mem_unionColumns_iff]
    exact Or.inl
      ((V1.column_mem_physicalColumns_iff kind index _).mp hphysical)
  · simp only [RegionSynthesisSummary.ofColumns_columns,
      FloorPlanner.mem_unionColumns_iff, List.not_mem_nil,
      List.mem_cons, or_false] at hselector
    simp at hselector
    subst selector
    rw [hq, Sinsemilla.Chain.slotIterationSynthesisSummary,
      RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns,
      V1.column_mem_physicalColumns_iff,
      FloorPlanner.mem_unionColumns_iff]
    exact Or.inl (hashPieceCircuit_xA_mem (ns.getD i 0) base cfg)

private theorem chain_selectorAnchored
    (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (anchor : ℕ → RegionColumn)
    (hq : anchor cfg.qS1.index = .column .advice cfg.xA.index) :
    V1.SummarySelectorsAnchoredBy
      (Sinsemilla.Chain.circuitSynthesisSummary ns cfg offset
        |>.toRegionShapeSummary)
      anchor := by
  unfold Sinsemilla.Chain.circuitSynthesisSummary
  apply V1.SummarySelectorsAnchoredBy.combine
  · apply V1.SummarySelectorsAnchoredBy.foldr_combine
    rw [List.forall_iff_forall_mem]
    intro summary hsummary
    simp only [List.mem_ofFn] at hsummary
    obtain ⟨i, rfl⟩ := hsummary
    exact chainSlot_selectorAnchored ns i cfg
      (offset + Sinsemilla.Chain.prefixRows ns i) anchor hq
  · apply V1.SummarySelectorsAnchoredBy.ofColumns
    simp

private theorem witnessShortCheck_selectorAnchored
    (K : ℕ) (cfg : LookupRangeCheck.Config K)
    (anchor : ℕ → RegionColumn)
    (hlookup : anchor cfg.qLookup.index =
      .column .advice cfg.runningSum.index)
    (hbitshift : anchor cfg.qBitshift.index =
      .column .advice cfg.runningSum.index) :
    V1.SelectorAnchoredBy
      (LookupRangeCheck.witnessShortCheckSynthesisSummary K cfg).regionShapes
      anchor := by
  apply V1.SelectorAnchoredBy.ofRegion
  apply V1.SummarySelectorsAnchoredBy.combine
  · apply V1.SummarySelectorsAnchoredBy.ofColumns
    simp
  · unfold LookupRangeCheck.shortRangeCheckSynthesisSummary
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp at hselector
    rcases hselector with rfl | rfl
    · rw [hlookup]
      simp [physicalColumns]
    · rw [hbitshift]
      simp [physicalColumns]

private theorem hashToPoint_selectorAnchored
    (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config) (offset : ℕ)
    (anchor : ℕ → RegionColumn)
    (hq1 : anchor cfg.qS1.index = .column .advice cfg.xA.index)
    (hq4 : anchor cfg.qS4.index = .column .advice cfg.xA.index) :
    V1.SummarySelectorsAnchoredBy
      (Sinsemilla.HashToPoint.hashRegionSynthesisSummary ns cfg offset
        |>.toRegionShapeSummary)
      anchor := by
  unfold Sinsemilla.HashToPoint.hashRegionSynthesisSummary
  apply V1.SummarySelectorsAnchoredBy.combine
  · apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp only [Sinsemilla.HashPiece.initialYQGate_selector] at hselector
    simp at hselector
    subst selector
    rw [hq4]
    simp [physicalColumns]
  · exact chain_selectorAnchored ns cfg offset anchor hq1

private theorem merkleGate_selectorAnchored
    (cfg : Sinsemilla.Merkle.Gate.Config) (offset : ℕ)
    (anchor : ℕ → RegionColumn)
    (hq : anchor cfg.qDecompose.index = .column .advice cfg.aWhole.index) :
    V1.SummarySelectorsAnchoredBy
      (Sinsemilla.Merkle.Gate.synthesisSummary cfg offset
        |>.toRegionShapeSummary)
      anchor := by
  unfold Sinsemilla.Merkle.Gate.synthesisSummary
  apply V1.SummarySelectorsAnchoredBy.ofColumns
  intro selector hselector
  simp at hselector
  subst selector
  rw [hq]
  simp [physicalColumns]

private theorem merkleHashLayer_selectorAnchored
    (cfg : Sinsemilla.Merkle.Config)
    (lookupCfg : LookupRangeCheck.Config 10)
    (anchor : ℕ → RegionColumn)
    (hq1 : anchor cfg.sinsemilla.qS1.index =
      .column .advice cfg.sinsemilla.xA.index)
    (hq4 : anchor cfg.sinsemilla.qS4.index =
      .column .advice cfg.sinsemilla.xA.index)
    (hlookup : anchor lookupCfg.qLookup.index =
      .column .advice lookupCfg.runningSum.index)
    (hbitshift : anchor lookupCfg.qBitshift.index =
      .column .advice lookupCfg.runningSum.index)
    (hdecompose : anchor cfg.gate.qDecompose.index =
      .column .advice cfg.gate.aWhole.index) :
    V1.SelectorAnchoredBy
      (Sinsemilla.Merkle.HashLayer.synthesisSummary cfg lookupCfg).regionShapes
      anchor := by
  unfold Sinsemilla.Merkle.HashLayer.synthesisSummary
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    simp
  · apply V1.SelectorAnchoredBy.combine
    · exact witnessShortCheck_selectorAnchored 10 lookupCfg anchor hlookup hbitshift
    · apply V1.SelectorAnchoredBy.combine
      · exact witnessShortCheck_selectorAnchored 10 lookupCfg anchor hlookup hbitshift
      · apply V1.SelectorAnchoredBy.combine
        · apply V1.SelectorAnchoredBy.ofRegion
          apply V1.SummarySelectorsAnchoredBy.ofColumns
          simp
        · apply V1.SelectorAnchoredBy.combine
          · apply V1.SelectorAnchoredBy.ofRegion
            apply V1.SummarySelectorsAnchoredBy.ofColumns
            simp
          · apply V1.SelectorAnchoredBy.combine
            · apply V1.SelectorAnchoredBy.ofRegion
              exact hashToPoint_selectorAnchored _ cfg.sinsemilla 0 anchor hq1 hq4
            · apply V1.SelectorAnchoredBy.ofRegion
              exact merkleGate_selectorAnchored cfg.gate 0 anchor hdecompose

private theorem merkleLayer_selectorAnchored
    (ccfg : CondSwap.Config) (cfg : Sinsemilla.Merkle.Config)
    (lookupCfg : LookupRangeCheck.Config 10)
    (anchor : ℕ → RegionColumn)
    (hqswap : anchor ccfg.qSwap.index = .column .advice ccfg.a.index)
    (hq1 : anchor cfg.sinsemilla.qS1.index =
      .column .advice cfg.sinsemilla.xA.index)
    (hq4 : anchor cfg.sinsemilla.qS4.index =
      .column .advice cfg.sinsemilla.xA.index)
    (hlookup : anchor lookupCfg.qLookup.index =
      .column .advice lookupCfg.runningSum.index)
    (hbitshift : anchor lookupCfg.qBitshift.index =
      .column .advice lookupCfg.runningSum.index)
    (hdecompose : anchor cfg.gate.qDecompose.index =
      .column .advice cfg.gate.aWhole.index) :
    V1.SelectorAnchoredBy
      (Sinsemilla.Merkle.Layer.synthesisSummary ccfg cfg lookupCfg).regionShapes
      anchor := by
  unfold Sinsemilla.Merkle.Layer.synthesisSummary
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp at hselector
    subst selector
    rw [hqswap]
    simp [physicalColumns]
  · exact merkleHashLayer_selectorAnchored cfg lookupCfg anchor
      hq1 hq4 hlookup hbitshift hdecompose

private theorem merkle1Layer_action_selectorAnchored :
    V1.SelectorAnchoredBy
      (Sinsemilla.Merkle.Layer.synthesisSummary
        actionConfig.merkle1.condSwap actionConfig.merkle1
        actionConfig.lookupConfig).regionShapes
      (selectorAnchor actionConfig) := by
  apply merkleLayer_selectorAnchored
  all_goals unfold selectorAnchor actionConfig
  all_goals try configure_norm

private theorem merkle2Layer_action_selectorAnchored :
    V1.SelectorAnchoredBy
      (Sinsemilla.Merkle.Layer.synthesisSummary
        actionConfig.merkle2.condSwap actionConfig.merkle2
        actionConfig.lookupConfig).regionShapes
      (selectorAnchor actionConfig) := by
  apply merkleLayer_selectorAnchored
  all_goals unfold selectorAnchor actionConfig
  all_goals try configure_norm

private theorem merkle1_selectorAnchored :
    V1.SelectorAnchoredBy
      (Sinsemilla.Merkle.CalculateRoot.synthesisSummary 16
        (actionConfig.merkle1.condSwap, actionConfig.merkle1,
          actionConfig.lookupConfig)).regionShapes
      (selectorAnchor actionConfig) := by
  apply V1.SelectorAnchoredBy.replicate merkle1Layer_action_selectorAnchored

private theorem merkle2_selectorAnchored :
    V1.SelectorAnchoredBy
      (Sinsemilla.Merkle.CalculateRoot.synthesisSummary 16
        (actionConfig.merkle2.condSwap, actionConfig.merkle2,
          actionConfig.lookupConfig)).regionShapes
      (selectorAnchor actionConfig) := by
  apply V1.SelectorAnchoredBy.replicate merkle2Layer_action_selectorAnchored

private theorem fullWidthInner_selectorAnchored
    (cfg : Ecc.MulFixed.FullWidth.Config) (offset : ℕ)
    (anchor : ℕ → RegionColumn)
    (hfull : anchor cfg.qMulFixedFull.index =
      .column .advice cfg.superConfig.addConfig.xP.index)
    (hadd : anchor cfg.superConfig.addIncompleteConfig.qAddIncomplete.index =
      .column .advice cfg.superConfig.addIncompleteConfig.xP.index) :
    V1.SummarySelectorsAnchoredBy
      (Ecc.MulFixed.FullWidth.innerRegionSynthesisSummary cfg offset
        |>.toRegionShapeSummary)
      anchor := by
  intro selector hselector
  simp only [Ecc.MulFixed.FullWidth.innerRegionSynthesisSummary,
    Ecc.MulFixed.FullWidth.witnessScalarLoopSynthesisSummary,
    Ecc.MulFixed.fixedConstantsLoopSynthesisSummary,
    Ecc.MulFixed.windowChainSynthesisSummary,
    Ecc.MulFixed.processWindowSynthesisSummary,
    Ecc.AddIncomplete.synthesisSummary,
    Ecc.MulFixed.windowStepColumns,
    Ecc.MulFixed.FullWidth.fullWidthGate_selector,
    RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.combine_columns,
    RegionSynthesisSummary.repeatColumnsWithSelector_columns,
    RegionSynthesisSummary.repeatColumns_columns,
    RegionSynthesisSummary.ofColumns_columns,
    FloorPlanner.mem_unionColumns_iff] at hselector
  simp [FloorPlanner.mem_unionColumns_iff] at hselector
  rcases hselector with rfl | rfl
  · rw [hfull]
    simp only [Ecc.MulFixed.FullWidth.innerRegionSynthesisSummary,
      Ecc.MulFixed.windowChainSynthesisSummary,
      Ecc.MulFixed.processWindowSynthesisSummary,
      RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns,
      RegionSynthesisSummary.repeatColumnsWithSelector_columns,
      V1.column_mem_physicalColumns_iff,
      FloorPlanner.mem_unionColumns_iff,
      RegionSynthesisSummary.repeatColumns_columns,
      RegionSynthesisSummary.ofColumns_columns]
    simp
  · rw [hadd]
    simp only [Ecc.MulFixed.FullWidth.innerRegionSynthesisSummary,
      Ecc.MulFixed.windowChainSynthesisSummary,
      Ecc.AddIncomplete.synthesisSummary,
      Ecc.MulFixed.windowStepColumns,
      RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns,
      RegionSynthesisSummary.repeatColumnsWithSelector_columns,
      V1.column_mem_physicalColumns_iff,
      FloorPlanner.mem_unionColumns_iff,
      RegionSynthesisSummary.repeatColumns_columns,
      RegionSynthesisSummary.ofColumns_columns]
    simp [FloorPlanner.mem_unionColumns_iff]

private theorem add_selectorAnchored
    (cfg : Ecc.Add.Config) (offset : ℕ) (anchor : ℕ → RegionColumn)
    (hq : anchor cfg.qAdd.index = .column .advice cfg.xP.index) :
    V1.SummarySelectorsAnchoredBy
      (Ecc.Add.synthesisSummary cfg offset |>.toRegionShapeSummary) anchor := by
  unfold Ecc.Add.synthesisSummary
  apply V1.SummarySelectorsAnchoredBy.ofColumns
  intro selector hselector
  simp at hselector
  subst selector
  rw [hq]
  simp [physicalColumns]

private theorem fullWidth_selectorAnchored
    (cfg : Ecc.MulFixed.FullWidth.Config) (anchor : ℕ → RegionColumn)
    (hfull : anchor cfg.qMulFixedFull.index =
      .column .advice cfg.superConfig.addConfig.xP.index)
    (haddIncomplete :
      anchor cfg.superConfig.addIncompleteConfig.qAddIncomplete.index =
        .column .advice cfg.superConfig.addIncompleteConfig.xP.index)
    (hadd : anchor cfg.superConfig.addConfig.qAdd.index =
      .column .advice cfg.superConfig.addConfig.xP.index) :
    V1.SelectorAnchoredBy
      (Ecc.MulFixed.FullWidth.circuitSynthesisSummary cfg).regionShapes
      anchor := by
  unfold Ecc.MulFixed.FullWidth.circuitSynthesisSummary
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    exact fullWidthInner_selectorAnchored cfg 0 anchor hfull haddIncomplete
  · apply V1.SelectorAnchoredBy.ofRegion
    exact add_selectorAnchored cfg.superConfig.addConfig 0 anchor hadd

private theorem actionFullWidth_selectorAnchored :
    V1.SelectorAnchoredBy
      (Ecc.MulFixed.FullWidth.circuitSynthesisSummary
        actionConfig.eccConfig.mulFixedFull).regionShapes
      (selectorAnchor actionConfig) := by
  apply fullWidth_selectorAnchored
  all_goals unfold selectorAnchor actionConfig
  all_goals try configure_norm

private theorem shortInner_selectorAnchored
    (cfg : Ecc.MulFixed.Short.Config) (offset : ℕ)
    (anchor : ℕ → RegionColumn)
    (hrange : anchor cfg.superConfig.runningSumConfig.qRangeCheck.index =
      .column .advice cfg.superConfig.addConfig.xP.index)
    (hadd : anchor cfg.superConfig.addIncompleteConfig.qAddIncomplete.index =
      .column .advice cfg.superConfig.addIncompleteConfig.xP.index) :
    V1.SummarySelectorsAnchoredBy
      (Ecc.MulFixed.Short.innerRegionSynthesisSummary cfg offset
        |>.toRegionShapeSummary)
      anchor := by
  intro selector hselector
  simp only [Ecc.MulFixed.Short.innerRegionSynthesisSummary,
    DecomposeRunningSum.copyDecomposeSynthesisSummary, DecomposeRunningSum.enableLoopSynthesisSummary,
    DecomposeRunningSum.assignLoopSynthesisSummary,
    Ecc.MulFixed.fixedConstantsLoopSynthesisSummary,
    Ecc.MulFixed.windowChainSynthesisSummary,
    Ecc.MulFixed.processWindowSynthesisSummary,
    Ecc.AddIncomplete.synthesisSummary,
    Ecc.MulFixed.windowStepColumns,
    Ecc.MulFixed.coordsGate_selector,
    RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.combine_columns,
    RegionSynthesisSummary.repeatColumnsWithSelector_columns,
    RegionSynthesisSummary.repeatColumns_columns,
    RegionSynthesisSummary.ofColumns_columns,
    FloorPlanner.mem_unionColumns_iff] at hselector
  simp [FloorPlanner.mem_unionColumns_iff] at hselector
  rcases hselector with rfl | rfl
  · rw [hrange]
    simp only [Ecc.MulFixed.Short.innerRegionSynthesisSummary,
      Ecc.MulFixed.windowChainSynthesisSummary,
      Ecc.MulFixed.processWindowSynthesisSummary,
      RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns,
      RegionSynthesisSummary.repeatColumnsWithSelector_columns,
      RegionSynthesisSummary.repeatColumns_columns,
      RegionSynthesisSummary.ofColumns_columns,
      V1.column_mem_physicalColumns_iff,
      FloorPlanner.mem_unionColumns_iff]
    simp
  · rw [hadd]
    simp only [Ecc.MulFixed.Short.innerRegionSynthesisSummary,
      Ecc.MulFixed.windowChainSynthesisSummary,
      Ecc.AddIncomplete.synthesisSummary,
      Ecc.MulFixed.windowStepColumns,
      RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns,
      RegionSynthesisSummary.repeatColumnsWithSelector_columns,
      RegionSynthesisSummary.repeatColumns_columns,
      RegionSynthesisSummary.ofColumns_columns,
      V1.column_mem_physicalColumns_iff,
      FloorPlanner.mem_unionColumns_iff]
    simp [FloorPlanner.mem_unionColumns_iff]

private theorem shortMsw_selectorAnchored
    (cfg : Ecc.MulFixed.Short.Config) (anchor : ℕ → RegionColumn)
    (hadd : anchor cfg.superConfig.addConfig.qAdd.index =
      .column .advice cfg.superConfig.addConfig.xP.index)
    (hshort : anchor cfg.qMulFixedShort.index =
      .column .advice cfg.superConfig.addConfig.xP.index) :
    V1.SummarySelectorsAnchoredBy
      (Ecc.MulFixed.Short.mswRegionSynthesisSummary cfg
        |>.toRegionShapeSummary)
      anchor := by
  intro selector hselector
  simp only [Ecc.MulFixed.Short.mswRegionSynthesisSummary,
    Ecc.Add.synthesisSummary,
    RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.combine_columns,
    RegionSynthesisSummary.ofColumns_columns,
    FloorPlanner.mem_unionColumns_iff] at hselector
  simp at hselector
  have hx : .column .advice cfg.superConfig.addConfig.xP.index ∈
      physicalColumns
        (Ecc.MulFixed.Short.mswRegionSynthesisSummary cfg
          |>.toRegionShapeSummary).columns := by
    simp only [Ecc.MulFixed.Short.mswRegionSynthesisSummary,
      Ecc.Add.synthesisSummary,
      RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns,
      RegionSynthesisSummary.ofColumns_columns,
      V1.column_mem_physicalColumns_iff,
      FloorPlanner.mem_unionColumns_iff]
    simp
  rcases hselector with rfl | rfl
  · simpa only [hadd] using hx
  · simpa only [hshort] using hx

private theorem short_selectorAnchored
    (cfg : Ecc.MulFixed.Short.Config) (anchor : ℕ → RegionColumn)
    (hrange : anchor cfg.superConfig.runningSumConfig.qRangeCheck.index =
      .column .advice cfg.superConfig.addConfig.xP.index)
    (haddIncomplete :
      anchor cfg.superConfig.addIncompleteConfig.qAddIncomplete.index =
        .column .advice cfg.superConfig.addIncompleteConfig.xP.index)
    (hadd : anchor cfg.superConfig.addConfig.qAdd.index =
      .column .advice cfg.superConfig.addConfig.xP.index)
    (hshort : anchor cfg.qMulFixedShort.index =
      .column .advice cfg.superConfig.addConfig.xP.index) :
    V1.SelectorAnchoredBy
      (Ecc.MulFixed.Short.circuitSynthesisSummary cfg).regionShapes anchor := by
  unfold Ecc.MulFixed.Short.circuitSynthesisSummary
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    exact shortInner_selectorAnchored cfg 0 anchor hrange haddIncomplete
  · apply V1.SelectorAnchoredBy.ofRegion
    exact shortMsw_selectorAnchored cfg anchor hadd hshort

private theorem actionShort_selectorAnchored :
    V1.SelectorAnchoredBy
      (Ecc.MulFixed.Short.circuitSynthesisSummary
        actionConfig.eccConfig.mulFixedShort).regionShapes
      (selectorAnchor actionConfig) := by
  apply short_selectorAnchored
  all_goals unfold selectorAnchor actionConfig
  all_goals try configure_norm

private theorem actionAdd_selectorAnchored :
    V1.SummarySelectorsAnchoredBy
      (Ecc.Add.synthesisSummary actionConfig.eccConfig.add 0
        |>.toRegionShapeSummary)
      (selectorAnchor actionConfig) := by
  apply add_selectorAnchored
  unfold selectorAnchor actionConfig
  configure_norm

private theorem actionValueCommit_selectorAnchored :
    V1.SelectorAnchoredBy
      (ValueCommit.synthesisSummary
        (actionConfig.eccConfig.mulFixedShort,
          actionConfig.eccConfig.mulFixedFull,
          actionConfig.eccConfig.add)).regionShapes
      (selectorAnchor actionConfig) := by
  unfold ValueCommit.synthesisSummary
  apply V1.SelectorAnchoredBy.combine actionShort_selectorAnchored
  apply V1.SelectorAnchoredBy.combine actionFullWidth_selectorAnchored
  exact V1.SelectorAnchoredBy.ofRegion actionAdd_selectorAnchored

private theorem poseidonPermute_selectorAnchored
    (cfg : Poseidon.Config) (offset : ℕ) (anchor : ℕ → RegionColumn)
    (hfull : anchor cfg.sFull.index = .column .advice (cfg.state 0).index)
    (hpartial : anchor cfg.sPartial.index =
      .column .advice (cfg.state 0).index) :
    V1.SummarySelectorsAnchoredBy
      (Poseidon.permuteSynthesisSummary cfg offset |>.toRegionShapeSummary)
      anchor := by
  intro selector hselector
  simp only [Poseidon.permuteSynthesisSummary,
    RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.combine_columns,
    RegionSynthesisSummary.repeatColumnsWithSelector_columns,
    RegionSynthesisSummary.repeatColumns_columns,
    RegionSynthesisSummary.ofColumns_columns,
    FloorPlanner.mem_unionColumns_iff] at hselector
  simp [FloorPlanner.mem_unionColumns_iff] at hselector
  have hx : .column .advice (cfg.state 0).index ∈
      physicalColumns
        (Poseidon.permuteSynthesisSummary cfg offset
          |>.toRegionShapeSummary).columns := by
    simp only [Poseidon.permuteSynthesisSummary,
      RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns,
      RegionSynthesisSummary.repeatColumnsWithSelector_columns,
      RegionSynthesisSummary.repeatColumns_columns,
      RegionSynthesisSummary.ofColumns_columns,
      V1.column_mem_physicalColumns_iff,
      FloorPlanner.mem_unionColumns_iff]
    simp [FloorPlanner.mem_unionColumns_iff]
  rcases hselector with rfl | rfl | rfl
  · simpa only [hfull] using hx
  · simpa only [hpartial] using hx
  · simpa only [hfull] using hx

private theorem poseidonHash_selectorAnchored
    (cfg : Poseidon.Config) (anchor : ℕ → RegionColumn)
    (hpad : anchor cfg.sPadAndAdd.index =
      .column .advice (cfg.state 0).index)
    (hfull : anchor cfg.sFull.index = .column .advice (cfg.state 0).index)
    (hpartial : anchor cfg.sPartial.index =
      .column .advice (cfg.state 0).index) :
    V1.SelectorAnchoredBy (Poseidon.hashSynthesisSummary cfg).regionShapes
      anchor := by
  unfold Poseidon.hashSynthesisSummary
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    simp
  · apply V1.SelectorAnchoredBy.combine
    · apply V1.SelectorAnchoredBy.ofRegion
      unfold Poseidon.addInputRegionSynthesisSummary
      apply V1.SummarySelectorsAnchoredBy.ofColumns
      intro selector hselector
      simp at hselector
      subst selector
      rw [hpad]
      simp [physicalColumns]
    · apply V1.SelectorAnchoredBy.ofRegion
      exact poseidonPermute_selectorAnchored cfg 0 anchor hfull hpartial

private theorem actionPoseidon_selectorAnchored :
    V1.SelectorAnchoredBy
      (Poseidon.hashSynthesisSummary actionConfig.poseidonConfig).regionShapes
      (selectorAnchor actionConfig) := by
  apply poseidonHash_selectorAnchored
  all_goals unfold selectorAnchor actionConfig
  all_goals try configure_norm

private theorem addChip_selectorAnchored
    (cfg : AddChip.Config) (offset : ℕ) (anchor : ℕ → RegionColumn)
    (hq : anchor cfg.qAdd.index = .column .advice cfg.c.index) :
    V1.SummarySelectorsAnchoredBy
      (AddChip.synthesisSummary cfg offset |>.toRegionShapeSummary) anchor := by
  unfold AddChip.synthesisSummary
  apply V1.SummarySelectorsAnchoredBy.ofColumns
  intro selector hselector
  simp at hselector
  subst selector
  rw [hq]
  simp [physicalColumns]

private theorem actionAddChip_selectorAnchored :
    V1.SummarySelectorsAnchoredBy
      (AddChip.synthesisSummary actionConfig.addChipConfig 0
        |>.toRegionShapeSummary)
      (selectorAnchor actionConfig) := by
  apply addChip_selectorAnchored
  unfold selectorAnchor actionConfig
  configure_norm

private theorem baseFieldInner_selectorAnchored
    (cfg : Ecc.MulFixed.BaseFieldElem.Config) (offset : ℕ)
    (anchor : ℕ → RegionColumn)
    (hrange : anchor cfg.superConfig.runningSumConfig.qRangeCheck.index =
      .column .advice cfg.superConfig.addConfig.xP.index)
    (hadd : anchor cfg.superConfig.addIncompleteConfig.qAddIncomplete.index =
      .column .advice cfg.superConfig.addIncompleteConfig.xP.index) :
    V1.SummarySelectorsAnchoredBy
      (Ecc.MulFixed.BaseFieldElem.innerRegionSynthesisSummary cfg offset
        |>.toRegionShapeSummary)
      anchor := by
  intro selector hselector
  simp only [Ecc.MulFixed.BaseFieldElem.innerRegionSynthesisSummary,
    DecomposeRunningSum.copyDecomposeSynthesisSummary,
    DecomposeRunningSum.enableLoopSynthesisSummary,
    DecomposeRunningSum.assignLoopSynthesisSummary,
    Ecc.MulFixed.fixedConstantsLoopSynthesisSummary,
    Ecc.MulFixed.windowChainSynthesisSummary,
    Ecc.MulFixed.processWindowSynthesisSummary,
    Ecc.AddIncomplete.synthesisSummary,
    Ecc.MulFixed.windowStepColumns,
    Ecc.MulFixed.coordsGate_selector,
    RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.combine_columns,
    RegionSynthesisSummary.repeatColumnsWithSelector_columns,
    RegionSynthesisSummary.repeatColumns_columns,
    RegionSynthesisSummary.ofColumns_columns,
    FloorPlanner.mem_unionColumns_iff] at hselector
  simp [FloorPlanner.mem_unionColumns_iff] at hselector
  rcases hselector with rfl | rfl
  · rw [hrange]
    simp only [Ecc.MulFixed.BaseFieldElem.innerRegionSynthesisSummary,
      Ecc.MulFixed.windowChainSynthesisSummary,
      Ecc.MulFixed.processWindowSynthesisSummary,
      RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns,
      RegionSynthesisSummary.repeatColumnsWithSelector_columns,
      RegionSynthesisSummary.repeatColumns_columns,
      RegionSynthesisSummary.ofColumns_columns,
      V1.column_mem_physicalColumns_iff,
      FloorPlanner.mem_unionColumns_iff]
    simp [FloorPlanner.mem_unionColumns_iff]
  · rw [hadd]
    simp only [Ecc.MulFixed.BaseFieldElem.innerRegionSynthesisSummary,
      Ecc.MulFixed.windowChainSynthesisSummary,
      Ecc.AddIncomplete.synthesisSummary,
      Ecc.MulFixed.windowStepColumns,
      RegionSynthesisSummary.toRegionShapeSummary_columns,
      RegionSynthesisSummary.combine_columns,
      RegionSynthesisSummary.repeatColumnsWithSelector_columns,
      RegionSynthesisSummary.repeatColumns_columns,
      RegionSynthesisSummary.ofColumns_columns,
      V1.column_mem_physicalColumns_iff,
      FloorPlanner.mem_unionColumns_iff]
    simp [FloorPlanner.mem_unionColumns_iff]

private theorem witnessCheck13_selectorAnchored
    (cfg : LookupRangeCheck.Config 10) (anchor : ℕ → RegionColumn)
    (hlookup : anchor cfg.qLookup.index =
      .column .advice cfg.runningSum.index)
    (hrunning : anchor cfg.qRunning.index =
      .column .advice cfg.runningSum.index) :
    V1.SelectorAnchoredBy
      (Ecc.MulFixed.BaseFieldElem.witnessCheck13SynthesisSummary cfg).regionShapes
      anchor := by
  apply V1.SelectorAnchoredBy.ofRegion
  unfold LookupRangeCheck.rangeCheckSynthesisSummary
  apply V1.SummarySelectorsAnchoredBy.ofColumns
  intro selector hselector
  simp at hselector
  rcases hselector with rfl | rfl
  · rw [hlookup]
    simp [physicalColumns]
  · rw [hrunning]
    simp [physicalColumns]

private theorem baseFieldCanonicity_selectorAnchored
    (cfg : Ecc.MulFixed.BaseFieldElem.Config) (anchor : ℕ → RegionColumn)
    (hq : anchor cfg.qMulFixedBaseField.index =
      .column .advice (cfg.canonAdvices 0).index) :
    V1.SummarySelectorsAnchoredBy
      (Ecc.MulFixed.BaseFieldElem.canonicityRegionSynthesisSummary cfg
        |>.toRegionShapeSummary)
      anchor := by
  unfold Ecc.MulFixed.BaseFieldElem.canonicityRegionSynthesisSummary
  apply V1.SummarySelectorsAnchoredBy.ofColumns
  intro selector hselector
  simp at hselector
  subst selector
  rw [hq]
  simp [physicalColumns]

private theorem actionBaseField_selectorAnchored :
    V1.SelectorAnchoredBy
      (Ecc.MulFixed.BaseFieldElem.circuitSynthesisSummary
        actionConfig.eccConfig.mulFixedBaseField).regionShapes
      (selectorAnchor actionConfig) := by
  unfold Ecc.MulFixed.BaseFieldElem.circuitSynthesisSummary
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    apply baseFieldInner_selectorAnchored
    all_goals unfold selectorAnchor actionConfig
    all_goals try configure_norm
  · apply V1.SelectorAnchoredBy.combine
    · exact V1.SelectorAnchoredBy.ofRegion actionAdd_selectorAnchored
    · apply V1.SelectorAnchoredBy.combine
      · apply witnessCheck13_selectorAnchored
        all_goals unfold selectorAnchor actionConfig
        all_goals try configure_norm
      · apply V1.SelectorAnchoredBy.ofRegion
        apply baseFieldCanonicity_selectorAnchored
        unfold selectorAnchor actionConfig
        configure_norm

private theorem actionDeriveNullifier_selectorAnchored :
    V1.SelectorAnchoredBy
      (DeriveNullifier.synthesisSummary
        (actionConfig.poseidonConfig, actionConfig.addChipConfig,
          actionConfig.eccConfig.mulFixedBaseField,
          actionConfig.eccConfig.add)).regionShapes
      (selectorAnchor actionConfig) := by
  unfold DeriveNullifier.synthesisSummary
  apply V1.SelectorAnchoredBy.combine actionPoseidon_selectorAnchored
  apply V1.SelectorAnchoredBy.combine
  · exact V1.SelectorAnchoredBy.ofRegion actionAddChip_selectorAnchored
  · apply V1.SelectorAnchoredBy.combine actionBaseField_selectorAnchored
    exact V1.SelectorAnchoredBy.ofRegion actionAdd_selectorAnchored

private theorem actionSpendAuthority_selectorAnchored :
    V1.SelectorAnchoredBy
      (SpendAuthority.synthesisSummary
        (actionConfig.eccConfig.mulFixedFull,
          actionConfig.eccConfig.add)).regionShapes
      (selectorAnchor actionConfig) := by
  unfold SpendAuthority.synthesisSummary
  apply V1.SelectorAnchoredBy.combine actionFullWidth_selectorAnchored
  exact V1.SelectorAnchoredBy.ofRegion actionAdd_selectorAnchored

private theorem witnessCheck_selectorAnchored
    (K numWords : ℕ) (strict : Bool) (cfg : LookupRangeCheck.Config K)
    (anchor : ℕ → RegionColumn) (hnumWords : numWords ≠ 0)
    (hlookup : anchor cfg.qLookup.index =
      .column .advice cfg.runningSum.index)
    (hrunning : anchor cfg.qRunning.index =
      .column .advice cfg.runningSum.index) :
    V1.SelectorAnchoredBy
      (LookupRangeCheck.witnessCheckSynthesisSummary
        K numWords strict cfg).regionShapes
      anchor := by
  apply V1.SelectorAnchoredBy.ofRegion
  unfold LookupRangeCheck.rangeCheckSynthesisSummary
  apply V1.SummarySelectorsAnchoredBy.ofColumns
  intro selector hselector
  simp [hnumWords] at hselector
  rcases hselector with rfl | rfl
  · rw [hlookup]
    simp [physicalColumns, hnumWords]
  · rw [hrunning]
    simp [physicalColumns, hnumWords]

private theorem actionLookupWitness13_selectorAnchored :
    V1.SelectorAnchoredBy
      (LookupRangeCheck.witnessCheckSynthesisSummary
        10 13 false actionConfig.lookupConfig).regionShapes
      (selectorAnchor actionConfig) := by
  apply witnessCheck_selectorAnchored 10 13 false actionConfig.lookupConfig
    (selectorAnchor actionConfig) (by norm_num)
  all_goals unfold selectorAnchor actionConfig
  all_goals try configure_norm

private theorem actionLookupWitness14_selectorAnchored :
    V1.SelectorAnchoredBy
      (LookupRangeCheck.witnessCheckSynthesisSummary
        10 14 false actionConfig.lookupConfig).regionShapes
      (selectorAnchor actionConfig) := by
  apply witnessCheck_selectorAnchored 10 14 false actionConfig.lookupConfig
    (selectorAnchor actionConfig) (by norm_num)
  all_goals unfold selectorAnchor actionConfig
  all_goals try configure_norm

private theorem actionHashToPoint_selectorAnchored (ns : List ℕ) :
    V1.SelectorAnchoredBy
      (Sinsemilla.HashToPoint.hashCircuitSynthesisSummary
        ns actionConfig.sinsemilla1).regionShapes
      (selectorAnchor actionConfig) := by
  apply V1.SelectorAnchoredBy.ofRegion
  apply hashToPoint_selectorAnchored
  all_goals unfold selectorAnchor actionConfig
  all_goals try configure_norm

private theorem actionCommitDomain1_selectorAnchored (ns : List ℕ) :
    V1.SelectorAnchoredBy
      (Sinsemilla.CommitDomain.commitSynthesisSummary ns
        (actionConfig.eccConfig.mulFixedFull, actionConfig.sinsemilla1,
          actionConfig.eccConfig.add)).regionShapes
      (selectorAnchor actionConfig) := by
  unfold Sinsemilla.CommitDomain.commitSynthesisSummary
  apply V1.SelectorAnchoredBy.combine actionFullWidth_selectorAnchored
  apply V1.SelectorAnchoredBy.combine
    (actionHashToPoint_selectorAnchored ns)
  exact V1.SelectorAnchoredBy.ofRegion actionAdd_selectorAnchored

private theorem actionCommitIvkGate_selectorAnchored :
    V1.SummarySelectorsAnchoredBy
      (CommitIvk.synthesisSummary actionConfig.commitIvkConfig 0
        |>.toRegionShapeSummary)
      (selectorAnchor actionConfig) := by
  unfold CommitIvk.synthesisSummary
  apply V1.SummarySelectorsAnchoredBy.ofColumns
  intro selector hselector
  simp at hselector
  subst selector
  have hanchor :
      selectorAnchor actionConfig actionConfig.commitIvkConfig.qCommitIvk.index =
        .column .advice (actionConfig.commitIvkConfig.advices 0).index := by
    unfold selectorAnchor actionConfig
    configure_norm
  rw [hanchor]
  simp [physicalColumns]

private theorem actionCommitIvkCanonicity_selectorAnchored :
    V1.SelectorAnchoredBy
      (CommitIvk.Canonicity.circuitSynthesisSummary
        actionConfig.commitIvkConfig actionConfig.lookupConfig).regionShapes
      (selectorAnchor actionConfig) := by
  unfold CommitIvk.Canonicity.circuitSynthesisSummary
  apply V1.SelectorAnchoredBy.combine actionLookupWitness13_selectorAnchored
  apply V1.SelectorAnchoredBy.combine actionLookupWitness14_selectorAnchored
  exact V1.SelectorAnchoredBy.ofRegion actionCommitIvkGate_selectorAnchored

private theorem actionCommitIvkPieces_selectorAnchored :
    V1.SelectorAnchoredBy
      (CommitIvk.Main.synthPiecesSynthesisSummary
        { gate := actionConfig.commitIvkConfig,
          hashConfig := actionConfig.sinsemilla1,
          lookupConfig := actionConfig.lookupConfig,
          mulConfig := actionConfig.eccConfig.mulFixedFull,
          addConfig := actionConfig.eccConfig.add }).regionShapes
      (selectorAnchor actionConfig) := by
  unfold CommitIvk.Main.synthPiecesSynthesisSummary
  simp only [List.foldr_cons, List.foldr_nil]
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    simp
  · apply V1.SelectorAnchoredBy.combine
    · exact witnessShortCheck_selectorAnchored 10 actionConfig.lookupConfig
        (selectorAnchor actionConfig) (by
          unfold selectorAnchor actionConfig
          configure_norm) (by
          unfold selectorAnchor actionConfig
          configure_norm)
    · apply V1.SelectorAnchoredBy.combine
      · exact witnessShortCheck_selectorAnchored 10 actionConfig.lookupConfig
          (selectorAnchor actionConfig) (by
            unfold selectorAnchor actionConfig
            configure_norm) (by
            unfold selectorAnchor actionConfig
            configure_norm)
      · apply V1.SelectorAnchoredBy.combine
        · apply V1.SelectorAnchoredBy.ofRegion
          apply V1.SummarySelectorsAnchoredBy.ofColumns
          simp
        · apply V1.SelectorAnchoredBy.combine
          · apply V1.SelectorAnchoredBy.ofRegion
            apply V1.SummarySelectorsAnchoredBy.ofColumns
            simp
          · apply V1.SelectorAnchoredBy.combine
            · exact witnessShortCheck_selectorAnchored 10 actionConfig.lookupConfig
                (selectorAnchor actionConfig) (by
                  unfold selectorAnchor actionConfig
                  configure_norm) (by
                  unfold selectorAnchor actionConfig
                  configure_norm)
            · apply V1.SelectorAnchoredBy.combine
              · apply V1.SelectorAnchoredBy.ofRegion
                apply V1.SummarySelectorsAnchoredBy.ofColumns
                simp
              · simp [V1.SelectorAnchoredBy]

private theorem actionCommitIvk_selectorAnchored :
    V1.SelectorAnchoredBy
      (CommitIvk.Main.synthesisSummary
        { gate := actionConfig.commitIvkConfig,
          hashConfig := actionConfig.sinsemilla1,
          lookupConfig := actionConfig.lookupConfig,
          mulConfig := actionConfig.eccConfig.mulFixedFull,
          addConfig := actionConfig.eccConfig.add }).regionShapes
      (selectorAnchor actionConfig) := by
  unfold CommitIvk.Main.synthesisSummary
  apply V1.SelectorAnchoredBy.combine actionCommitIvkPieces_selectorAnchored
  apply V1.SelectorAnchoredBy.combine
    (actionCommitDomain1_selectorAnchored CommitIvk.Main.ns)
  exact actionCommitIvkCanonicity_selectorAnchored

private theorem incompleteDoubleAndAdd_selectorAnchored
    (n offset : ℕ) (cfg : Ecc.MulIncomplete.Config)
    (anchor : ℕ → RegionColumn)
    (hq1 : anchor cfg.qMul1.index = .column .advice cfg.xP.index)
    (hq2 : anchor cfg.qMul2.index = .column .advice cfg.xP.index)
    (hq3 : anchor cfg.qMul3.index = .column .advice cfg.xP.index) :
    V1.SummarySelectorsAnchoredBy
      (Ecc.MulIncomplete.doubleAndAddSynthesisSummary n cfg offset
        |>.toRegionShapeSummary)
      anchor := by
  have hxP : .column .advice cfg.xP.index ∈ physicalColumns
      (Ecc.MulIncomplete.doubleAndAddSynthesisSummary n cfg offset).columns := by
    rw [V1.column_mem_physicalColumns_iff]
    unfold Ecc.MulIncomplete.doubleAndAddSynthesisSummary
    rw [RegionSynthesisSummary.combine_columns,
      FloorPlanner.mem_unionColumns_iff]
    apply Or.inl
    rw [RegionSynthesisSummary.ofColumns_columns,
      FloorPlanner.mem_unionColumns_iff]
    exact Or.inr (by simp)
  intro selector hselector
  rw [RegionSynthesisSummary.toRegionShapeSummary_columns] at hselector
  unfold Ecc.MulIncomplete.doubleAndAddSynthesisSummary at hselector
  rw [RegionSynthesisSummary.combine_columns,
    FloorPlanner.mem_unionColumns_iff] at hselector
  rcases hselector with hselector | hselector
  · rw [RegionSynthesisSummary.ofColumns_columns,
      FloorPlanner.mem_unionColumns_iff] at hselector
    rcases hselector with hselector | hselector
    · simp at hselector
    · simp at hselector
      subst selector
      simpa only [RegionSynthesisSummary.toRegionShapeSummary_columns,
        hq1] using hxP
  · rw [RegionSynthesisSummary.combine_columns,
      FloorPlanner.mem_unionColumns_iff] at hselector
    rcases hselector with hselector | hselector
    · rw [Ecc.MulIncomplete.loopSynthesisSummary,
        RegionSynthesisSummary.repeatColumnsWithSelectorAt_columns,
        RegionSynthesisSummary.repeatColumns_columns] at hselector
      split at hselector
      · simp at hselector
      · rw [FloorPlanner.mem_unionColumns_iff] at hselector
        rcases hselector with hselector | hselector
        · simp at hselector
        · simp at hselector
          subst selector
          simpa only [RegionSynthesisSummary.toRegionShapeSummary_columns,
            hq2] using hxP
    · rw [RegionSynthesisSummary.ofColumns_columns,
        FloorPlanner.mem_unionColumns_iff] at hselector
      rcases hselector with hselector | hselector
      · simp at hselector
      · simp at hselector
        subst selector
        simpa only [RegionSynthesisSummary.toRegionShapeSummary_columns,
          hq3] using hxP

private theorem completeMul_selectorAnchored
    (numBits offset : ℕ) (cfg : Ecc.MulComplete.Config)
    (anchor : ℕ → RegionColumn)
    (hdecompose : anchor cfg.qDecompose.index =
      .column .advice cfg.addConfig.xP.index)
    (hadd : anchor cfg.addConfig.qAdd.index =
      .column .advice cfg.addConfig.xP.index) :
    V1.SummarySelectorsAnchoredBy
      (Ecc.MulComplete.circuitSynthesisSummary numBits cfg offset
        |>.toRegionShapeSummary)
      anchor := by
  cases numBits with
  | zero =>
    unfold Ecc.MulComplete.circuitSynthesisSummary
    apply V1.SummarySelectorsAnchoredBy.combine
    · apply V1.SummarySelectorsAnchoredBy.ofColumns
      simp
    · rw [Ecc.MulComplete.roundsSynthesisSummary,
        RegionSynthesisSummary.repeatColumnsWithSelectorPattern_toRegionShapeSummary,
        RegionSynthesisSummary.repeatColumns]
      exact V1.SummarySelectorsAnchoredBy.empty anchor
  | succ numBits =>
    unfold Ecc.MulComplete.circuitSynthesisSummary
    apply V1.SummarySelectorsAnchoredBy.combine
    · apply V1.SummarySelectorsAnchoredBy.ofColumns
      simp
    · unfold Ecc.MulComplete.roundsSynthesisSummary
      rw [RegionSynthesisSummary.repeatColumnsWithSelectorPattern_toRegionShapeSummary]
      rw [RegionSynthesisSummary.repeatColumns]
      simp only [Nat.succ_ne_zero, ↓reduceIte]
      apply V1.SummarySelectorsAnchoredBy.ofColumns
      intro selector hselector
      simp [Ecc.MulComplete.roundColumns] at hselector
      rcases hselector with hselector | hselector
      · subst selector
        rw [hdecompose]
        simp [Ecc.MulComplete.roundColumns, physicalColumns]
      · subst selector
        rw [hadd]
        simp [Ecc.MulComplete.roundColumns, physicalColumns]

private theorem actionVariableMulMain_selectorAnchored :
    V1.SummarySelectorsAnchoredBy
      (Ecc.Mul.mainCircuitSynthesisSummary actionConfig.eccConfig.mul
        |>.toRegionShapeSummary)
      (selectorAnchor actionConfig) := by
  unfold Ecc.Mul.mainCircuitSynthesisSummary
  apply V1.SummarySelectorsAnchoredBy.combine actionAdd_selectorAnchored
  apply V1.SummarySelectorsAnchoredBy.combine
  · apply V1.SummarySelectorsAnchoredBy.ofColumns
    simp
  · apply V1.SummarySelectorsAnchoredBy.combine
    · apply incompleteDoubleAndAdd_selectorAnchored
      all_goals unfold selectorAnchor actionConfig
      all_goals configure_norm
    · apply V1.SummarySelectorsAnchoredBy.combine
      · apply incompleteDoubleAndAdd_selectorAnchored
        all_goals unfold selectorAnchor actionConfig
        all_goals configure_norm
      · apply V1.SummarySelectorsAnchoredBy.combine
        · apply completeMul_selectorAnchored
          all_goals unfold selectorAnchor actionConfig
          all_goals configure_norm
        · apply V1.SummarySelectorsAnchoredBy.combine
          · apply V1.SummarySelectorsAnchoredBy.ofColumns
            intro selector hselector
            simp at hselector
            subst selector
            unfold selectorAnchor
            rw [actionConfig_qMulLsb, actionConfig_advice0,
              actionConfig_mulAddXP]
            norm_num [physicalColumns]
          · exact actionAdd_selectorAnchored

private theorem copyCheck_selectorAnchored
    (K numWords : ℕ) (strict : Bool) (cfg : LookupRangeCheck.Config K)
    (anchor : ℕ → RegionColumn) (hnumWords : numWords ≠ 0)
    (hlookup : anchor cfg.qLookup.index =
      .column .advice cfg.runningSum.index)
    (hrunning : anchor cfg.qRunning.index =
      .column .advice cfg.runningSum.index) :
    V1.SelectorAnchoredBy
      (LookupRangeCheck.copyCheckSynthesisSummary
        K numWords strict cfg).regionShapes
      anchor := by
  simpa only [LookupRangeCheck.copyCheckSynthesisSummary,
    LookupRangeCheck.witnessCheckSynthesisSummary] using
    witnessCheck_selectorAnchored K numWords strict cfg anchor hnumWords
      hlookup hrunning

private theorem actionMulOverflow_selectorAnchored :
    V1.SelectorAnchoredBy
      (Ecc.MulOverflow.circuitSynthesisSummary 10
        actionConfig.eccConfig.mul.overflowConfig).regionShapes
      (selectorAnchor actionConfig) := by
  unfold Ecc.MulOverflow.circuitSynthesisSummary
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    simp
  · apply V1.SelectorAnchoredBy.combine
    · apply copyCheck_selectorAnchored 10 (Ecc.MulOverflow.numWords 10)
        false actionConfig.eccConfig.mul.overflowConfig.lookupConfig
        (selectorAnchor actionConfig)
      · norm_num [Ecc.MulOverflow.numWords]
      all_goals unfold selectorAnchor actionConfig
      all_goals configure_norm
    · apply V1.SelectorAnchoredBy.ofRegion
      apply V1.SummarySelectorsAnchoredBy.ofColumns
      intro selector hselector
      simp at hselector
      subst selector
      have hanchor :
          selectorAnchor actionConfig
              actionConfig.eccConfig.mul.overflowConfig.qOverflow.index =
            .column .advice
              actionConfig.eccConfig.mul.overflowConfig.adv0.index := by
        unfold selectorAnchor actionConfig
        configure_norm
      rw [hanchor]
      simp [physicalColumns]

private theorem actionVariableMul_selectorAnchored :
    V1.SelectorAnchoredBy
      (Ecc.Mul.mulSynthesisSummary actionConfig.eccConfig.mul).regionShapes
      (selectorAnchor actionConfig) := by
  unfold Ecc.Mul.mulSynthesisSummary
  apply V1.SelectorAnchoredBy.combine
  · exact V1.SelectorAnchoredBy.ofRegion
      actionVariableMulMain_selectorAnchored
  · exact actionMulOverflow_selectorAnchored

private theorem pointNonId_selectorAnchored
    (cfg : Ecc.WitnessPoint.Config) (offset : ℕ)
    (anchor : ℕ → RegionColumn)
    (hq : anchor cfg.qPointNonId.index =
      .column .advice cfg.x.index) :
    V1.SummarySelectorsAnchoredBy
      (Ecc.WitnessPoint.pointNonIdSynthesisSummary cfg offset
        |>.toRegionShapeSummary)
      anchor := by
  unfold Ecc.WitnessPoint.pointNonIdSynthesisSummary
  apply V1.SummarySelectorsAnchoredBy.ofColumns
  intro selector hselector
  simp at hselector
  subst selector
  rw [hq]
  simp [physicalColumns]

private theorem actionAddressIntegrity_selectorAnchored :
    V1.SelectorAnchoredBy
      (AddressIntegrity.synthesisSummary
        (actionConfig.eccConfig.mul,
          actionConfig.eccConfig.witnessPoint)).regionShapes
      (selectorAnchor actionConfig) := by
  unfold AddressIntegrity.synthesisSummary
  apply V1.SelectorAnchoredBy.combine actionVariableMul_selectorAnchored
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    apply pointNonId_selectorAnchored
    unfold selectorAnchor actionConfig
    configure_norm
  · exact V1.SelectorAnchoredBy.ofRegion
      (V1.SummarySelectorsAnchoredBy.empty (selectorAnchor actionConfig))

private theorem loadPrivate_selectorAnchored (column : Column .advice) :
    V1.SelectorAnchoredBy
      (Circuit.loadPrivateSynthesisSummary column).regionShapes
      (selectorAnchor actionConfig) := by
  unfold Circuit.loadPrivateSynthesisSummary
  apply V1.SelectorAnchoredBy.ofRegion
  apply V1.SummarySelectorsAnchoredBy.ofColumns
  simp

private theorem empty_selectorAnchored (anchor : ℕ → RegionColumn) :
    V1.SelectorAnchoredBy ({} : SynthesisSummary).regionShapes anchor := by
  simp [V1.SelectorAnchoredBy]

private theorem emptyRegion_selectorAnchored (anchor : ℕ → RegionColumn) :
    V1.SelectorAnchoredBy
      (SynthesisSummary.ofRegion ({} : RegionSynthesisSummary)).regionShapes
      anchor :=
  V1.SelectorAnchoredBy.ofRegion
    (V1.SummarySelectorsAnchoredBy.empty anchor)

private theorem instanceRow_selectorAnchored (row : ℕ)
    (anchor : ℕ → RegionColumn) :
    V1.SelectorAnchoredBy
      (SynthesisSummary.ofInstanceRow row).regionShapes anchor := by
  rw [SynthesisSummary.ofInstanceRow_regionShapes]
  trivial

private theorem selectorAnchoredBy_foldr_combine
    {summaries : List SynthesisSummary} {anchor : ℕ → RegionColumn}
    (hsummaries : summaries.Forall fun summary =>
      V1.SelectorAnchoredBy summary.regionShapes anchor) :
    V1.SelectorAnchoredBy
      (summaries.foldr SynthesisSummary.combine {}).regionShapes anchor := by
  induction summaries with
  | nil => exact empty_selectorAnchored anchor
  | cons summary rest inductionHypothesis =>
      rw [List.forall_cons] at hsummaries
      exact hsummaries.1.combine (inductionHypothesis hsummaries.2)

private theorem actionSynthChecks_selectorAnchored :
    V1.SelectorAnchoredBy
      (Circuit.synthChecksSynthesisSummary actionConfig).regionShapes
      (selectorAnchor actionConfig) := by
  unfold Circuit.synthChecksSynthesisSummary
  apply selectorAnchoredBy_foldr_combine
  simp only [List.forall_cons, List.forall_nil, and_true]
  exact ⟨merkle1_selectorAnchored, merkle2_selectorAnchored,
    loadPrivate_selectorAnchored _, loadPrivate_selectorAnchored _,
    actionValueCommit_selectorAnchored,
    instanceRow_selectorAnchored _ (selectorAnchor actionConfig),
    instanceRow_selectorAnchored _ (selectorAnchor actionConfig),
    actionDeriveNullifier_selectorAnchored,
    instanceRow_selectorAnchored _ (selectorAnchor actionConfig),
    actionSpendAuthority_selectorAnchored,
    instanceRow_selectorAnchored _ (selectorAnchor actionConfig),
    instanceRow_selectorAnchored _ (selectorAnchor actionConfig),
    actionCommitIvk_selectorAnchored,
    actionAddressIntegrity_selectorAnchored⟩

private theorem point_selectorAnchored
    (cfg : Ecc.WitnessPoint.Config) (offset : ℕ)
    (anchor : ℕ → RegionColumn)
    (hq : anchor cfg.qPoint.index = .column .advice cfg.x.index) :
    V1.SummarySelectorsAnchoredBy
      (Ecc.WitnessPoint.pointSynthesisSummary cfg offset
        |>.toRegionShapeSummary)
      anchor := by
  unfold Ecc.WitnessPoint.pointSynthesisSummary
  apply V1.SummarySelectorsAnchoredBy.ofColumns
  intro selector hselector
  simp at hselector
  subst selector
  rw [hq]
  simp [physicalColumns]

private theorem actionSynthWitness_selectorAnchored :
    V1.SelectorAnchoredBy
      (Circuit.synthWitnessSynthesisSummary actionConfig).regionShapes
      (selectorAnchor actionConfig) := by
  unfold Circuit.synthWitnessSynthesisSummary
  simp only [List.foldr_cons, List.foldr_nil]
  apply V1.SelectorAnchoredBy.combine
  · unfold Sinsemilla.loadSynthesisSummary
    exact empty_selectorAnchored (selectorAnchor actionConfig)
  apply V1.SelectorAnchoredBy.combine (loadPrivate_selectorAnchored _)
  apply V1.SelectorAnchoredBy.combine (loadPrivate_selectorAnchored _)
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    apply point_selectorAnchored
    unfold selectorAnchor actionConfig
    configure_norm
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    apply pointNonId_selectorAnchored
    unfold selectorAnchor actionConfig
    configure_norm
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    apply pointNonId_selectorAnchored
    unfold selectorAnchor actionConfig
    configure_norm
  apply V1.SelectorAnchoredBy.combine (loadPrivate_selectorAnchored _)
  apply V1.SelectorAnchoredBy.combine (loadPrivate_selectorAnchored _)
  apply V1.SelectorAnchoredBy.combine (loadPrivate_selectorAnchored _)
  exact empty_selectorAnchored (selectorAnchor actionConfig)

private theorem actionCrossAddress_selectorAnchored :
    V1.SelectorAnchoredBy
      (Circuit.synthCrossAddressChecksSynthesisSummary actionConfig).regionShapes
      (selectorAnchor actionConfig) := by
  unfold Circuit.synthCrossAddressChecksSynthesisSummary
  apply V1.SelectorAnchoredBy.ofRegion
  intro selector hselector
  simp only [RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.repeatColumnsWithSelector_columns,
    RegionSynthesisSummary.repeatColumns_columns] at hselector
  simp [FloorPlanner.mem_unionColumns_iff,
    Circuit.crossAddressColumns] at hselector
  subst selector
  have hanchor : selectorAnchor actionConfig actionConfig.qOrchard.index =
      .column .advice (actionConfig.advices 0).index := by
    unfold selectorAnchor
    rw [actionConfig_qOrchard]
    norm_num
  rw [hanchor]
  simp [RegionSynthesisSummary.toRegionShapeSummary_columns,
    RegionSynthesisSummary.repeatColumnsWithSelector_columns,
    RegionSynthesisSummary.repeatColumns_columns,
    FloorPlanner.mem_unionColumns_iff, Circuit.crossAddressColumns,
    physicalColumns]

private theorem witnessCheckDecomposed_selectorAnchored
    (cfg : LookupRangeCheck.Config 10) (anchor : ℕ → RegionColumn)
    (hlookup : anchor cfg.qLookup.index =
      .column .advice cfg.runningSum.index)
    (hrunning : anchor cfg.qRunning.index =
      .column .advice cfg.runningSum.index) :
    V1.SelectorAnchoredBy
      (LookupRangeCheck.witnessCheckDecomposedSynthesisSummary cfg).regionShapes
      anchor := by
  apply V1.SelectorAnchoredBy.ofRegion
  apply V1.SummarySelectorsAnchoredBy.combine
  · apply V1.SummarySelectorsAnchoredBy.ofColumns
    simp
  · unfold LookupRangeCheck.rangeCheckAtDecomposedSynthesisSummary
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp at hselector
    rcases hselector with rfl | rfl
    · rw [hlookup]
      simp [physicalColumns]
    · rw [hrunning]
      simp [physicalColumns]

private theorem yCanonicity_selectorAnchored
    (gcfg : NoteCommit.YCanonicity.Config)
    (lcfg : LookupRangeCheck.Config 10) (anchor : ℕ → RegionColumn)
    (hlookup : anchor lcfg.qLookup.index =
      .column .advice lcfg.runningSum.index)
    (hrunning : anchor lcfg.qRunning.index =
      .column .advice lcfg.runningSum.index)
    (hbitshift : anchor lcfg.qBitshift.index =
      .column .advice lcfg.runningSum.index)
    (hy : anchor gcfg.qYCanon.index =
      .column .advice (gcfg.advices 5).index) :
    V1.SelectorAnchoredBy
      (NoteCommit.YCanonicityCheck.synthesisSummary gcfg lcfg).regionShapes
      anchor := by
  unfold NoteCommit.YCanonicityCheck.synthesisSummary
  apply V1.SelectorAnchoredBy.combine
    (witnessShortCheck_selectorAnchored 10 lcfg anchor hlookup hbitshift)
  apply V1.SelectorAnchoredBy.combine
    (witnessShortCheck_selectorAnchored 10 lcfg anchor hlookup hbitshift)
  apply V1.SelectorAnchoredBy.combine
    (witnessCheckDecomposed_selectorAnchored lcfg anchor hlookup hrunning)
  apply V1.SelectorAnchoredBy.combine
    (witnessCheck_selectorAnchored 10 13 false lcfg anchor (by norm_num)
      hlookup hrunning)
  apply V1.SelectorAnchoredBy.ofRegion
  unfold NoteCommit.YCanonicity.synthesisSummary
  apply V1.SummarySelectorsAnchoredBy.ofColumns
  intro selector hselector
  simp at hselector
  subst selector
  rw [hy]
  simp [physicalColumns]

private theorem actionYCanonicityOld_selectorAnchored :
    V1.SelectorAnchoredBy
      (NoteCommit.YCanonicityCheck.synthesisSummary
        actionConfig.noteCommitOld.y actionConfig.lookupConfig).regionShapes
      (selectorAnchor actionConfig) := by
  apply yCanonicity_selectorAnchored
  all_goals unfold selectorAnchor actionConfig
  all_goals configure_norm

private theorem actionYCanonicityNew_selectorAnchored :
    V1.SelectorAnchoredBy
      (NoteCommit.YCanonicityCheck.synthesisSummary
        actionConfig.noteCommitNew.y actionConfig.lookupConfig).regionShapes
      (selectorAnchor actionConfig) := by
  apply yCanonicity_selectorAnchored
  all_goals unfold selectorAnchor actionConfig
  all_goals configure_norm

private theorem actionCommitDomain2_selectorAnchored :
    V1.SelectorAnchoredBy
      (Sinsemilla.CommitDomain.commitSynthesisSummary NoteCommit.Main.ns
        (actionConfig.eccConfig.mulFixedFull, actionConfig.sinsemilla2,
          actionConfig.eccConfig.add)).regionShapes
      (selectorAnchor actionConfig) := by
  unfold Sinsemilla.CommitDomain.commitSynthesisSummary
  apply V1.SelectorAnchoredBy.combine actionFullWidth_selectorAnchored
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    apply hashToPoint_selectorAnchored
    all_goals unfold selectorAnchor actionConfig
    all_goals configure_norm
  exact V1.SelectorAnchoredBy.ofRegion actionAdd_selectorAnchored

private theorem notePieces_selectorAnchored
    (gates : NoteCommit.Config) (cfg : Sinsemilla.HashPiece.Config) :
    V1.SelectorAnchoredBy
      (NoteCommit.Main.synthPiecesSynthesisSummary
        { gates := gates, hashConfig := cfg,
          lookupConfig := actionConfig.lookupConfig,
          mulConfig := actionConfig.eccConfig.mulFixedFull,
          addConfig := actionConfig.eccConfig.add }).regionShapes
      (selectorAnchor actionConfig) := by
  unfold NoteCommit.Main.synthPiecesSynthesisSummary
  simp only [List.foldr_cons, List.foldr_nil]
  let piece : V1.SelectorAnchoredBy
      (Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary cfg).regionShapes
      (selectorAnchor actionConfig) := by
    unfold Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary
    apply V1.SelectorAnchoredBy.ofRegion
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    simp
  let short := witnessShortCheck_selectorAnchored 10 actionConfig.lookupConfig
    (selectorAnchor actionConfig) (by
      unfold selectorAnchor actionConfig
      configure_norm) (by
      unfold selectorAnchor actionConfig
      configure_norm)
  apply V1.SelectorAnchoredBy.combine piece
  apply V1.SelectorAnchoredBy.combine short
  apply V1.SelectorAnchoredBy.combine short
  apply V1.SelectorAnchoredBy.combine piece
  apply V1.SelectorAnchoredBy.combine piece
  apply V1.SelectorAnchoredBy.combine short
  apply V1.SelectorAnchoredBy.combine piece
  apply V1.SelectorAnchoredBy.combine short
  apply V1.SelectorAnchoredBy.combine short
  apply V1.SelectorAnchoredBy.combine piece
  apply V1.SelectorAnchoredBy.combine piece
  apply V1.SelectorAnchoredBy.combine short
  apply V1.SelectorAnchoredBy.combine piece
  apply V1.SelectorAnchoredBy.combine short
  apply V1.SelectorAnchoredBy.combine piece
  exact empty_selectorAnchored (selectorAnchor actionConfig)

private theorem noteChecksOld_selectorAnchored :
    V1.SelectorAnchoredBy
      (NoteCommit.Main.synthChecksSynthesisSummary
        { gates := actionConfig.noteCommitOld,
          hashConfig := actionConfig.sinsemilla1,
          lookupConfig := actionConfig.lookupConfig,
          mulConfig := actionConfig.eccConfig.mulFixedFull,
          addConfig := actionConfig.eccConfig.add }).regionShapes
      (selectorAnchor actionConfig) := by
  unfold NoteCommit.Main.synthChecksSynthesisSummary
  simp only [List.foldr_cons, List.foldr_nil]
  apply V1.SelectorAnchoredBy.combine actionYCanonicityOld_selectorAnchored
  apply V1.SelectorAnchoredBy.combine actionYCanonicityOld_selectorAnchored
  apply V1.SelectorAnchoredBy.combine
    (actionCommitDomain1_selectorAnchored NoteCommit.Main.ns)
  apply V1.SelectorAnchoredBy.combine actionLookupWitness13_selectorAnchored
  apply V1.SelectorAnchoredBy.combine actionLookupWitness14_selectorAnchored
  apply V1.SelectorAnchoredBy.combine actionLookupWitness14_selectorAnchored
  apply V1.SelectorAnchoredBy.combine actionLookupWitness13_selectorAnchored
  exact empty_selectorAnchored (selectorAnchor actionConfig)

private theorem noteChecksNew_selectorAnchored :
    V1.SelectorAnchoredBy
      (NoteCommit.Main.synthChecksSynthesisSummary
        { gates := actionConfig.noteCommitNew,
          hashConfig := actionConfig.sinsemilla2,
          lookupConfig := actionConfig.lookupConfig,
          mulConfig := actionConfig.eccConfig.mulFixedFull,
          addConfig := actionConfig.eccConfig.add }).regionShapes
      (selectorAnchor actionConfig) := by
  unfold NoteCommit.Main.synthChecksSynthesisSummary
  simp only [List.foldr_cons, List.foldr_nil]
  apply V1.SelectorAnchoredBy.combine actionYCanonicityNew_selectorAnchored
  apply V1.SelectorAnchoredBy.combine actionYCanonicityNew_selectorAnchored
  apply V1.SelectorAnchoredBy.combine actionCommitDomain2_selectorAnchored
  apply V1.SelectorAnchoredBy.combine actionLookupWitness13_selectorAnchored
  apply V1.SelectorAnchoredBy.combine actionLookupWitness14_selectorAnchored
  apply V1.SelectorAnchoredBy.combine actionLookupWitness14_selectorAnchored
  apply V1.SelectorAnchoredBy.combine actionLookupWitness13_selectorAnchored
  exact empty_selectorAnchored (selectorAnchor actionConfig)

private theorem noteGates_selectorAnchored
    (cfg : NoteCommit.Config) (anchor : ℕ → RegionColumn)
    (hb : anchor cfg.b.qNotecommitB.index =
      .column .advice cfg.b.colL.index)
    (hd : anchor cfg.d.qNotecommitD.index =
      .column .advice cfg.d.colL.index)
    (he : anchor cfg.e.qNotecommitE.index =
      .column .advice cfg.e.colL.index)
    (hg : anchor cfg.g.qNotecommitG.index =
      .column .advice cfg.g.colL.index)
    (hh : anchor cfg.h.qNotecommitH.index =
      .column .advice cfg.h.colL.index)
    (hgd : anchor cfg.gd.qNotecommitGd.index =
      .column .advice cfg.gd.colL.index)
    (hpkd : anchor cfg.pkd.qNotecommitPkd.index =
      .column .advice cfg.pkd.colL.index)
    (hvalue : anchor cfg.value.qNotecommitValue.index =
      .column .advice cfg.value.colL.index)
    (hrho : anchor cfg.rho.qNotecommitRho.index =
      .column .advice cfg.rho.colL.index)
    (hpsi : anchor cfg.psi.qNotecommitPsi.index =
      .column .advice cfg.psi.colL.index) :
    V1.SelectorAnchoredBy
      (NoteCommit.Main.synthGatesSynthesisSummary
        { gates := cfg, hashConfig := actionConfig.sinsemilla1,
          lookupConfig := actionConfig.lookupConfig,
          mulConfig := actionConfig.eccConfig.mulFixedFull,
          addConfig := actionConfig.eccConfig.add }).regionShapes
      anchor := by
  unfold NoteCommit.Main.synthGatesSynthesisSummary
  simp only [List.foldr_cons, List.foldr_nil]
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    unfold NoteCommit.DecomposeB.synthesisSummary
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp at hselector
    subst selector
    rw [hb]
    simp [physicalColumns]
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    unfold NoteCommit.DecomposeD.synthesisSummary
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp at hselector
    subst selector
    rw [hd]
    simp [physicalColumns]
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    unfold NoteCommit.DecomposeE.synthesisSummary
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp at hselector
    subst selector
    rw [he]
    simp [physicalColumns]
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    unfold NoteCommit.DecomposeG.synthesisSummary
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp at hselector
    subst selector
    rw [hg]
    simp [physicalColumns]
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    unfold NoteCommit.DecomposeH.synthesisSummary
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp at hselector
    subst selector
    rw [hh]
    simp [physicalColumns]
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    unfold NoteCommit.GdCanonicity.synthesisSummary
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp at hselector
    subst selector
    rw [hgd]
    simp [physicalColumns]
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    unfold NoteCommit.PkdCanonicity.synthesisSummary
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp at hselector
    subst selector
    rw [hpkd]
    simp [physicalColumns]
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    unfold NoteCommit.ValueCanonicity.synthesisSummary
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp at hselector
    subst selector
    rw [hvalue]
    simp [physicalColumns]
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    unfold NoteCommit.RhoCanonicity.synthesisSummary
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp at hselector
    subst selector
    rw [hrho]
    simp [physicalColumns]
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    unfold NoteCommit.PsiCanonicity.synthesisSummary
    apply V1.SummarySelectorsAnchoredBy.ofColumns
    intro selector hselector
    simp at hselector
    subst selector
    rw [hpsi]
    simp [physicalColumns]
  exact empty_selectorAnchored anchor

private theorem noteGatesOld_selectorAnchored :
    V1.SelectorAnchoredBy
      (NoteCommit.Main.synthGatesSynthesisSummary
        { gates := actionConfig.noteCommitOld,
          hashConfig := actionConfig.sinsemilla1,
          lookupConfig := actionConfig.lookupConfig,
          mulConfig := actionConfig.eccConfig.mulFixedFull,
          addConfig := actionConfig.eccConfig.add }).regionShapes
      (selectorAnchor actionConfig) := by
  apply noteGates_selectorAnchored
  all_goals unfold selectorAnchor actionConfig
  all_goals configure_norm

private theorem noteGatesNew_selectorAnchored :
    V1.SelectorAnchoredBy
      (NoteCommit.Main.synthGatesSynthesisSummary
        { gates := actionConfig.noteCommitNew,
          hashConfig := actionConfig.sinsemilla2,
          lookupConfig := actionConfig.lookupConfig,
          mulConfig := actionConfig.eccConfig.mulFixedFull,
          addConfig := actionConfig.eccConfig.add }).regionShapes
      (selectorAnchor actionConfig) := by
  apply noteGates_selectorAnchored
  all_goals unfold selectorAnchor actionConfig
  all_goals configure_norm

private theorem noteOld_selectorAnchored :
    V1.SelectorAnchoredBy
      (NoteCommit.Main.synthesisSummary
        { gates := actionConfig.noteCommitOld,
          hashConfig := actionConfig.sinsemilla1,
          lookupConfig := actionConfig.lookupConfig,
          mulConfig := actionConfig.eccConfig.mulFixedFull,
          addConfig := actionConfig.eccConfig.add }).regionShapes
      (selectorAnchor actionConfig) := by
  unfold NoteCommit.Main.synthesisSummary
  apply V1.SelectorAnchoredBy.combine
    (notePieces_selectorAnchored actionConfig.noteCommitOld
      actionConfig.sinsemilla1)
  apply V1.SelectorAnchoredBy.combine noteChecksOld_selectorAnchored
    noteGatesOld_selectorAnchored

private theorem noteNew_selectorAnchored :
    V1.SelectorAnchoredBy
      (NoteCommit.Main.synthesisSummary
        { gates := actionConfig.noteCommitNew,
          hashConfig := actionConfig.sinsemilla2,
          lookupConfig := actionConfig.lookupConfig,
          mulConfig := actionConfig.eccConfig.mulFixedFull,
          addConfig := actionConfig.eccConfig.add }).regionShapes
      (selectorAnchor actionConfig) := by
  unfold NoteCommit.Main.synthesisSummary
  apply V1.SelectorAnchoredBy.combine
    (notePieces_selectorAnchored actionConfig.noteCommitNew
      actionConfig.sinsemilla2)
  apply V1.SelectorAnchoredBy.combine noteChecksNew_selectorAnchored
    noteGatesNew_selectorAnchored

private theorem orchardChecks_selectorAnchored :
    V1.SelectorAnchoredBy
      (Circuit.orchardChecksSynthesisSummary actionConfig).regionShapes
      (selectorAnchor actionConfig) := by
  unfold Circuit.orchardChecksSynthesisSummary
  apply V1.SelectorAnchoredBy.ofRegion
  unfold Circuit.orchardChecksRegionSynthesisSummary
  apply V1.SummarySelectorsAnchoredBy.ofColumns
  intro selector hselector
  simp at hselector
  subst selector
  have hanchor : selectorAnchor actionConfig actionConfig.qOrchard.index =
      .column .advice (actionConfig.advices 0).index := by
    unfold selectorAnchor
    rw [actionConfig_qOrchard]
    norm_num
  rw [hanchor]
  simp [physicalColumns]

private theorem actionSynthNotes_selectorAnchored :
    V1.SelectorAnchoredBy
      (Circuit.synthNotesSynthesisSummary actionConfig).regionShapes
      (selectorAnchor actionConfig) := by
  unfold Circuit.synthNotesSynthesisSummary
  simp only [List.foldr_cons, List.foldr_nil]
  apply V1.SelectorAnchoredBy.combine noteOld_selectorAnchored
  apply V1.SelectorAnchoredBy.combine
    (emptyRegion_selectorAnchored (selectorAnchor actionConfig))
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    apply pointNonId_selectorAnchored
    unfold selectorAnchor actionConfig
    configure_norm
  apply V1.SelectorAnchoredBy.combine
  · apply V1.SelectorAnchoredBy.ofRegion
    apply pointNonId_selectorAnchored
    unfold selectorAnchor actionConfig
    configure_norm
  apply V1.SelectorAnchoredBy.combine (loadPrivate_selectorAnchored _)
  apply V1.SelectorAnchoredBy.combine noteNew_selectorAnchored
  apply V1.SelectorAnchoredBy.combine orchardChecks_selectorAnchored
  exact empty_selectorAnchored (selectorAnchor actionConfig)

private theorem actionMainPost_selectorAnchored :
    V1.SelectorAnchoredBy
      (Circuit.mainPostSynthesisSummary actionConfig).regionShapes
      (selectorAnchor actionConfig) := by
  unfold Circuit.mainPostSynthesisSummary
  apply V1.SelectorAnchoredBy.combine
  · unfold Circuit.synthesizeBaseSynthesisSummary
    apply V1.SelectorAnchoredBy.combine actionSynthWitness_selectorAnchored
    apply V1.SelectorAnchoredBy.combine actionSynthChecks_selectorAnchored
      actionSynthNotes_selectorAnchored
  · exact actionCrossAddress_selectorAnchored

/-- Every selector in the reduced Action synthesis summary is anchored to the column selected by
`selectorAnchor`. -/
theorem actionSelectorAnchored :
    V1.SelectorAnchoredBy actionSynthesisSummary.regionShapes
      (selectorAnchor actionConfig) := by
  simpa only [actionSynthesisSummary] using actionMainPost_selectorAnchored

/-- Reduces the Action circuit's physical V1 placement endpoint to the endpoint computed from its
selector-free, consensus-sorted region summaries. -/
theorem actionPlacementEnd_eq :
    V1.placementEnd actionOperations =
      V1.slotSummaryEndFrom actionSortedPlannerSummaries ∅ := by
  apply V1.placementEnd_eq_slotSummaryEndFrom_withoutSelectors
    actionOperations (selectorAnchor actionConfig)
  rw [← actionSynthesisSummary_eq_operations]
  exact actionSelectorAnchored

end Zcash.Circuits.Action
