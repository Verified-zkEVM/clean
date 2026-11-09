import Clean.Ironwood.Action.Shape.PlannerTraceBridge

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

/-- The compact exact trace computes every sorted start row, including the two
zero-row regions at the end. -/
theorem actionExactSortedPlannerSummaries_starts_eq :
    (slotShapeSummariesFrom actionExactSortedPlannerSummaries
      (∅ : CircuitAllocations)).1 = actionExactSortedStarts := by
  have hrepresents :
      V1.AllocationView.empty.Represents (∅ : CircuitAllocations) := by
    intro column
    simp [V1.AllocationView.empty]
  have hvalid : V1.AllocationView.empty.Valid := by
    intro column
    simp [V1.AllocationView.empty, Allocations.Valid]
  have htrace := V1.PlannedSummaryBlock.slotShapeSummaryBlocks_eq
    actionExactPlannerTrace (∅ : CircuitAllocations)
    V1.AllocationView.empty hrepresents hvalid
    actionExactPlannerTrace_lawful
  unfold actionExactSortedPlannerSummaries actionExactSortedStarts
  rw [slotShapeSummariesFrom_append,
    V1.PlannedSummaryBlock.slotShapeSummariesFrom_summaries]
  simp only
  rw [htrace.1, slotShapeSummariesFrom_replicate_empty]
  simp

/-- The consensus-sorted Action region stream ends exactly at row 1779. -/
theorem actionSortedPlannerSummaries_endpoint :
    (V1.slotSummaryStateFromWith 0 actionSortedPlannerSummaries
      (∅ : CircuitAllocations)).1 = 1779 := by
  rw [V1.slotSummaryStateFromWith_eq_of_forall₂_placementEquivalent
    actionSortedPlannerSummaries_equivalent_exact]
  unfold actionExactSortedPlannerSummaries
  rw [V1.slotSummaryStateFromWith_append]
  rw [V1.slotSummaryStateFromWith_replicate_empty]
  have hTrace := V1.PlannedSummaryBlock.slotSummaryStateFromWith_summaries_result
    actionExactPlannerTrace 0 (∅ : CircuitAllocations)
    V1.AllocationView.empty V1.AllocationView.empty_represents_empty
    V1.AllocationView.empty_valid actionExactPlannerTrace_lawful
  rw [hTrace.1, actionExactPlannerTrace_endpoint]

theorem actionPlacementEnd_eq_1779 :
    V1.placementEnd actionOperations = 1779 := by
  rw [actionPlacementEnd_eq]
  unfold V1.slotSummaryEndFrom
  rw [← V1.slotSummaryStateFromWith_fst]
  exact actionSortedPlannerSummaries_endpoint

/-- The Action circuit's reduced synthesis summary records the exact table endpoint. -/
theorem actionSynthesisSummary_tableRowExtent_eq :
    actionSynthesisSummary.tableRowExtent = 1025 := by
  unfold actionSynthesisSummary Circuit.mainPostSynthesisSummary
    Circuit.synthesizeBaseSynthesisSummary
  simp only [synthesis_summary_norm]

/-- The Action circuit's reduced synthesis summary records the exact instance endpoint. -/
theorem actionSynthesisSummary_instanceRowExtent_eq :
    actionSynthesisSummary.instanceRowExtent = 10 := by
  unfold actionSynthesisSummary Circuit.mainPostSynthesisSummary
    Circuit.synthesizeBaseSynthesisSummary
  simp only [synthesis_summary_norm]
  norm_num

/-- V1 placement covers the Action circuit's complete operation footprint exactly. -/
theorem actionOperations_usedRows_eq_1779 :
    Halo2.usedRows actionOperations = 1779 := by
  apply Nat.le_antisymm
  · apply (Halo2.usedRows_le_summaryExtents
      actionOperations actionOperations_copyCellsAssigned).trans
    rw [actionPlacementEnd_eq_1779,
      ← actionSynthesisSummary_eq_operations,
      actionSynthesisSummary_tableRowExtent_eq,
      actionSynthesisSummary_instanceRowExtent_eq]
    norm_num
  · rw [← actionPlacementEnd_eq_1779]
    exact V1_placementEnd_le_usedRows actionOperations

/-- The Action circuit's public inputs do not extend its exact operation footprint. -/
theorem actionUsedRows_eq_1779 :
    TopLevelCompilation.usedRows actionFormalCircuit PublicInputs.layout = 1779 := by
  unfold TopLevelCompilation.usedRows
  rw [show TopLevelCompilation.operations actionFormalCircuit =
      actionOperations by rfl,
    actionOperations_usedRows_eq_1779]
  apply Nat.max_eq_left
  have hPublicInputRows : PublicInputs.layout.usedRows = 10 := by
    rw [← actionCircuit_publicInputLayout_usedRows_eq]
    rw [Internal.actionCircuit_eq_impl]
    rfl
  exact hPublicInputRows.le.trans (by norm_num)

/-- Halo 2's minimal-domain calculation selects exponent 11 for the Action circuit. -/
theorem actionDomainExponent_eq :
    TopLevelCompilation.domainExponent actionFormalCircuit PublicInputs.layout = 11 := by
  have hcompiledUsedRows :
      TopLevelCompilation.usedRows actionFormalCircuit
        PublicInputs.layout = 1779 := by
    exact actionUsedRows_eq_1779
  have hcompiledBlindingFactors :
      (TopLevelCompilation.constraintSystem
        actionFormalCircuit).blindingFactors = 5 := by
    simpa only [← actionCircuit_formalCircuit_eq,
      TopLevelCircuit.blindingFactors, TopLevelCircuit.constraintSystem] using
        actionCircuit_blindingFactors_eq
  unfold TopLevelCompilation.domainExponent
  apply minimalKForRows_eq_succ_of (k := 10)
  · simp only [ConstraintSystem.minimumRows, hcompiledUsedRows,
      hcompiledBlindingFactors]
    norm_num
  · simp only [ConstraintSystem.minimumRows, hcompiledUsedRows,
      hcompiledBlindingFactors]
    norm_num

/-- V1's exact Action start rows in original region-index order. -/
def actionReducedRegionStarts : List ℕ :=
  [1768, 1770, 1762, 1763, 1764, 1769, 1773, 1772, 1758, 333, 751, 742,
   332, 331, 1288, 1737, 1761, 330, 700, 682, 329, 328, 1341, 1727, 1755,
   334, 1773, 652, 325, 297, 917, 1713, 1750, 321, 721, 1664, 318, 317,
   1500, 1719, 1753, 313, 1770, 1767, 310, 309, 1076, 1731, 1757, 305,
   1706, 1697, 303, 302, 1553, 1743, 1747, 301, 1658, 1606, 300, 299, 864,
   1741, 1752, 298, 670, 649, 296, 295, 970, 1733, 1759, 294, 607, 604,
   293, 292, 1129, 1721, 1760, 291, 613, 622, 290, 289, 1394, 1725, 1756,
   288, 658, 661, 287, 286, 1235, 1729, 1754, 285, 1776, 694, 284, 283,
   1447, 1735, 1751, 282, 730, 733, 281, 280, 1182, 1739, 1749, 279, 1615,
   1627, 278, 277, 811, 1717, 1746, 276, 1667, 1676, 275, 274, 1023, 1723,
   1748, 312, 1709, 1755, 327, 314, 758, 1715, 1744, 319, 1761, 1758, 318,
   317, 1235, 1731, 1746, 316, 1694, 1691, 274, 275, 1023, 1723, 1657, 276,
   1673, 1670, 277, 278, 970, 1713, 1739, 279, 1636, 1633, 280, 281, 1129,
   1715, 1740, 282, 1612, 1609, 283, 284, 1394, 1737, 1742, 285, 739, 736,
   286, 287, 1500, 1735, 1743, 288, 715, 712, 289, 290, 1553, 1733, 1750,
   291, 691, 688, 292, 293, 1341, 1729, 1747, 294, 667, 664, 295, 296, 758,
   1727, 1748, 297, 643, 640, 298, 299, 1288, 1725, 1751, 300, 619, 616,
   301, 302, 1447, 1721, 1752, 303, 601, 598, 304, 305, 1182, 1717, 1753,
   306, 610, 625, 307, 308, 1076, 1651, 1749, 320, 637, 646, 329, 309, 917,
   1643, 1754, 310, 697, 706, 311, 312, 864, 1647, 1741, 313, 1618, 1639,
   314, 315, 811, 1655, 757, 1642, 1658, 1691, 418, 1699, 1697, 272, 250,
   1606, 273, 247, 1693, 524, 253, 1701, 673, 1703, 1711, 304, 1700, 1703,
   306, 307, 1764, 308, 333, 1689, 1606, 1685, 538, 381, 1709, 0, 311, 566,
   247, 1767, 0, 315, 655, 1688, 316, 319, 1685, 320, 1661, 745, 322, 323,
   718, 324, 685, 326, 673, 634, 247, 496, 1645, 631, 628, 325, 426, 1653,
   503, 1687, 137, 1707, 468, 366, 351, 552, 256, 260, 268, 266, 269, 586,
   580, 596, 594, 582, 0, 1766, 1765, 1771, 321, 676, 679, 322, 323, 703,
   324, 709, 724, 325, 326, 727, 327, 748, 328, 754, 1621, 273, 510, 1719,
   1624, 1630, 299, 454, 1649, 588, 1695, 137, 1705, 482, 411, 396, 440,
   258, 262, 270, 264, 271, 592, 590, 597, 588, 584, 1745, 1681]

/-- The operation-level planner starts agree with the reduced-summary computation. -/
theorem actionRegionStarts_eq_reduced :
    TopLevelCompilation.regionStarts actionFormalCircuit =
      actionReducedRegionStarts := by
  unfold TopLevelCompilation.regionStarts V1.starts
  rw [V1.planOperations_eq]
  rw [show TopLevelCompilation.operations actionFormalCircuit =
      actionOperations by rfl]
  let shapes := measureRegions actionOperations
  let sorted := (Pdqsort.quicksort shapes.toArray
    (fun left right => left.key < right.key)).reverse.toList
  let pairs := (slotIn sorted).1
  have hsortedIndices :
      sorted.map RegionShape.index = actionSortedRegionIndices := by
    simpa only [shapes, sorted] using actionSortedRegionIndices_eq
  have hpairsIndices : pairs.map (·.1) = actionSortedRegionIndices := by
    exact (slotIn_indices sorted).trans hsortedIndices
  have hpairsStarts : pairs.map (·.2) = actionExactSortedStarts := by
    have hstarts :=
      V1.sortedRegionStarts_eq_slotShapeSummariesFrom_withoutSelectors
        actionOperations (selectorAnchor actionConfig)
        (by
          rw [← actionSynthesisSummary_eq_operations]
          exact actionSelectorAnchored)
    have hphysical : pairs.map (·.2) =
        (slotShapeSummariesFrom actionSortedPlannerSummaries
          (∅ : CircuitAllocations)).1 := by
      simpa only [shapes, sorted, pairs, actionSortedPlannerSummaries]
        using hstarts
    have hequivalent :=
      slotShapeSummariesFrom_eq_of_forall₂_placementEquivalent
        actionSortedPlannerSummaries_equivalent_exact
        (∅ : CircuitAllocations)
    rw [hphysical, hequivalent]
    exact actionExactSortedPlannerSummaries_starts_eq
  have hpairs : pairs =
      actionSortedRegionIndices.zip actionExactSortedStarts := by
    exact List.zip_of_prod hpairsIndices hpairsStarts
  unfold V1.planCandidate
  change (V1.sortPairsByIndex pairs).map (·.2) = actionReducedRegionStarts
  rw [hpairs]
  unfold actionSortedRegionIndices actionExactSortedStarts
    actionExactPlannerTrace actionPlannerBlocks actionReducedRegionStarts
    V1.PlannedSummaryBlock.starts V1.repeatedStarts V1.sortPairsByIndex
  decide +kernel

/-- Action's absolute selector activations reconstructed from reduced local summaries. -/
def actionReducedSelectorActivations : List (ℕ × ℕ) :=
  placeSelectorActivations actionReducedRegionStarts 0
    actionSynthesisSummary.regionSelectorActivations

/-- The operation-level activation stream agrees with reduced-summary reconstruction. -/
theorem actionSelectorActivations_eq_reduced :
    TopLevelCompilation.selectorActivations actionFormalCircuit =
      actionReducedSelectorActivations := by
  unfold TopLevelCompilation.selectorActivations
    actionReducedSelectorActivations
  rw [activations_eq_placeSelectorActivations]
  rw [show TopLevelCompilation.operations actionFormalCircuit =
      actionOperations by rfl,
    ← actionSynthesisSummary_eq_operations,
    actionRegionStarts_eq_reduced]

/-- Every Action selector activation lies inside the literal domain of size `2^11`. -/
theorem actionSelectorActivation_row_lt_domain
    (activation : ℕ × ℕ)
    (hactivation : activation ∈
      TopLevelCompilation.selectorActivations actionFormalCircuit) :
    activation.2 < 2 ^ 11 := by
  have hplaced : activation.2 < V1.placementEnd actionOperations := by
    apply V1.activation_row_lt_placementEnd actionOperations
    simpa only [TopLevelCompilation.selectorActivations,
      TopLevelCompilation.regionStarts, actionOperations] using hactivation
  rw [actionPlacementEnd_eq_1779] at hplaced
  omega

end Zcash.Circuits.Action
