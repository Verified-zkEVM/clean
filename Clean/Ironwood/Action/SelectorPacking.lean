import Clean.Halo2.Keygen.FloorPlanner.SelectorConflicts
import Clean.Halo2.Keygen.SelectorPackingCorrectness
import Clean.Ironwood.Action.Planner

namespace Zcash.Circuits.Action

open Halo2 FloorPlanner

private def actionNonzeroSelectors : List ℕ :=
  [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19,
   20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37,
   38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53,
   54, 55]

private theorem actionSelectorDegreePartitions :
    (List.range 56).filter
        (fun selector => actionSelectorDegrees[selector]! = 0) =
      [2, 3, 25, 29] ∧
    (List.range 56).filter
        (fun selector => actionSelectorDegrees[selector]! ≠ 0) =
      actionNonzeroSelectors := by
  unfold actionSelectorDegrees actionNonzeroSelectors
  decide +kernel

/-- The selector pairs whose conflict result is not determined by the compact
region-local separation argument. The packing width is independent of all
nineteen answers. -/
def actionUnresolvedSelectorPairs : List (ℕ × ℕ) :=
  [(0, 4), (1, 4), (1, 5), (4, 5), (1, 6), (4, 6), (1, 7), (4, 7),
   (4, 8), (23, 26), (23, 27), (24, 26), (24, 27), (28, 30),
   (28, 31), (28, 32), (28, 34), (28, 35), (28, 36)]

private def actionSelectorsMayConflict (left right : ℕ) : Bool :=
  actionUnresolvedSelectorPairs.contains (left, right) ||
    actionUnresolvedSelectorPairs.contains (right, left)

private theorem actionShortLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Ecc.MulFixed.Short.circuitSynthesisSummary
          actionConfig.eccConfig.mulFixedShort) =
      [(7, 18)].toFinset := by
  ext pair
  rcases pair with ⟨left, right⟩
  unfold Ecc.MulFixed.Short.circuitSynthesisSummary
    Ecc.MulFixed.Short.innerRegionSynthesisSummary
    Ecc.MulFixed.Short.mswRegionSynthesisSummary
  simp only [synthesis_summary_norm, Finset.mem_union, List.mem_toFinset,
    mem_regionLocalSelectorConflictPairs_iff]
  simp only [DecomposeRunningSum.copyDecomposeSynthesisSummary,
    DecomposeRunningSum.enableLoopSynthesisSummary,
    DecomposeRunningSum.assignLoopSynthesisSummary,
    Ecc.MulFixed.fixedConstantsLoopSynthesisSummary,
    Ecc.MulFixed.windowChainSynthesisSummary,
    Ecc.MulFixed.processWindowSynthesisSummary,
    Ecc.AddIncomplete.synthesisSummary, Ecc.Add.synthesisSummary,
    synthesis_summary_norm, List.mem_append,
    RegionSynthesisSummary.mem_repeatedSelectorActivations_iff]
  rw [show actionConfig.eccConfig.mulFixedShort.superConfig.runningSumConfig.qRangeCheck.index = 18 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addIncompleteConfig.qAddIncomplete.index = 7 by rfl,
    show actionConfig.eccConfig.mulFixedShort.superConfig.addConfig.qAdd.index = 8 by rfl,
    show actionConfig.eccConfig.mulFixedShort.qMulFixedShort.index = 20 by rfl]
  simp
  aesop

private theorem actionFullWidthLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Ecc.MulFixed.FullWidth.circuitSynthesisSummary
          actionConfig.eccConfig.mulFixedFull) =
      [(7, 19)].toFinset := by
  ext pair
  rcases pair with ⟨left, right⟩
  unfold Ecc.MulFixed.FullWidth.circuitSynthesisSummary
    Ecc.MulFixed.FullWidth.innerRegionSynthesisSummary
    Ecc.Add.synthesisSummary
  simp only [synthesis_summary_norm, Finset.mem_union, List.mem_toFinset,
    mem_regionLocalSelectorConflictPairs_iff]
  simp only [Ecc.MulFixed.FullWidth.witnessScalarLoopSynthesisSummary,
    Ecc.MulFixed.fixedConstantsLoopSynthesisSummary,
    Ecc.MulFixed.windowChainSynthesisSummary,
    Ecc.MulFixed.processWindowSynthesisSummary,
    Ecc.AddIncomplete.synthesisSummary, synthesis_summary_norm,
    List.mem_append,
    RegionSynthesisSummary.mem_repeatedSelectorActivations_iff]
  rw [show actionConfig.eccConfig.mulFixedFull.qMulFixedFull.index = 19 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addIncompleteConfig.qAddIncomplete.index = 7 by rfl,
    show actionConfig.eccConfig.mulFixedFull.superConfig.addConfig.qAdd.index = 8 by rfl]
  simp
  aesop

private theorem actionValueCommitLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (ValueCommit.synthesisSummary
          (actionConfig.eccConfig.mulFixedShort,
            actionConfig.eccConfig.mulFixedFull,
            actionConfig.eccConfig.add)) =
      [(7, 18), (7, 19)].toFinset := by
  unfold ValueCommit.synthesisSummary
  rw [localSelectorConflictPairs_combine,
    localSelectorConflictPairs_combine,
    actionShortLocalSelectorConflictPairs_eq,
    actionFullWidthLocalSelectorConflictPairs_eq]
  unfold Ecc.Add.synthesisSummary
  simp [synthesis_summary_norm, regionLocalSelectorConflictPairs]

private theorem actionSpendAuthorityLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (SpendAuthority.synthesisSummary
          (actionConfig.eccConfig.mulFixedFull,
            actionConfig.eccConfig.add)) =
      [(7, 19)].toFinset := by
  unfold SpendAuthority.synthesisSummary
  rw [localSelectorConflictPairs_combine,
    actionFullWidthLocalSelectorConflictPairs_eq]
  unfold Ecc.Add.synthesisSummary
  simp [synthesis_summary_norm, regionLocalSelectorConflictPairs]

private theorem actionBaseFieldLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Ecc.MulFixed.BaseFieldElem.circuitSynthesisSummary
          actionConfig.eccConfig.mulFixedBaseField) =
      [(7, 18), (2, 3)].toFinset := by
  ext pair
  rcases pair with ⟨left, right⟩
  unfold Ecc.MulFixed.BaseFieldElem.circuitSynthesisSummary
    Ecc.MulFixed.BaseFieldElem.innerRegionSynthesisSummary
    Ecc.MulFixed.BaseFieldElem.witnessCheck13SynthesisSummary
    Ecc.MulFixed.BaseFieldElem.canonicityRegionSynthesisSummary
    LookupRangeCheck.witnessCheckSynthesisSummary
    LookupRangeCheck.rangeCheckSynthesisSummary
    Ecc.Add.synthesisSummary
  simp only [synthesis_summary_norm, Finset.mem_union, List.mem_toFinset,
    mem_regionLocalSelectorConflictPairs_iff]
  simp only [DecomposeRunningSum.copyDecomposeSynthesisSummary,
    DecomposeRunningSum.enableLoopSynthesisSummary,
    DecomposeRunningSum.assignLoopSynthesisSummary,
    Ecc.MulFixed.fixedConstantsLoopSynthesisSummary,
    Ecc.MulFixed.windowChainSynthesisSummary,
    Ecc.MulFixed.processWindowSynthesisSummary,
    Ecc.AddIncomplete.synthesisSummary, synthesis_summary_norm,
    List.mem_append,
    RegionSynthesisSummary.mem_repeatedSelectorActivations_iff,
    RegionSynthesisSummary.mem_repeatedSelectorPattern_iff]
  rw [show actionConfig.eccConfig.mulFixedBaseField.superConfig.runningSumConfig.qRangeCheck.index = 18 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addIncompleteConfig.qAddIncomplete.index = 7 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.superConfig.addConfig.qAdd.index = 8 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.qMulFixedBaseField.index = 21 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.lookupConfig.qLookup.index = 2 by rfl,
    show actionConfig.eccConfig.mulFixedBaseField.lookupConfig.qRunning.index = 3 by rfl]
  simp
  constructor
  · rintro (⟨hlt, row, hleft, hright⟩ | hsameAdd |
      ⟨hlt, row, hleft, hright⟩ | hsameCanonicity)
    · rcases hleft with hleft | hleft | hleft <;>
        rcases hright with hright | hright | hright <;> omega
    · omega
    · rcases hleft with ⟨index, hindex, hleft⟩
      rcases hright with ⟨other, hother, hright⟩
      rcases hleft with hleft | hleft <;>
        rcases hright with hright | hright <;>
        rcases hleft with ⟨hleftSelector, hleftRow⟩ <;>
        rcases hright with ⟨hrightSelector, hrightRow⟩ <;> omega
    · omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · left
      exact ⟨by omega, 1, Or.inr (Or.inl ⟨rfl, rfl⟩),
        Or.inl ⟨rfl, by omega⟩⟩
    · right
      right
      left
      exact ⟨by omega, 0,
        ⟨0, by omega, Or.inl ⟨rfl, rfl⟩⟩,
        ⟨0, by omega, Or.inr ⟨rfl, rfl⟩⟩⟩

private theorem actionPoseidonLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Poseidon.hashSynthesisSummary actionConfig.poseidonConfig) = ∅ := by
  ext pair
  rcases pair with ⟨left, right⟩
  unfold Poseidon.hashSynthesisSummary
    Poseidon.initRegionSynthesisSummary
    Poseidon.addInputRegionSynthesisSummary
    Poseidon.permuteSynthesisSummary
  simp only [synthesis_summary_norm, Finset.mem_union,
    mem_regionLocalSelectorConflictPairs_iff]
  simp only [List.mem_append,
    RegionSynthesisSummary.mem_repeatedSelectorActivations_iff]
  simp only [List.not_mem_nil, false_and, false_or, List.mem_singleton,
    Prod.mk.injEq, Nat.zero_add, Nat.one_mul]
  simp
  constructor
  · omega
  · intro hlt row hleft
    rcases hleft with hleft | hleft | hleft
    · rcases hleft with ⟨hselector, hrow⟩
      constructor
      · omega
      · constructor <;> omega
    · rcases hleft with ⟨hselector, index, hindex, hrow⟩
      constructor
      · omega
      · constructor <;> omega
    · rcases hleft with ⟨hselector, index, hindex, hrow⟩
      constructor
      · omega
      · constructor <;> omega

private theorem actionDeriveNullifierLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (DeriveNullifier.synthesisSummary
          (actionConfig.poseidonConfig, actionConfig.addChipConfig,
            actionConfig.eccConfig.mulFixedBaseField,
            actionConfig.eccConfig.add)) =
      [(7, 18), (2, 3)].toFinset := by
  unfold DeriveNullifier.synthesisSummary
  rw [localSelectorConflictPairs_combine,
    localSelectorConflictPairs_combine,
    localSelectorConflictPairs_combine,
    actionBaseFieldLocalSelectorConflictPairs_eq]
  rw [actionPoseidonLocalSelectorConflictPairs_eq]
  unfold AddChip.synthesisSummary
    Ecc.Add.synthesisSummary
  simp [synthesis_summary_norm, regionLocalSelectorConflictPairs]

private theorem actionMulMainSelectorActivation_iff
    (selector row : ℕ) :
    (selector, row) ∈
        (Ecc.Mul.mainCircuitSynthesisSummary
          actionConfig.eccConfig.mul).selectorActivations ↔
      (selector = 8 ∧ (row = 0 ∨
        (∃ index < 3, row = 129 + 2 * index) ∨
        (∃ index < 3, row = 130 + 2 * index) ∨ row = 135)) ∨
      (selector = 9 ∧ row = 1) ∨
      (selector = 10 ∧ ∃ index < 124, row = 2 + index) ∨
      (selector = 11 ∧ row = 126) ∨
      (selector = 12 ∧ row = 1) ∨
      (selector = 13 ∧ ∃ index < 125, row = 2 + index) ∨
      (selector = 14 ∧ row = 127) ∨
      (selector = 15 ∧ ∃ index < 3, row = 130 + 2 * index) ∨
      (selector = 17 ∧ row = 135) := by
  unfold Ecc.Mul.mainCircuitSynthesisSummary
    Ecc.MulIncomplete.doubleAndAddSynthesisSummary
    Ecc.MulIncomplete.loopSynthesisSummary
    Ecc.MulComplete.circuitSynthesisSummary
    Ecc.MulComplete.roundsSynthesisSummary Ecc.Add.synthesisSummary
  simp only [synthesis_summary_norm, List.mem_append,
    RegionSynthesisSummary.mem_repeatedSelectorActivations_iff,
    RegionSynthesisSummary.mem_repeatedSelectorPattern_iff]
  rw [show actionConfig.eccConfig.mul.addConfig.qAdd.index = 8 by rfl,
    show actionConfig.eccConfig.mul.hiConfig.qMul1.index = 9 by rfl,
    show actionConfig.eccConfig.mul.hiConfig.qMul2.index = 10 by rfl,
    show actionConfig.eccConfig.mul.hiConfig.qMul3.index = 11 by rfl,
    show actionConfig.eccConfig.mul.loConfig.qMul1.index = 12 by rfl,
    show actionConfig.eccConfig.mul.loConfig.qMul2.index = 13 by rfl,
    show actionConfig.eccConfig.mul.loConfig.qMul3.index = 14 by rfl,
    show actionConfig.eccConfig.mul.completeConfig.qDecompose.index = 15 by rfl,
    show actionConfig.eccConfig.mul.completeConfig.addConfig.qAdd.index = 8 by rfl,
    show actionConfig.eccConfig.mul.qMulLsb.index = 17 by rfl]
  simp only [Ecc.Mul.offInit, Ecc.Mul.offHi, Ecc.Mul.offLo,
    Ecc.Mul.offComp, Ecc.Mul.offLsb, Ecc.Mul.loSpan, Ecc.Mul.compSpan]
  simp only [List.not_mem_nil, false_or, List.mem_cons, Prod.mk.injEq,
    or_false, Nat.one_mul]
  constructor
  · rintro (h8zero | (h9 | h10 | h11) | (h12 | h13 | h14) |
      hcomplete | h17 | h8last)
    · left
      exact ⟨h8zero.1, Or.inl h8zero.2⟩
    · right; left
      exact h9
    · rcases h10 with ⟨hselector, index, hindex, hrow⟩
      right; right; left
      exact ⟨hselector, index, hindex, by omega⟩
    · right; right; right; left
      exact ⟨h11.1, by omega⟩
    · right; right; right; right; left
      exact ⟨h12.1, by simpa [Ecc.Mul.offHi] using h12.2⟩
    · rcases h13 with ⟨hselector, index, hindex, hrow⟩
      right; right; right; right; right; left
      exact ⟨hselector, index, hindex,
        by simpa [Ecc.Mul.offHi] using hrow⟩
    · right; right; right; right; right; right; left
      exact ⟨h14.1, by simpa [Ecc.Mul.offHi] using h14.2⟩
    · rcases hcomplete with ⟨index, hindex, source,
        hsource, hselector, hrow⟩
      rcases hsource with rfl | rfl | rfl
      · right; right; right; right; right; right; right; left
        exact ⟨hselector, index, hindex, by omega⟩
      · left
        exact ⟨hselector, Or.inr (Or.inl
          ⟨index, hindex, by omega⟩)⟩
      · left
        exact ⟨hselector, Or.inr (Or.inr (Or.inl
          ⟨index, hindex, by omega⟩))⟩
    · right; right; right; right; right; right; right; right
      exact ⟨h17.1, by omega⟩
    · left
      exact ⟨h8last.1, Or.inr (Or.inr (Or.inr (by omega)))⟩
  · rintro (h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h17)
    · rcases h8 with ⟨hselector, hrow | heven | hodd | hrow⟩
      · left
        exact ⟨hselector, hrow⟩
      · rcases heven with ⟨index, hindex, hrow⟩
        right; right; right; left
        exact ⟨index, hindex, (8, 0), Or.inr (Or.inl rfl),
          hselector, by omega⟩
      · rcases hodd with ⟨index, hindex, hrow⟩
        right; right; right; left
        exact ⟨index, hindex, (8, 1), Or.inr (Or.inr rfl),
          hselector, by omega⟩
      · right; right; right; right; right
        exact ⟨hselector, by omega⟩
    · right; left; left
      exact h9
    · rcases h10 with ⟨hselector, index, hindex, hrow⟩
      right; left; right; left
      exact ⟨hselector, index, hindex, by omega⟩
    · right; left; right; right
      exact ⟨h11.1, by omega⟩
    · right; right; left; left
      exact ⟨h12.1, by simpa [Ecc.Mul.offHi] using h12.2⟩
    · rcases h13 with ⟨hselector, index, hindex, hrow⟩
      right; right; left; right; left
      exact ⟨hselector, index, hindex,
        by simpa [Ecc.Mul.offHi] using hrow⟩
    · right; right; left; right; right
      exact ⟨h14.1, by simpa [Ecc.Mul.offHi] using h14.2⟩
    · rcases h15 with ⟨hselector, index, hindex, hrow⟩
      right; right; right; left
      exact ⟨index, hindex, (15, 1), Or.inl rfl,
        hselector, by omega⟩
    · right; right; right; right; left
      exact ⟨h17.1, by omega⟩

private theorem actionMulMainLocalSelectorConflictPairs_eq :
    regionLocalSelectorConflictPairs
        (Ecc.Mul.mainCircuitSynthesisSummary
          actionConfig.eccConfig.mul).selectorActivations =
      [(9, 12), (10, 13), (11, 13), (8, 15),
        (8, 17)].toFinset := by
  ext pair
  rcases pair with ⟨left, right⟩
  rw [mem_regionLocalSelectorConflictPairs_iff]
  simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    Prod.mk.injEq, or_false]
  constructor
  · rintro ⟨hlt, row, hleft, hright⟩
    rw [actionMulMainSelectorActivation_iff] at hleft hright
    rcases hleft with
        ⟨rfl, hleft | ⟨leftIndex, hleftIndex, hleft⟩ |
          ⟨leftIndex, hleftIndex, hleft⟩ | hleft⟩ |
        ⟨rfl, hleft⟩ |
        ⟨rfl, leftIndex, hleftIndex, hleft⟩ |
        ⟨rfl, hleft⟩ | ⟨rfl, hleft⟩ |
        ⟨rfl, leftIndex, hleftIndex, hleft⟩ |
        ⟨rfl, hleft⟩ |
        ⟨rfl, leftIndex, hleftIndex, hleft⟩ | ⟨rfl, hleft⟩ <;>
      rcases hright with
        ⟨rfl, hright | ⟨rightIndex, hrightIndex, hright⟩ |
          ⟨rightIndex, hrightIndex, hright⟩ | hright⟩ |
        ⟨rfl, hright⟩ |
        ⟨rfl, rightIndex, hrightIndex, hright⟩ |
        ⟨rfl, hright⟩ | ⟨rfl, hright⟩ |
        ⟨rfl, rightIndex, hrightIndex, hright⟩ |
        ⟨rfl, hright⟩ |
        ⟨rfl, rightIndex, hrightIndex, hright⟩ | ⟨rfl, hright⟩ <;>
      omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨by omega, 1,
        actionMulMainSelectorActivation_iff 9 1 |>.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
        actionMulMainSelectorActivation_iff 12 1 |>.mpr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))⟩
    · exact ⟨by omega, 2,
        actionMulMainSelectorActivation_iff 10 2 |>.mpr
          (Or.inr (Or.inr (Or.inl ⟨rfl, 0, by omega, by omega⟩))),
        actionMulMainSelectorActivation_iff 13 2 |>.mpr
          (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl ⟨rfl, 0, by omega, by omega⟩))))))⟩
    · exact ⟨by omega, 126,
        actionMulMainSelectorActivation_iff 11 126 |>.mpr
          (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))),
        actionMulMainSelectorActivation_iff 13 126 |>.mpr
          (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl ⟨rfl, 124, by omega, by omega⟩))))))⟩
    · exact ⟨by omega, 130,
        actionMulMainSelectorActivation_iff 8 130 |>.mpr
          (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl
            ⟨0, by omega, by omega⟩))⟩),
        actionMulMainSelectorActivation_iff 15 130 |>.mpr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl ⟨rfl, 0, by omega, by omega⟩))))))))⟩
    · exact ⟨by omega, 135,
        actionMulMainSelectorActivation_iff 8 135 |>.mpr
          (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr rfl))⟩),
        actionMulMainSelectorActivation_iff 17 135 |>.mpr
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inr ⟨rfl, rfl⟩))))))))⟩

private theorem actionMulOverflowLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Ecc.MulOverflow.circuitSynthesisSummary 10
          actionConfig.eccConfig.mul.overflowConfig) =
      [(2, 3)].toFinset := by
  ext pair
  rcases pair with ⟨left, right⟩
  unfold Ecc.MulOverflow.circuitSynthesisSummary
    LookupRangeCheck.copyCheckSynthesisSummary
    LookupRangeCheck.rangeCheckSynthesisSummary
  simp only [synthesis_summary_norm, Finset.mem_union, List.mem_toFinset,
    mem_regionLocalSelectorConflictPairs_iff,
    RegionSynthesisSummary.mem_repeatedSelectorPattern_iff]
  rw [show actionConfig.eccConfig.mul.overflowConfig.lookupConfig.qLookup.index = 2 by rfl,
    show actionConfig.eccConfig.mul.overflowConfig.lookupConfig.qRunning.index = 3 by rfl,
    show actionConfig.eccConfig.mul.overflowConfig.qOverflow.index = 16 by rfl]
  unfold Ecc.MulOverflow.numWords
  simp
  constructor
  · rintro (⟨hlt, row, hleft, hright⟩ | hsame)
    · rcases hleft with ⟨leftIndex, hleftIndex, hleft⟩
      rcases hright with ⟨rightIndex, hrightIndex, hright⟩
      rcases hleft with hleft | hleft <;>
        rcases hright with hright | hright <;> omega
    · omega
  · rintro ⟨rfl, rfl⟩
    left
    exact ⟨by omega, 0,
      ⟨0, by omega, Or.inl ⟨rfl, rfl⟩⟩,
      ⟨0, by omega, Or.inr ⟨rfl, rfl⟩⟩⟩

private theorem actionMulLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Ecc.Mul.mulSynthesisSummary actionConfig.eccConfig.mul) =
      [(9, 12), (10, 13), (11, 13), (8, 15), (8, 17),
        (2, 3)].toFinset := by
  unfold Ecc.Mul.mulSynthesisSummary
  rw [localSelectorConflictPairs_combine,
    localSelectorConflictPairs_ofRegion,
    actionMulMainLocalSelectorConflictPairs_eq,
    actionMulOverflowLocalSelectorConflictPairs_eq]
  ext pair
  simp

private theorem actionAddressIntegrityLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (AddressIntegrity.synthesisSummary
          (actionConfig.eccConfig.mul,
            actionConfig.eccConfig.witnessPoint)) =
      [(9, 12), (10, 13), (11, 13), (8, 15), (8, 17),
        (2, 3)].toFinset := by
  unfold AddressIntegrity.synthesisSummary
  rw [localSelectorConflictPairs_combine,
    localSelectorConflictPairs_combine,
    actionMulLocalSelectorConflictPairs_eq]
  unfold Ecc.WitnessPoint.pointNonIdSynthesisSummary
  simp [synthesis_summary_norm, regionLocalSelectorConflictPairs]

private theorem actionShortRangeLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (LookupRangeCheck.witnessShortCheckSynthesisSummary 10
          actionConfig.lookupConfig) = [(2, 4)].toFinset := by
  ext pair
  rcases pair with ⟨left, right⟩
  unfold LookupRangeCheck.witnessShortCheckSynthesisSummary
    LookupRangeCheck.shortRangeCheckSynthesisSummary
  simp only [synthesis_summary_norm, List.mem_toFinset,
    mem_regionLocalSelectorConflictPairs_iff]
  rw [show actionConfig.lookupConfig.qLookup.index = 2 by rfl,
    show actionConfig.lookupConfig.qBitshift.index = 4 by rfl]
  simp
  constructor
  · rintro ⟨hlt, row, hleft, hright⟩
    rcases hleft with hleft | hleft | hleft <;>
      rcases hright with hright | hright | hright <;> omega
  · rintro ⟨rfl, rfl⟩
    exact ⟨by omega, 1, Or.inr (Or.inl ⟨rfl, rfl⟩),
      Or.inr (Or.inr ⟨rfl, rfl⟩)⟩

private theorem actionMerkleHashLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Sinsemilla.HashToPoint.hashCircuitSynthesisSummary
          Sinsemilla.Merkle.HashLayer.merkleNs
          actionConfig.merkle1.sinsemilla) =
      [(25, 26)].toFinset := by
  ext pair
  rcases pair with ⟨left, right⟩
  unfold Sinsemilla.HashToPoint.hashCircuitSynthesisSummary
    Sinsemilla.HashToPoint.hashRegionSynthesisSummary
    Sinsemilla.Chain.circuitSynthesisSummary
    Sinsemilla.Chain.slotIterationSynthesisSummary
    Sinsemilla.Chain.slotSynthesisSummary
    Sinsemilla.HashPiece.circuitSynthesisSummary
    Sinsemilla.HashPiece.loopSynthesisSummary
    Sinsemilla.Merkle.HashLayer.merkleNs
  simp only [synthesis_summary_norm, List.mem_toFinset,
    mem_regionLocalSelectorConflictPairs_iff, List.mem_append,
    RegionSynthesisSummary.mem_repeatedSelectorPattern_iff,
    List.ofFn_succ, List.ofFn_zero, List.foldr_cons, List.foldr_nil]
  rw [show actionConfig.merkle1.sinsemilla.qS4.index = 26 by rfl,
    show actionConfig.merkle1.sinsemilla.qS1.index = 25 by rfl,
    show actionConfig.merkle1.sinsemilla.qS1.toSelector.index = 25 by rfl]
  simp [Sinsemilla.Chain.prefixRows]
  aesop

private theorem actionCommitHashLocalSelectorConflictPairs_eq
    (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config)
    (hns : ns ≠ [])
    (hqS4 : cfg.qS4.index = 26) (hqS1 : cfg.qS1.index = 25) :
    localSelectorConflictPairs
        (Sinsemilla.HashToPoint.hashCircuitSynthesisSummary ns cfg) =
      [(25, 26)].toFinset := by
  unfold Sinsemilla.HashToPoint.hashCircuitSynthesisSummary
  rw [localSelectorConflictPairs_ofRegion]
  ext pair
  rcases pair with ⟨left, right⟩
  rw [mem_regionLocalSelectorConflictPairs_iff]
  simp only [List.mem_toFinset, List.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨hlt, row, hleft, hright⟩
    have hleftSelector :=
      Sinsemilla.HashToPoint.selector_eq_qS1_or_qS4_of_mem_hashCircuitSynthesisSummary
        ns cfg (left, row) hleft
    have hrightSelector :=
      Sinsemilla.HashToPoint.selector_eq_qS1_or_qS4_of_mem_hashCircuitSynthesisSummary
        ns cfg (right, row) hright
    omega
  · rintro ⟨rfl, rfl⟩
    obtain ⟨hleft, hright⟩ :=
      Sinsemilla.HashToPoint.qS1_qS4_overlap_in_hashCircuitSynthesisSummary
        ns cfg hns
    exact ⟨by omega, 0, by simpa only [hqS1] using hleft,
      by simpa only [hqS4] using hright⟩

private theorem actionMerkleHashLayerLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Sinsemilla.Merkle.HashLayer.synthesisSummary
          actionConfig.merkle1 actionConfig.lookupConfig) =
      [(2, 4), (25, 26)].toFinset := by
  unfold Sinsemilla.Merkle.HashLayer.synthesisSummary
  simp only [localSelectorConflictPairs_combine]
  rw [actionShortRangeLocalSelectorConflictPairs_eq,
    actionMerkleHashLocalSelectorConflictPairs_eq]
  unfold Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary
    Sinsemilla.Merkle.Gate.synthesisSummary
  simp [synthesis_summary_norm, regionLocalSelectorConflictPairs]

private theorem actionMerkleLayerLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Sinsemilla.Merkle.Layer.synthesisSummary
          actionConfig.merkle1.condSwap actionConfig.merkle1
          actionConfig.lookupConfig) =
      [(2, 4), (25, 26)].toFinset := by
  unfold Sinsemilla.Merkle.Layer.synthesisSummary
  rw [localSelectorConflictPairs_combine,
    actionMerkleHashLayerLocalSelectorConflictPairs_eq]
  simp [synthesis_summary_norm, regionLocalSelectorConflictPairs]

private theorem actionMerkleLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Sinsemilla.Merkle.CalculateRoot.synthesisSummary 16
          (actionConfig.merkle1.condSwap, actionConfig.merkle1,
            actionConfig.lookupConfig)) =
      [(2, 4), (25, 26)].toFinset := by
  unfold Sinsemilla.Merkle.CalculateRoot.synthesisSummary
  rw [localSelectorConflictPairs_replicate,
    actionMerkleLayerLocalSelectorConflictPairs_eq]
  simp

private def actionEarlySelectorConflict
    (unknown : Fin 9 → Bool) (left right : ℕ) : Bool :=
  match left, right with
  | 0, 4 | 4, 0 => unknown 0
  | 1, 4 | 4, 1 => unknown 1
  | 1, 5 | 5, 1 => unknown 2
  | 4, 5 | 5, 4 => unknown 3
  | 1, 6 | 6, 1 => unknown 4
  | 4, 6 | 6, 4 => unknown 5
  | 1, 7 | 7, 1 => unknown 6
  | 4, 7 | 7, 4 => unknown 7
  | 4, 8 | 8, 4 => unknown 8
  | 8, 15 | 15, 8 | 8, 17 | 17, 8 | 9, 12 | 12, 9 |
      10, 13 | 13, 10 | 11, 13 | 13, 11 => true
  | _, _ => false

private def actionLateSelectorConflict
    (first : Bool) (unknown : Fin 9 → Bool) (left right : ℕ) : Bool :=
  match left, right with
  | 23, 26 | 26, 23 => first
  | 23, 27 | 27, 23 => unknown 0
  | 24, 26 | 26, 24 => unknown 1
  | 24, 27 | 27, 24 => unknown 2
  | 28, 30 | 30, 28 => unknown 3
  | 28, 31 | 31, 28 => unknown 4
  | 28, 32 | 32, 28 => unknown 5
  | 28, 34 | 34, 28 => unknown 6
  | 28, 35 | 35, 28 => unknown 7
  | 28, 36 | 36, 28 => unknown 8
  | _, _ => false

private def actionPackingDegree : ℕ → ℕ
  | 0 => 3 | 1 => 2 | 4 => 3 | 5 => 5 | 6 => 4 | 7 => 4 | 8 => 6
  | 9 => 4 | 10 => 4 | 11 => 4 | 12 => 4 | 13 => 4 | 14 => 4
  | 15 => 3 | 16 => 5 | 17 => 3 | 18 => 9 | 19 => 9 | 20 => 3
  | 21 => 5 | 22 => 6 | 23 => 6 | 24 => 2 | 26 => 4 | 27 => 3
  | 28 => 2 | 30 => 4 | 31 => 3 | 32 => 2 | 33 => 3 | 34 => 3
  | 35 => 3 | 36 => 2 | 37 => 3 | 38 => 3 | 39 => 3 | 40 => 3
  | 41 => 2 | 42 => 3 | 43 => 3 | 44 => 3 | 45 => 3 | 46 => 3
  | 47 => 2 | 48 => 3 | 49 => 3 | 50 => 3 | 51 => 3 | 52 => 2
  | 53 => 3 | 54 => 3 | 55 => 3
  | _ => 0

private theorem actionPackingDegree_eq (selector : ℕ)
    (hselector : selector ∈ actionNonzeroSelectors) :
    actionPackingDegree selector = actionSelectorDegrees[selector]! := by
  have hbound : selector ≤ 55 := by
    simp [actionNonzeroSelectors] at hselector
    omega
  interval_cases selector <;> rfl

private def actionPackingRemainderThree : List (List ℕ) :=
  [[13, 17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32,
    33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55],
   [15, 17, 18, 19, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33,
    34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55],
   [16, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33,
    34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55],
   [17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33,
    34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
    49, 50, 51, 52, 53, 54, 55],
   [18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34,
    35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55]]

private def actionPackingRemainderSixFirst : List ℕ :=
  [23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]

private def actionPackingRemainderSixSecond : List ℕ :=
  [24, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40,
   41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]

private def actionPackingRemainderSixZeroth : List ℕ :=
  [22, 23, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]

private def actionPackingRemainderSix : List (List ℕ) :=
  [actionPackingRemainderSixZeroth, actionPackingRemainderSixFirst,
   actionPackingRemainderSixSecond]

private def actionPackingRemainderNine : List (List ℕ) :=
  [[42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55],
   [45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55],
   [46, 47, 48, 49, 50, 51, 52, 53, 54, 55]]

private def actionPackingRemainderTen : List (List ℕ) :=
  [[49, 50, 51, 52, 53, 54, 55], [52, 53, 54, 55], [53, 54, 55]]

private theorem actionPackingRemainder_three (unknown : Fin 9 → Bool) :
    packingRemainderWith 9 actionPackingDegree
        (actionEarlySelectorConflict unknown) 3 actionNonzeroSelectors ∈
      actionPackingRemainderThree := by
  decide +revert +kernel

private theorem actionPackingRemainder_six
    (selectors : List ℕ) (hselectors : selectors ∈ actionPackingRemainderThree) :
    packingRemainderWith 9 actionPackingDegree
        (fun _ _ => false) 3 selectors ∈
      actionPackingRemainderSix := by
  simp only [actionPackingRemainderThree, List.mem_cons, List.not_mem_nil,
    or_false]
    at hselectors
  rcases hselectors with rfl | rfl | rfl | rfl | rfl <;> decide +kernel

private theorem actionPackingRemainder_nine_false_zeroth
    (unknown : Fin 9 → Bool) :
    packingRemainderWith 9 actionPackingDegree
        (actionLateSelectorConflict false unknown) 3
        actionPackingRemainderSixZeroth ∈
      actionPackingRemainderNine := by
  decide +revert +kernel

private theorem actionPackingRemainder_nine_false_first
    (unknown : Fin 9 → Bool) :
    packingRemainderWith 9 actionPackingDegree
        (actionLateSelectorConflict false unknown) 3
        actionPackingRemainderSixFirst ∈
      actionPackingRemainderNine := by
  decide +revert +kernel

private theorem actionPackingRemainder_nine_false_second
    (unknown : Fin 9 → Bool) :
    packingRemainderWith 9 actionPackingDegree
        (actionLateSelectorConflict false unknown) 3
        actionPackingRemainderSixSecond ∈
      actionPackingRemainderNine := by
  decide +revert +kernel

private theorem actionPackingRemainder_nine_true_first
    (unknown : Fin 9 → Bool) :
    packingRemainderWith 9 actionPackingDegree
        (actionLateSelectorConflict true unknown) 3
        actionPackingRemainderSixFirst ∈
      actionPackingRemainderNine := by
  decide +revert +kernel

private theorem actionPackingRemainder_nine_true_zeroth
    (unknown : Fin 9 → Bool) :
    packingRemainderWith 9 actionPackingDegree
        (actionLateSelectorConflict true unknown) 3
        actionPackingRemainderSixZeroth ∈
      actionPackingRemainderNine := by
  decide +revert +kernel

private theorem actionPackingRemainder_nine_true_second
    (unknown : Fin 9 → Bool) :
    packingRemainderWith 9 actionPackingDegree
        (actionLateSelectorConflict true unknown) 3
        actionPackingRemainderSixSecond ∈
      actionPackingRemainderNine := by
  decide +revert +kernel

private theorem actionPackingRemainder_nine (first : Bool)
    (unknown : Fin 9 → Bool)
    (selectors : List ℕ) (hselectors : selectors ∈ actionPackingRemainderSix) :
    packingRemainderWith 9 actionPackingDegree
        (actionLateSelectorConflict first unknown) 3 selectors ∈
      actionPackingRemainderNine := by
  simp only [actionPackingRemainderSix, List.mem_cons, List.not_mem_nil,
    or_false] at hselectors
  rcases hselectors with rfl | rfl | rfl <;> cases first
  · exact actionPackingRemainder_nine_false_zeroth unknown
  · exact actionPackingRemainder_nine_true_zeroth unknown
  · exact actionPackingRemainder_nine_false_first unknown
  · exact actionPackingRemainder_nine_true_first unknown
  · exact actionPackingRemainder_nine_false_second unknown
  · exact actionPackingRemainder_nine_true_second unknown

private theorem actionPackingRemainder_ten
    (selectors : List ℕ) (hselectors : selectors ∈ actionPackingRemainderNine) :
    packingRemainderWith 9 actionPackingDegree
        (fun _ _ => false) 1 selectors ∈
      actionPackingRemainderTen := by
  simp only [actionPackingRemainderNine, List.mem_cons, List.not_mem_nil,
    or_false]
    at hselectors
  rcases hselectors with rfl | rfl | rfl <;> decide +kernel

private theorem actionPackingRemainder_eleven
    (selectors : List ℕ) (hselectors : selectors ∈ actionPackingRemainderTen) :
    packingRemainderWith 9 actionPackingDegree
        (fun _ _ => false) 1 selectors = [] := by
  simp only [actionPackingRemainderTen, List.mem_cons, List.not_mem_nil,
    or_false]
    at hselectors
  rcases hselectors with rfl | rfl | rfl <;> decide +kernel

end Zcash.Circuits.Action
