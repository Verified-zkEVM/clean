import Clean.Halo2.Keygen.FloorPlanner.SelectorConflicts
import Clean.Halo2.Keygen.SelectorPackingCorrectness
import Clean.Ironwood.Action.SelectorPlacement
import Clean.Ironwood.Action.SelectorSharedColumns

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
    (ns : List ℕ) (cfg : Sinsemilla.HashPiece.Config) (qS1 qS4 : ℕ)
    (hns : ns ≠ [])
    (hqS4 : cfg.qS4.index = qS4) (hqS1 : cfg.qS1.index = qS1)
    (hlt : qS1 < qS4) :
    localSelectorConflictPairs
        (Sinsemilla.HashToPoint.hashCircuitSynthesisSummary ns cfg) =
      [(qS1, qS4)].toFinset := by
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
    exact ⟨hlt, 0, by simpa only [hqS1] using hleft,
      by simpa only [hqS4] using hright⟩

private theorem actionWitnessCheckLocalSelectorConflictPairs_eq
    (numWords : ℕ) (strict : Bool) (hpositive : 0 < numWords) :
    localSelectorConflictPairs
      (LookupRangeCheck.witnessCheckSynthesisSummary 10 numWords strict
          actionConfig.lookupConfig) = [(2, 3)].toFinset := by
  unfold LookupRangeCheck.witnessCheckSynthesisSummary
    LookupRangeCheck.rangeCheckSynthesisSummary
  rw [localSelectorConflictPairs_ofRegion]
  simp only [RegionSynthesisSummary.withSelectorActivations_selectorActivations]
  rw [show actionConfig.lookupConfig.qLookup.index = 2 by rfl,
    show actionConfig.lookupConfig.qRunning.index = 3 by rfl]
  exact regionLocalSelectorConflictPairs_repeatedSelectorPattern_eq
    2 3 0 1 numWords (by omega) hpositive

private theorem actionWitnessCheckDecomposedLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
      (LookupRangeCheck.witnessCheckDecomposedSynthesisSummary
          actionConfig.lookupConfig) = [(2, 3)].toFinset := by
  unfold LookupRangeCheck.witnessCheckDecomposedSynthesisSummary
    LookupRangeCheck.rangeCheckAtDecomposedSynthesisSummary
  rw [localSelectorConflictPairs_ofRegion]
  simp only [RegionSynthesisSummary.combine_selectorActivations,
    RegionSynthesisSummary.ofColumns_selectorActivations,
    RegionSynthesisSummary.withSelectorActivations_selectorActivations,
    List.nil_append]
  rw [show actionConfig.lookupConfig.qLookup.index = 2 by rfl,
    show actionConfig.lookupConfig.qRunning.index = 3 by rfl]
  exact regionLocalSelectorConflictPairs_repeatedSelectorPattern_eq
    2 3 0 1 25 (by omega) (by omega)

private theorem actionYCanonicityLocalSelectorConflictPairs_eq
    (gateConfig : NoteCommit.YCanonicity.Config) :
    localSelectorConflictPairs
        (NoteCommit.YCanonicityCheck.synthesisSummary gateConfig
          actionConfig.lookupConfig) = [(2, 3), (2, 4)].toFinset := by
  unfold NoteCommit.YCanonicityCheck.synthesisSummary
  simp only [localSelectorConflictPairs_combine]
  rw [actionWitnessCheckDecomposedLocalSelectorConflictPairs_eq,
    actionWitnessCheckLocalSelectorConflictPairs_eq 13 false (by omega)]
  unfold NoteCommit.YCanonicity.synthesisSummary
  rw [actionShortRangeLocalSelectorConflictPairs_eq]
  simp [synthesis_summary_norm, regionLocalSelectorConflictPairs]
  ext pair
  simp
  aesop

private theorem witnessMessagePieceLocalSelectorConflictPairs_eq
    (config : Sinsemilla.HashPiece.Config) :
    localSelectorConflictPairs
        (Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary config) = ∅ := by
  unfold Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary
  rw [localSelectorConflictPairs_ofRegion]
  rw [RegionSynthesisSummary.ofColumns_selectorActivations]
  simp [regionLocalSelectorConflictPairs]

private theorem actionCommitDomainLocalSelectorConflictPairs_eq
    (ns : List ℕ) (hashConfig : Sinsemilla.HashPiece.Config)
    (qS1 qS4 : ℕ) (hns : ns ≠ [])
    (hqS4 : hashConfig.qS4.index = qS4)
    (hqS1 : hashConfig.qS1.index = qS1) (hlt : qS1 < qS4) :
    localSelectorConflictPairs
        (Sinsemilla.CommitDomain.commitSynthesisSummary ns
          (actionConfig.eccConfig.mulFixedFull,
            hashConfig,
            actionConfig.eccConfig.add)) =
      [(7, 19), (qS1, qS4)].toFinset := by
  unfold Sinsemilla.CommitDomain.commitSynthesisSummary
  rw [localSelectorConflictPairs_combine,
    localSelectorConflictPairs_combine,
    actionFullWidthLocalSelectorConflictPairs_eq,
    actionCommitHashLocalSelectorConflictPairs_eq ns hashConfig qS1 qS4
      hns hqS4 hqS1 hlt]
  unfold Ecc.Add.synthesisSummary
  simp [synthesis_summary_norm, regionLocalSelectorConflictPairs]

private theorem actionCommitIvkPiecesLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (CommitIvk.Main.synthPiecesSynthesisSummary
          { gate := actionConfig.commitIvkConfig,
            hashConfig := actionConfig.sinsemilla1,
            lookupConfig := actionConfig.lookupConfig,
            mulConfig := actionConfig.eccConfig.mulFixedFull,
            addConfig := actionConfig.eccConfig.add }) =
      [(2, 4)].toFinset := by
  unfold CommitIvk.Main.synthPiecesSynthesisSummary
  simp only
  rw [localSelectorConflictPairs_foldr_combine]
  simp only [List.foldr_cons, List.foldr_nil,
    witnessMessagePieceLocalSelectorConflictPairs_eq,
    actionShortRangeLocalSelectorConflictPairs_eq, Finset.empty_union,
    Finset.union_empty, Finset.union_self]

private theorem actionCommitIvkCanonicityLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (CommitIvk.Canonicity.circuitSynthesisSummary
          actionConfig.commitIvkConfig actionConfig.lookupConfig) =
      [(2, 3)].toFinset := by
  unfold CommitIvk.Canonicity.circuitSynthesisSummary
  rw [localSelectorConflictPairs_combine,
    localSelectorConflictPairs_combine,
    actionWitnessCheckLocalSelectorConflictPairs_eq 13 false (by omega),
    actionWitnessCheckLocalSelectorConflictPairs_eq 14 false (by omega)]
  unfold CommitIvk.synthesisSummary
  rw [localSelectorConflictPairs_ofRegion]
  simp only [RegionSynthesisSummary.withSelectorActivations_selectorActivations,
    regionLocalSelectorConflictPairs_singleton]
  simp

private theorem actionCommitIvkLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (CommitIvk.Main.synthesisSummary
          { gate := actionConfig.commitIvkConfig,
            hashConfig := actionConfig.sinsemilla1,
            lookupConfig := actionConfig.lookupConfig,
            mulConfig := actionConfig.eccConfig.mulFixedFull,
            addConfig := actionConfig.eccConfig.add }) =
      [(2, 4), (7, 19), (25, 26), (2, 3)].toFinset := by
  unfold CommitIvk.Main.synthesisSummary
  rw [localSelectorConflictPairs_combine,
    localSelectorConflictPairs_combine,
    actionCommitIvkPiecesLocalSelectorConflictPairs_eq,
    actionCommitDomainLocalSelectorConflictPairs_eq CommitIvk.Main.ns
      actionConfig.sinsemilla1 25 26 CommitIvk.Main.ns_ne_nil
      (by rfl) (by rfl) (by omega),
    actionCommitIvkCanonicityLocalSelectorConflictPairs_eq]
  ext pair
  simp
  aesop

private theorem actionNotePiecesLocalSelectorConflictPairs_eq
    (gates : NoteCommit.Config) (hashConfig : Sinsemilla.HashPiece.Config) :
    localSelectorConflictPairs
        (NoteCommit.Main.synthPiecesSynthesisSummary
          { gates := gates, hashConfig := hashConfig,
            lookupConfig := actionConfig.lookupConfig,
            mulConfig := actionConfig.eccConfig.mulFixedFull,
            addConfig := actionConfig.eccConfig.add }) =
      [(2, 4)].toFinset := by
  unfold NoteCommit.Main.synthPiecesSynthesisSummary
  simp only
  rw [localSelectorConflictPairs_foldr_combine]
  simp only [List.foldr_cons, List.foldr_nil,
    witnessMessagePieceLocalSelectorConflictPairs_eq,
    actionShortRangeLocalSelectorConflictPairs_eq, Finset.empty_union,
    Finset.union_empty, Finset.union_self]

private theorem actionNoteChecksLocalSelectorConflictPairs_eq
    (gates : NoteCommit.Config) (hashConfig : Sinsemilla.HashPiece.Config)
    (qS1 qS4 : ℕ) (hqS4 : hashConfig.qS4.index = qS4)
    (hqS1 : hashConfig.qS1.index = qS1) (hlt : qS1 < qS4) :
    localSelectorConflictPairs
        (NoteCommit.Main.synthChecksSynthesisSummary
          { gates := gates, hashConfig := hashConfig,
            lookupConfig := actionConfig.lookupConfig,
            mulConfig := actionConfig.eccConfig.mulFixedFull,
            addConfig := actionConfig.eccConfig.add }) =
      [(2, 3), (2, 4), (7, 19), (qS1, qS4)].toFinset := by
  unfold NoteCommit.Main.synthChecksSynthesisSummary
  simp only
  rw [localSelectorConflictPairs_foldr_combine]
  simp only [List.foldr_cons, List.foldr_nil]
  rw [actionYCanonicityLocalSelectorConflictPairs_eq,
    actionCommitDomainLocalSelectorConflictPairs_eq NoteCommit.Main.ns
      hashConfig qS1 qS4 NoteCommit.Main.ns_ne_nil hqS4 hqS1 hlt,
    actionWitnessCheckLocalSelectorConflictPairs_eq 13 false (by omega),
    actionWitnessCheckLocalSelectorConflictPairs_eq 14 false (by omega)]
  ext pair
  simp
  aesop

private theorem actionNoteGatesLocalSelectorConflictPairs_eq
    (gates : NoteCommit.Config) (hashConfig : Sinsemilla.HashPiece.Config) :
    localSelectorConflictPairs
        (NoteCommit.Main.synthGatesSynthesisSummary
          { gates := gates, hashConfig := hashConfig,
            lookupConfig := actionConfig.lookupConfig,
            mulConfig := actionConfig.eccConfig.mulFixedFull,
            addConfig := actionConfig.eccConfig.add }) = ∅ := by
  unfold NoteCommit.Main.synthGatesSynthesisSummary
  simp only
  rw [localSelectorConflictPairs_foldr_combine]
  simp only [List.foldr_cons, List.foldr_nil,
    localSelectorConflictPairs_ofRegion]
  unfold NoteCommit.DecomposeB.synthesisSummary
    NoteCommit.DecomposeD.synthesisSummary
    NoteCommit.DecomposeE.synthesisSummary
    NoteCommit.DecomposeG.synthesisSummary
    NoteCommit.DecomposeH.synthesisSummary
    NoteCommit.GdCanonicity.synthesisSummary
    NoteCommit.PkdCanonicity.synthesisSummary
    NoteCommit.ValueCanonicity.synthesisSummary
    NoteCommit.RhoCanonicity.synthesisSummary
    NoteCommit.PsiCanonicity.synthesisSummary
  simp only [RegionSynthesisSummary.withSelectorActivations_selectorActivations,
    regionLocalSelectorConflictPairs_singleton, Finset.empty_union]

private theorem actionNoteLocalSelectorConflictPairs_eq
    (gates : NoteCommit.Config) (hashConfig : Sinsemilla.HashPiece.Config)
    (qS1 qS4 : ℕ) (hqS4 : hashConfig.qS4.index = qS4)
    (hqS1 : hashConfig.qS1.index = qS1) (hlt : qS1 < qS4) :
    localSelectorConflictPairs
        (NoteCommit.Main.synthesisSummary
          { gates := gates, hashConfig := hashConfig,
            lookupConfig := actionConfig.lookupConfig,
            mulConfig := actionConfig.eccConfig.mulFixedFull,
            addConfig := actionConfig.eccConfig.add }) =
      [(2, 3), (2, 4), (7, 19), (qS1, qS4)].toFinset := by
  unfold NoteCommit.Main.synthesisSummary
  rw [localSelectorConflictPairs_combine,
    localSelectorConflictPairs_combine,
    actionNotePiecesLocalSelectorConflictPairs_eq,
    actionNoteChecksLocalSelectorConflictPairs_eq gates hashConfig qS1 qS4
      hqS4 hqS1 hlt,
    actionNoteGatesLocalSelectorConflictPairs_eq]
  ext pair
  simp
  aesop

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

private theorem actionMerkleHash2LocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Sinsemilla.HashToPoint.hashCircuitSynthesisSummary
          Sinsemilla.Merkle.HashLayer.merkleNs
          actionConfig.merkle2.sinsemilla) =
      [(29, 30)].toFinset :=
  actionCommitHashLocalSelectorConflictPairs_eq
    Sinsemilla.Merkle.HashLayer.merkleNs actionConfig.merkle2.sinsemilla
    29 30 (by simp [Sinsemilla.Merkle.HashLayer.merkleNs])
    (by rfl) (by rfl) (by omega)

private theorem actionMerkleHashLayer2LocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Sinsemilla.Merkle.HashLayer.synthesisSummary
          actionConfig.merkle2 actionConfig.lookupConfig) =
      [(2, 4), (29, 30)].toFinset := by
  unfold Sinsemilla.Merkle.HashLayer.synthesisSummary
  simp only [localSelectorConflictPairs_combine]
  rw [actionShortRangeLocalSelectorConflictPairs_eq,
    actionMerkleHash2LocalSelectorConflictPairs_eq]
  unfold Sinsemilla.HashToPoint.witnessMessagePieceSynthesisSummary
    Sinsemilla.Merkle.Gate.synthesisSummary
  simp [synthesis_summary_norm, regionLocalSelectorConflictPairs]

private theorem actionMerkleLayer2LocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Sinsemilla.Merkle.Layer.synthesisSummary
          actionConfig.merkle2.condSwap actionConfig.merkle2
          actionConfig.lookupConfig) =
      [(2, 4), (29, 30)].toFinset := by
  unfold Sinsemilla.Merkle.Layer.synthesisSummary
  rw [localSelectorConflictPairs_combine,
    actionMerkleHashLayer2LocalSelectorConflictPairs_eq]
  simp [synthesis_summary_norm, regionLocalSelectorConflictPairs]

private theorem actionMerkle2LocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Sinsemilla.Merkle.CalculateRoot.synthesisSummary 16
          (actionConfig.merkle2.condSwap, actionConfig.merkle2,
            actionConfig.lookupConfig)) =
      [(2, 4), (29, 30)].toFinset := by
  unfold Sinsemilla.Merkle.CalculateRoot.synthesisSummary
  rw [localSelectorConflictPairs_replicate,
    actionMerkleLayer2LocalSelectorConflictPairs_eq]
  simp

private theorem actionSynthWitnessLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Circuit.synthWitnessSynthesisSummary actionConfig) = ∅ := by
  unfold Circuit.synthWitnessSynthesisSummary
  rw [localSelectorConflictPairs_foldr_combine]
  unfold Sinsemilla.loadSynthesisSummary Circuit.loadPrivateSynthesisSummary
    Ecc.WitnessPoint.pointSynthesisSummary
    Ecc.WitnessPoint.pointNonIdSynthesisSummary
  simp only [List.foldr_cons, List.foldr_nil,
    localSelectorConflictPairs_ofRegion,
    RegionSynthesisSummary.ofColumns_selectorActivations,
    RegionSynthesisSummary.withSelectorActivations_selectorActivations,
    regionLocalSelectorConflictPairs_singleton,
    regionLocalSelectorConflictPairs_nil, Finset.empty_union]
  simp [localSelectorConflictPairs]

private theorem actionLoadPrivateLocalSelectorConflictPairs_eq
    (column : Column .advice) :
    localSelectorConflictPairs (Circuit.loadPrivateSynthesisSummary column) = ∅ := by
  unfold Circuit.loadPrivateSynthesisSummary
  rw [localSelectorConflictPairs_ofRegion,
    RegionSynthesisSummary.ofColumns_selectorActivations]
  exact regionLocalSelectorConflictPairs_eq_empty_of_fst_eq [] 0 (by simp)

private theorem actionSynthChecksLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Circuit.synthChecksSynthesisSummary actionConfig) =
      [(29, 30), (7, 18), (2, 4), (7, 19), (25, 26),
        (9, 12), (10, 13), (11, 13), (8, 15), (8, 17),
        (2, 3)].toFinset := by
  unfold Circuit.synthChecksSynthesisSummary
  rw [localSelectorConflictPairs_foldr_combine]
  simp only [List.foldr_cons, List.foldr_nil,
    actionLoadPrivateLocalSelectorConflictPairs_eq,
    localSelectorConflictPairs_ofInstanceRow, Finset.empty_union]
  rw [actionMerkleLocalSelectorConflictPairs_eq,
    actionMerkle2LocalSelectorConflictPairs_eq,
    actionValueCommitLocalSelectorConflictPairs_eq,
    actionDeriveNullifierLocalSelectorConflictPairs_eq,
    actionSpendAuthorityLocalSelectorConflictPairs_eq,
    actionCommitIvkLocalSelectorConflictPairs_eq,
    actionAddressIntegrityLocalSelectorConflictPairs_eq]
  decide +kernel

private theorem actionOrchardChecksLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Circuit.orchardChecksSynthesisSummary actionConfig) = ∅ := by
  unfold Circuit.orchardChecksSynthesisSummary
    Circuit.orchardChecksRegionSynthesisSummary
  rw [localSelectorConflictPairs_ofRegion]
  simp only [RegionSynthesisSummary.withSelectorActivations_selectorActivations,
    regionLocalSelectorConflictPairs_singleton]

private theorem actionSynthNotesLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Circuit.synthNotesSynthesisSummary actionConfig) =
      [(29, 30), (2, 4), (7, 19), (25, 26), (2, 3)].toFinset := by
  unfold Circuit.synthNotesSynthesisSummary
  rw [localSelectorConflictPairs_foldr_combine]
  simp only [List.foldr_cons, List.foldr_nil,
    localSelectorConflictPairs_ofRegion,
    Ecc.WitnessPoint.pointNonIdSynthesisSummary,
    RegionSynthesisSummary.withSelectorActivations_selectorActivations,
    regionLocalSelectorConflictPairs_singleton,
    regionLocalSelectorConflictPairs_nil,
    actionLoadPrivateLocalSelectorConflictPairs_eq,
    localSelectorConflictPairs_ofInstanceRow,
    actionOrchardChecksLocalSelectorConflictPairs_eq, Finset.empty_union]
  rw [actionNoteLocalSelectorConflictPairs_eq actionConfig.noteCommitOld
      actionConfig.sinsemilla1 25 26 (by rfl) (by rfl) (by omega),
    actionNoteLocalSelectorConflictPairs_eq actionConfig.noteCommitNew
      actionConfig.sinsemilla2 29 30 (by rfl) (by rfl) (by omega)]
  decide +kernel

private theorem actionCrossAddressLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs
        (Circuit.synthCrossAddressChecksSynthesisSummary actionConfig) = ∅ := by
  unfold Circuit.synthCrossAddressChecksSynthesisSummary
  rw [localSelectorConflictPairs_ofRegion]
  apply regionLocalSelectorConflictPairs_eq_empty_of_fst_eq _
    actionConfig.qOrchard.index
  intro activation hactivation
  have hactivation' : activation ∈
      RegionSynthesisSummary.repeatedSelectorActivations
        actionConfig.qOrchard.index 0 1 4 := by
    simpa only [RegionSynthesisSummary.repeatColumnsWithSelector_selectorActivations]
      using hactivation
  rw [RegionSynthesisSummary.mem_repeatedSelectorActivations_iff] at hactivation'
  exact hactivation'.1

/-- The literal selector pairs that necessarily conflict within one Action region. -/
def actionLocalSelectorConflictPairs : Finset (ℕ × ℕ) :=
  [(29, 30), (7, 18), (2, 4), (7, 19), (25, 26),
    (9, 12), (10, 13), (11, 13), (8, 15), (8, 17),
    (2, 3)].toFinset

/-- The exact selector pairs that necessarily conflict within one Action region. -/
theorem actionLocalSelectorConflictPairs_eq :
    localSelectorConflictPairs actionSynthesisSummary =
      actionLocalSelectorConflictPairs := by
  unfold actionSynthesisSummary Circuit.mainPostSynthesisSummary
    Circuit.synthesizeBaseSynthesisSummary
  simp only [localSelectorConflictPairs_combine]
  rw [actionSynthWitnessLocalSelectorConflictPairs_eq,
    actionSynthChecksLocalSelectorConflictPairs_eq,
    actionSynthNotesLocalSelectorConflictPairs_eq,
    actionCrossAddressLocalSelectorConflictPairs_eq]
  unfold actionLocalSelectorConflictPairs
  decide +kernel

private def actionLocalSelectorsConflict (left right : ℕ) : Bool :=
  decide ((left, right) ∈ actionLocalSelectorConflictPairs ∨
    (right, left) ∈ actionLocalSelectorConflictPairs)

private theorem actionLocalSelectorsConflict_eq_true_iff
    (left right : ℕ) :
    actionLocalSelectorsConflict left right = true ↔
      (left, right) ∈ actionLocalSelectorConflictPairs ∨
        (right, left) ∈ actionLocalSelectorConflictPairs := by
  simp [actionLocalSelectorsConflict]

/-- A small class identifying the physical advice column that anchors each Action
selector. Only equality of classes matters to selector placement. -/
private def actionSelectorAnchorClass (selector : ℕ) : ℕ :=
  if selector = 2 ∨ selector = 3 ∨ selector = 4 then 9
  else if 29 ≤ selector ∧ selector ≤ 32 ∨ selector = 44 ∨ selector = 55 then 5
  else if selector = 1 ∨ selector = 16 ∨
      (21 ≤ selector ∧ selector ≤ 24) ∨
      (34 ≤ selector ∧ selector ≤ 43) ∨
      (45 ≤ selector ∧ selector ≤ 54) then 6
  else 0

private theorem selectorAnchor_eq_class (selector : ℕ) :
    selectorAnchor actionConfig selector =
      .column .advice (actionSelectorAnchorClass selector) := by
  unfold selectorAnchor actionSelectorAnchorClass
  rw [show (actionConfig.advices 0).index = 0 by rfl,
    show (actionConfig.advices 5).index = 5 by rfl,
    show (actionConfig.advices 6).index = 6 by rfl,
    show (actionConfig.advices 9).index = 9 by rfl]
  by_cases hfirst : selector = 2 ∨ selector = 3 ∨ selector = 4
  · simp only [if_pos hfirst]
  · simp only [if_neg hfirst]
    by_cases hsecond :
        29 ≤ selector ∧ selector ≤ 32 ∨ selector = 44 ∨ selector = 55
    · simp only [if_pos hsecond]
    · simp only [if_neg hsecond]
      by_cases hthird : selector = 1 ∨ selector = 16 ∨
          (21 ≤ selector ∧ selector ≤ 24) ∨
          (34 ≤ selector ∧ selector ≤ 43) ∨
          (45 ≤ selector ∧ selector ≤ 54)
      · simp only [if_pos hthird]
      · simp only [if_neg hthird]

private theorem selectorAnchor_eq_of_class_eq (left right : ℕ)
    (hclass : actionSelectorAnchorClass left =
      actionSelectorAnchorClass right) :
    selectorAnchor actionConfig left = selectorAnchor actionConfig right := by
  rw [selectorAnchor_eq_class, selectorAnchor_eq_class, hclass]

private theorem actionActualSelectorConflict_comm (left right : ℕ) :
    actionActualSelectorConflict left right =
      actionActualSelectorConflict right left := by
  unfold actionActualSelectorConflict
  exact selectorActivationsConflict_comm _ _ _

private def actionActualEarlySelectorConflicts : Fin 9 → Bool :=
  ![actionActualSelectorConflict 0 4,
    actionActualSelectorConflict 1 4,
    actionActualSelectorConflict 1 5,
    actionActualSelectorConflict 4 5,
    actionActualSelectorConflict 1 6,
    actionActualSelectorConflict 4 6,
    actionActualSelectorConflict 1 7,
    actionActualSelectorConflict 4 7,
    actionActualSelectorConflict 4 8]

private def actionActualFirstLateSelectorConflict : Bool :=
  actionActualSelectorConflict 23 26

private def actionActualLateSelectorConflicts : Fin 9 → Bool :=
  ![actionActualSelectorConflict 23 27,
    actionActualSelectorConflict 24 26,
    actionActualSelectorConflict 24 27,
    actionActualSelectorConflict 28 30,
    actionActualSelectorConflict 28 31,
    actionActualSelectorConflict 28 32,
    actionActualSelectorConflict 28 34,
    actionActualSelectorConflict 28 35,
    actionActualSelectorConflict 28 36]

private theorem actionActualEarlySelectorConflicts_eq_reduced :
    actionActualEarlySelectorConflicts =
      ![false, false, false, true, false, true, true, true, true] := by
  funext index
  fin_cases index <;>
    apply actionActualSelectorConflict_eq_modeled <;> decide

private theorem actionActualFirstLateSelectorConflict_eq_reduced :
    actionActualFirstLateSelectorConflict = false := by
  apply actionActualSelectorConflict_eq_modeled
  decide

private theorem actionActualLateSelectorConflicts_eq_reduced :
    actionActualLateSelectorConflicts =
      ![false, false, false, false, true, true, false, false, false] := by
  funext index
  fin_cases index <;>
    apply actionActualSelectorConflict_eq_modeled <;> decide

private theorem actionActualSelectorConflict_eq_true_of_local
    (left right : ℕ)
    (hlocal : actionLocalSelectorsConflict left right = true) :
    actionActualSelectorConflict left right = true := by
  unfold actionActualSelectorConflict actionPlacedSelectorActivations
  rw [actionLocalSelectorsConflict_eq_true_iff] at hlocal
  rcases hlocal with hlocal | hlocal
  · apply selectorActivationsConflict_eq_true_of_mem_localConflictPairs
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      actionLocalSelectorConflictPairs_eq]
    exact hlocal
  · rw [selectorActivationsConflict_comm]
    apply selectorActivationsConflict_eq_true_of_mem_localConflictPairs
      actionOperations
    rw [← actionSynthesisSummary_eq_operations,
      actionLocalSelectorConflictPairs_eq]
    exact hlocal

private theorem actionActualSelectorConflict_eq_false_of_anchor
    (left right : ℕ) (hlt : left < right)
    (hlocal : actionLocalSelectorsConflict left right = false)
    (hclass : actionSelectorAnchorClass left =
      actionSelectorAnchorClass right) :
    actionActualSelectorConflict left right = false := by
  unfold actionActualSelectorConflict actionPlacedSelectorActivations
  apply selectorActivationsConflict_eq_false_of_sitesSeparated actionOperations
  apply selectorSitesSeparated_of_anchor actionOperations
    (selectorAnchor actionConfig)
  · rw [← actionSynthesisSummary_eq_operations]
    exact actionSelectorAnchored
  · apply selectorLocalRowsSeparated_of_not_mem_localConflictPairs
      _ left right hlt
    rw [← actionSynthesisSummary_eq_operations,
      actionLocalSelectorConflictPairs_eq]
    intro hconflict
    have : actionLocalSelectorsConflict left right = true :=
      actionLocalSelectorsConflict_eq_true_iff left right |>.mpr
        (Or.inl hconflict)
    simp_all
  · exact selectorAnchor_eq_of_class_eq left right hclass

private theorem actionActualSelectorConflict_eq_false_of_sharedColumn
    (left right : ℕ) (hlt : left < right)
    (hlocal : actionLocalSelectorsConflict left right = false)
    (column : RegionColumn)
    (hleft : SelectorUsesColumn actionSynthesisSummary left column)
    (hright : SelectorUsesColumn actionSynthesisSummary right column) :
    actionActualSelectorConflict left right = false := by
  unfold actionActualSelectorConflict actionPlacedSelectorActivations
  apply selectorActivationsConflict_eq_false_of_sitesSeparated actionOperations
  apply selectorSitesSeparated_of_sharedColumn
  · apply selectorLocalRowsSeparated_of_not_mem_localConflictPairs
      _ left right hlt
    rw [← actionSynthesisSummary_eq_operations,
      actionLocalSelectorConflictPairs_eq]
    intro hconflict
    have : actionLocalSelectorsConflict left right = true :=
      actionLocalSelectorsConflict_eq_true_iff left right |>.mpr
        (Or.inl hconflict)
    simp_all
  · rw [← actionSynthesisSummary_eq_operations]
    exact hleft
  · rw [← actionSynthesisSummary_eq_operations]
    exact hright

private theorem actionActualSelectorConflict_eq_false_of_additionalSharedColumn
    (left right : ℕ) (hlt : left < right)
    (hlocal : actionLocalSelectorsConflict left right = false)
    (hpair : (left, right) ∈ actionAdditionalSharedColumnPairs) :
    actionActualSelectorConflict left right = false := by
  obtain ⟨column, hleft, hright⟩ :=
    actionAdditionalSharedColumnPairs_useColumn left right hpair
  exact actionActualSelectorConflict_eq_false_of_sharedColumn
    left right hlt hlocal column hleft hright

private def actionEarlyUnresolvedSelectorCode
    (left right : ℕ) : Option (Fin 9) :=
  match left, right with
  | 0, 4 | 4, 0 => some 0
  | 1, 4 | 4, 1 => some 1
  | 1, 5 | 5, 1 => some 2
  | 4, 5 | 5, 4 => some 3
  | 1, 6 | 6, 1 => some 4
  | 4, 6 | 6, 4 => some 5
  | 1, 7 | 7, 1 => some 6
  | 4, 7 | 7, 4 => some 7
  | 4, 8 | 8, 4 => some 8
  | _, _ => none

private def actionEarlySelectorCode
    (left right : ℕ) : Option (Option (Fin 9)) :=
  if actionLocalSelectorsConflict left right then some none
  else (actionEarlyUnresolvedSelectorCode left right).map some

private def actionEarlySelectorConflict
    (unknown : Fin 9 → Bool) (left right : ℕ) : Bool :=
  match actionEarlySelectorCode left right with
  | some (some index) => unknown index
  | some none => true
  | none => false

private def actionLateSelectorCode
    (left right : ℕ) : Option (Option (Fin 9)) :=
  match left, right with
  | 23, 26 | 26, 23 => some none
  | 23, 27 | 27, 23 => some (some 0)
  | 24, 26 | 26, 24 => some (some 1)
  | 24, 27 | 27, 24 => some (some 2)
  | 28, 30 | 30, 28 => some (some 3)
  | 28, 31 | 31, 28 => some (some 4)
  | 28, 32 | 32, 28 => some (some 5)
  | 28, 34 | 34, 28 => some (some 6)
  | 28, 35 | 35, 28 => some (some 7)
  | 28, 36 | 36, 28 => some (some 8)
  | _, _ => none

private def actionLateSelectorConflict
    (first : Bool) (unknown : Fin 9 → Bool) (left right : ℕ) : Bool :=
  actionLateExceptionalSelectorConflict left right ||
    match actionLateSelectorCode left right with
    | some (some index) => unknown index
    | some none => first
    | none => false

private def actionEarlySelectorSupport (left right : ℕ) : Bool :=
  (actionEarlySelectorCode left right).isSome

private def actionLateSelectorSupport (left right : ℕ) : Bool :=
  actionLateExceptionalSelectorConflict left right ||
    (actionLateSelectorCode left right).isSome

private theorem actionEarlySelectorConflict_eq_false_of_support
    (unknown : Fin 9 → Bool) (left right : ℕ)
    (hsupport : actionEarlySelectorSupport left right = false) :
    actionEarlySelectorConflict unknown left right = false := by
  unfold actionEarlySelectorSupport at hsupport
  unfold actionEarlySelectorConflict
  cases hcode : actionEarlySelectorCode left right <;>
    simp_all only [Option.isSome_none,
      Option.isSome_some, Bool.true_eq_false]

private theorem actionLateSelectorConflict_eq_false_of_support
    (first : Bool) (unknown : Fin 9 → Bool) (left right : ℕ)
    (hsupport : actionLateSelectorSupport left right = false) :
    actionLateSelectorConflict first unknown left right = false := by
  unfold actionLateSelectorSupport at hsupport
  unfold actionLateSelectorConflict
  cases hcode : actionLateSelectorCode left right <;>
    simp_all only [Option.isSome_none, Option.isSome_some,
      Bool.or_false, Bool.or_true, Bool.true_eq_false]

private theorem actionEarlySelectorCode_local
    (left right : ℕ)
    (hcode : actionEarlySelectorCode left right = some none) :
    actionLocalSelectorsConflict left right = true := by
  unfold actionEarlySelectorCode at hcode
  split at hcode <;> rename_i hlocal
  · exact hlocal
  · cases hcode' : actionEarlyUnresolvedSelectorCode left right <;>
      simp_all

private theorem actionEarlySelectorSupport_eq_true_of_local
    (left right : ℕ)
    (hlocal : actionLocalSelectorsConflict left right = true) :
    actionEarlySelectorSupport left right = true := by
  unfold actionEarlySelectorSupport actionEarlySelectorCode
  rw [if_pos hlocal]
  rfl

/-- The compact conflict oracle used by the Action packing proof. Same-region
and exceptional late conflicts are fixed; the remaining placement-dependent
answers are supplied by the reduced placement model. -/
private def actionInitialSelectorConflict (early : Fin 9 → Bool)
    (left right : ℕ) : Bool :=
  actionEarlySelectorConflict early left right ||
    actionSpecialSelectorConflict left right

private def actionPackingConflict (early : Fin 9 → Bool)
    (first : Bool) (late : Fin 9 → Bool)
    (left right : ℕ) : Bool :=
  actionInitialSelectorConflict early left right ||
    actionLateSelectorConflict first late left right

private theorem actionEarlySelectorConflict_eq_actual_of_code
    (left right : ℕ) (index : Fin 9)
    (hcode : actionEarlySelectorCode left right = some (some index)) :
    actionEarlySelectorConflict actionActualEarlySelectorConflicts left right =
      actionActualSelectorConflict left right := by
  unfold actionEarlySelectorConflict
  rw [hcode]
  unfold actionEarlySelectorCode at hcode
  split at hcode <;> rename_i hlocal
  · simp at hcode
  · simp only [Option.map_eq_some_iff] at hcode
    obtain ⟨resolved, hresolved, hindex⟩ := hcode
    simp only [Option.some.injEq] at hindex
    subst resolved
    unfold actionEarlyUnresolvedSelectorCode at hresolved
    split at hresolved <;> try simp at hresolved
    all_goals
      cases hresolved
      simp [actionActualEarlySelectorConflicts]
    all_goals rw [actionActualSelectorConflict_comm]

private theorem actionLateSelectorConflict_eq_actual_of_indexed_code
    (left right : ℕ) (index : Fin 9)
    (hcode : actionLateSelectorCode left right = some (some index)) :
    actionLateSelectorConflict actionActualFirstLateSelectorConflict
        actionActualLateSelectorConflicts left right =
      actionActualSelectorConflict left right := by
  unfold actionLateSelectorConflict
  rw [hcode]
  unfold actionLateSelectorCode at hcode
  split at hcode <;> try simp at hcode
  all_goals
    cases hcode
    simp [actionActualLateSelectorConflicts,
      actionLateExceptionalSelectorConflict]
  all_goals rw [actionActualSelectorConflict_comm]

private theorem actionLateSelectorConflict_eq_actual_of_first_code
    (left right : ℕ)
    (hcode : actionLateSelectorCode left right = some none) :
    actionLateSelectorConflict actionActualFirstLateSelectorConflict
        actionActualLateSelectorConflicts left right =
      actionActualSelectorConflict left right := by
  unfold actionLateSelectorConflict
  rw [hcode]
  unfold actionLateSelectorCode at hcode
  split at hcode <;> try simp at hcode
  all_goals
    cases hcode
    simp [actionActualFirstLateSelectorConflict,
      actionLateExceptionalSelectorConflict]
  all_goals rw [actionActualSelectorConflict_comm]

private theorem actionEarlySelectorConflict_eq_actual_of_support
    (left right : ℕ)
    (hsupport : actionEarlySelectorSupport left right = true) :
    actionEarlySelectorConflict actionActualEarlySelectorConflicts left right =
      actionActualSelectorConflict left right := by
  unfold actionEarlySelectorSupport at hsupport
  cases hcode : actionEarlySelectorCode left right with
  | none => simp [hcode] at hsupport
  | some code =>
      cases code with
      | none =>
          unfold actionEarlySelectorConflict
          rw [hcode]
          symm
          apply actionActualSelectorConflict_eq_true_of_local
          exact actionEarlySelectorCode_local left right hcode
      | some index =>
          exact actionEarlySelectorConflict_eq_actual_of_code
            left right index hcode

private theorem actionLateSelectorConflict_eq_actual_of_support
    (left right : ℕ)
    (hsupport : actionLateSelectorSupport left right = true) :
    actionLateSelectorConflict actionActualFirstLateSelectorConflict
        actionActualLateSelectorConflicts left right =
      actionActualSelectorConflict left right := by
  unfold actionLateSelectorSupport at hsupport
  by_cases hexceptional :
      actionLateExceptionalSelectorConflict left right = true
  · have hpair : (left, right) ∈ actionLateExceptionalSelectorPairs := by
      simp only [actionLateExceptionalSelectorConflict, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq] at hexceptional
      rcases hexceptional with
        (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩ <;> decide
    rw [actionActualSelectorConflict_eq_lateExceptional left right hpair,
      hexceptional]
    simp [actionLateSelectorConflict, hexceptional]
  · have hcodeSupport : (actionLateSelectorCode left right).isSome = true := by
      simpa only [hexceptional, Bool.false_or] using hsupport
    cases hcode : actionLateSelectorCode left right with
    | none => simp [hcode] at hcodeSupport
    | some code =>
        cases code with
        | none =>
            exact actionLateSelectorConflict_eq_actual_of_first_code
              left right hcode
        | some index =>
            exact actionLateSelectorConflict_eq_actual_of_indexed_code
              left right index hcode

private def actionPackingDegree (selector : ℕ) : ℕ :=
  actionSelectorDegrees[selector]!

private def actionPackingActualConflict (left right : ℕ) : Bool :=
  selectorActivationsConflict actionReducedSelectorActivations left right

private theorem actionActualSelectorConflict_eq_reduced
    (left right : ℕ) :
    actionActualSelectorConflict left right =
      actionPackingActualConflict left right := by
  unfold actionActualSelectorConflict actionPlacedSelectorActivations
    actionPackingActualConflict actionReducedSelectorActivations
  rw [← actionSynthesisSummary_eq_operations,
    show V1.starts actionOperations =
      TopLevelCompilation.regionStarts actionFormalCircuit by rfl,
    actionRegionStarts_eq_reduced]

private def actionPackingRemainderThree : List ℕ :=
  [17, 18, 19, 20, 21, 22, 23, 24, 26, 27, 28, 30, 31, 32, 33,
   34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
   49, 50, 51, 52, 53, 54, 55]

private def actionPackingRemainderSix : List ℕ :=
  [23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39,
   40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]

private def actionPackingRemainderNine : List ℕ :=
  [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]

private def actionPackingRemainderTen : List ℕ :=
  [49, 50, 51, 52, 53, 54, 55]

private theorem actionCompactPacking_length_eq :
    (buildCombinationsWith 9 actionPackingDegree
      (actionPackingConflict actionActualEarlySelectorConflicts
        actionActualFirstLateSelectorConflict actionActualLateSelectorConflicts)
      actionNonzeroSelectors.length actionNonzeroSelectors).length = 11 := by
  rw [actionActualEarlySelectorConflicts_eq_reduced,
    actionActualFirstLateSelectorConflict_eq_reduced,
    actionActualLateSelectorConflicts_eq_reduced]
  decide +kernel

private def actionEarlyQueriedPairs : List (ℕ × ℕ) :=
  [(0, 1), (0, 4), (1, 4), (0, 5), (1, 5), (4, 5), (0, 6), (1, 6),
   (4, 6), (5, 6), (7, 8), (7, 9), (8, 9), (7, 10), (8, 10), (9, 10),
   (11, 12), (11, 13), (12, 13), (11, 14), (12, 14), (11, 15),
   (12, 15), (14, 15), (11, 16), (12, 16), (14, 16), (15, 16), (0, 7),
   (1, 7), (5, 7), (6, 7), (4, 8), (4, 9), (4, 10), (4, 7), (0, 8),
   (1, 8), (6, 8), (0, 9), (1, 9), (6, 9), (5, 8), (5, 10), (5, 11),
   (8, 11), (10, 11), (13, 14), (13, 15), (13, 16), (0, 10), (1, 10),
   (6, 10), (4, 11), (4, 12), (8, 12), (5, 13), (5, 14), (5, 15),
   (5, 16), (5, 9), (6, 11), (9, 11), (6, 12), (9, 12), (10, 12),
   (4, 13), (6, 13), (9, 13), (10, 13), (4, 14), (6, 14), (9, 14),
   (10, 14), (5, 12), (6, 15), (6, 16), (6, 17), (12, 17), (13, 17),
   (14, 17), (15, 17), (4, 15), (9, 15), (10, 15), (7, 11), (7, 12),
   (7, 13), (7, 14), (7, 15), (7, 16), (7, 17), (5, 17), (7, 18),
   (12, 18), (13, 18), (15, 18), (17, 18), (7, 19), (12, 19),
   (13, 19), (15, 19), (17, 19), (7, 20), (12, 20), (13, 20),
   (15, 20), (17, 20), (6, 18), (6, 19), (6, 20), (8, 13), (8, 16),
   (8, 15), (8, 17), (16, 17), (8, 18), (16, 18), (8, 19), (16, 19),
   (8, 20), (16, 20), (4, 16), (4, 17), (11, 17), (0, 11), (1, 11)]

private theorem actionActualSelectorConflict_eq_initial_of_resolved
    (left right : ℕ) (hlt : left < right)
    (hresolved :
      (actionEarlySelectorSupport left right = true ∧
        actionSpecialSelectorConflict left right = false) ∨
      (actionEarlySelectorSupport left right = false ∧
        ((((actionSelectorAnchorClass left = actionSelectorAnchorClass right) ∨
              (left, right) ∈ actionAdditionalSharedColumnPairs) ∧
            actionSpecialSelectorConflict left right = false) ∨
          (left, right) ∈ actionSpecialSeparatedSelectorPairs))) :
    actionPackingActualConflict left right =
      actionInitialSelectorConflict actionActualEarlySelectorConflicts
        left right := by
  rw [← actionActualSelectorConflict_eq_reduced left right]
  rcases hresolved with ⟨hearly, hspecial⟩ | ⟨hearly, hseparated⟩
  · rw [actionInitialSelectorConflict,
      actionEarlySelectorConflict_eq_actual_of_support left right hearly,
      hspecial, Bool.or_false]
  · rw [actionInitialSelectorConflict,
      actionEarlySelectorConflict_eq_false_of_support _ _ _ hearly,
      Bool.false_or]
    rcases hseparated with ⟨hshared, hspecial⟩ | hspecial
    · rw [hspecial]
      have hlocal : actionLocalSelectorsConflict left right = false := by
        apply Bool.eq_false_iff.mpr
        intro hlocal
        have := actionEarlySelectorSupport_eq_true_of_local left right hlocal
        simp_all
      rcases hshared with hanchor | hcommon
      · exact actionActualSelectorConflict_eq_false_of_anchor
          left right hlt hlocal hanchor
      · exact actionActualSelectorConflict_eq_false_of_additionalSharedColumn
          left right hlt hlocal hcommon
    · exact actionActualSelectorConflict_eq_special left right hspecial

private theorem actionEarlyPackingQueries_pairs :
    (packingRemainderQueries 9 actionPackingDegree
      (actionInitialSelectorConflict actionActualEarlySelectorConflicts)
      3 actionNonzeroSelectors).Forall fun query =>
        query.combination.Forall fun left =>
          (left, query.selector) ∈ actionEarlyQueriedPairs := by
  rw [actionActualEarlySelectorConflicts_eq_reduced]
  decide +kernel

private theorem actionEarlyPairs_resolved :
    actionEarlyQueriedPairs.Forall fun pair =>
      pair.1 < pair.2 ∧
        ((actionEarlySelectorSupport pair.1 pair.2 = true ∧
            actionSpecialSelectorConflict pair.1 pair.2 = false) ∨
          (actionEarlySelectorSupport pair.1 pair.2 = false ∧
            ((((actionSelectorAnchorClass pair.1 =
                  actionSelectorAnchorClass pair.2) ∨
                pair ∈ actionAdditionalSharedColumnPairs) ∧
              actionSpecialSelectorConflict pair.1 pair.2 = false) ∨
            pair ∈ actionSpecialSeparatedSelectorPairs))) := by
  decide +kernel

private theorem actionActualPackingRemainder_three_eq :
    packingRemainderWith 9 actionPackingDegree
        actionPackingActualConflict 3 actionNonzeroSelectors =
      actionPackingRemainderThree := by
  rw [show packingRemainderWith 9 actionPackingDegree
      actionPackingActualConflict 3 actionNonzeroSelectors =
    packingRemainderWith 9 actionPackingDegree
      (actionInitialSelectorConflict actionActualEarlySelectorConflicts)
      3 actionNonzeroSelectors by
    apply packingRemainderWith_eq_of_queries
    intro query hquery
    rw [expected_eq_any_of_mem_packingRemainderQueries
      9 3 actionPackingDegree
      (actionInitialSelectorConflict actionActualEarlySelectorConflicts)
      actionNonzeroSelectors query hquery]
    apply List.any_congr_of_forall_mem
    intro left hleft
    have hpair := List.forall_iff_forall_mem.mp
      (List.forall_iff_forall_mem.mp actionEarlyPackingQueries_pairs
        query hquery) left hleft
    have hresolved := List.forall_iff_forall_mem.mp
      actionEarlyPairs_resolved (left, query.selector) hpair
    exact actionActualSelectorConflict_eq_initial_of_resolved
      left query.selector hresolved.1 hresolved.2]
  rw [actionActualEarlySelectorConflicts_eq_reduced]
  decide +kernel

private def actionMiddleQueriedPairs : List (ℕ × ℕ) :=
  [(13, 17), (13, 18), (17, 18), (13, 19), (17, 19), (13, 20),
   (17, 20), (13, 21), (17, 21), (20, 21), (13, 22), (17, 22),
   (20, 22), (21, 22), (13, 23), (17, 23), (20, 23), (21, 23),
   (13, 24), (17, 24), (20, 24), (21, 24), (15, 17), (15, 18),
   (15, 19), (15, 21), (15, 22), (16, 18), (16, 19), (16, 20),
   (16, 21), (16, 22), (22, 23), (16, 23), (16, 17)]

private theorem actionMiddlePackingQueries_pairs :
    (packingRemainderQueries 9 actionPackingDegree
      actionSpecialSelectorConflict 3 actionPackingRemainderThree).Forall
      fun query => query.combination.Forall fun left =>
        (left, query.selector) ∈ actionMiddleQueriedPairs := by
  decide +kernel

private theorem actionMiddlePairs_resolved :
    actionMiddleQueriedPairs.Forall fun pair =>
      pair.1 < pair.2 ∧
        actionEarlySelectorSupport pair.1 pair.2 = false ∧
        ((((actionSelectorAnchorClass pair.1 =
              actionSelectorAnchorClass pair.2) ∨
            pair ∈ actionAdditionalSharedColumnPairs) ∧
          actionSpecialSelectorConflict pair.1 pair.2 = false) ∨
        pair ∈ actionSpecialSeparatedSelectorPairs) := by
  decide +kernel

private theorem actionActualSelectorConflict_eq_special_of_resolved
    (left right : ℕ) (hlt : left < right)
    (hearly : actionEarlySelectorSupport left right = false)
    (hresolved :
      (((actionSelectorAnchorClass left = actionSelectorAnchorClass right) ∨
          (left, right) ∈ actionAdditionalSharedColumnPairs) ∧
        actionSpecialSelectorConflict left right = false) ∨
      (left, right) ∈ actionSpecialSeparatedSelectorPairs) :
    actionPackingActualConflict left right =
      actionSpecialSelectorConflict left right := by
  rw [← actionActualSelectorConflict_eq_reduced left right]
  rcases hresolved with ⟨hshared, hspecial⟩ | hspecial
  · rw [hspecial]
    have hlocal : actionLocalSelectorsConflict left right = false := by
      apply Bool.eq_false_iff.mpr
      intro hlocal
      have hsupport := actionEarlySelectorSupport_eq_true_of_local
        left right hlocal
      simp_all
    rcases hshared with hanchor | hcommon
    · exact actionActualSelectorConflict_eq_false_of_anchor
        left right hlt hlocal hanchor
    · exact actionActualSelectorConflict_eq_false_of_additionalSharedColumn
        left right hlt hlocal hcommon
  · exact actionActualSelectorConflict_eq_special left right hspecial

private theorem actionActualPackingRemainder_six_eq :
    packingRemainderWith 9 actionPackingDegree
        actionPackingActualConflict 6 actionNonzeroSelectors =
      actionPackingRemainderSix := by
  rw [show 6 = 3 + 3 by omega,
    packingRemainderWith_add, actionActualPackingRemainder_three_eq]
  rw [show packingRemainderWith 9 actionPackingDegree
      actionPackingActualConflict 3 actionPackingRemainderThree =
    packingRemainderWith 9 actionPackingDegree
      actionSpecialSelectorConflict 3 actionPackingRemainderThree by
    apply packingRemainderWith_eq_of_queries
    intro query hquery
    rw [expected_eq_any_of_mem_packingRemainderQueries
      9 3 actionPackingDegree actionSpecialSelectorConflict
      actionPackingRemainderThree query hquery]
    apply List.any_congr_of_forall_mem
    intro left hleft
    have hpair := List.forall_iff_forall_mem.mp
      (List.forall_iff_forall_mem.mp actionMiddlePackingQueries_pairs
        query hquery) left hleft
    have hresolved := List.forall_iff_forall_mem.mp
      actionMiddlePairs_resolved (left, query.selector) hpair
    exact actionActualSelectorConflict_eq_special_of_resolved
      left query.selector hresolved.1 hresolved.2.1 hresolved.2.2]
  decide +kernel

private theorem actionLatePackingQueries_bounds :
    (packingRemainderQueries 9 actionPackingDegree
      (actionLateSelectorConflict actionActualFirstLateSelectorConflict
        actionActualLateSelectorConflicts)
      3 actionPackingRemainderSix).Forall fun query =>
        query.combination.Forall fun left =>
          22 ≤ left ∧ left ≠ 25 ∧ left ≠ 29 ∧
            left < query.selector ∧ query.selector ≠ 25 ∧
            query.selector ≠ 29 ∧ query.selector < 42 := by
  rw [actionActualFirstLateSelectorConflict_eq_reduced,
    actionActualLateSelectorConflicts_eq_reduced]
  decide +kernel

private def actionLatePackingSelectors : List ℕ :=
  [22, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38,
   39, 40, 41]

private theorem mem_actionLatePackingSelectors
    (selector : ℕ) (hlower : 22 ≤ selector) (hne25 : selector ≠ 25)
    (hne29 : selector ≠ 29) (hupper : selector < 42) :
    selector ∈ actionLatePackingSelectors := by
  interval_cases selector <;> simp_all [actionLatePackingSelectors]

private theorem actionLatePackingSelectors_resolved :
    actionLatePackingSelectors.Forall fun left =>
      actionLatePackingSelectors.Forall fun right =>
        left < right →
          actionLocalSelectorsConflict left right = false ∧
            (actionLateSelectorSupport left right = true ∨
              (actionLateSelectorSupport left right = false ∧
                ((actionUsesAdviceColumn6 left ∧
                    actionUsesAdviceColumn6 right) ∨
                  actionSelectorAnchorClass left =
                    actionSelectorAnchorClass right ∨
                  (left, right) ∈ actionLateExceptionalSelectorPairs))) := by
  decide +kernel

private theorem actionLatePair_resolved
    (left right : ℕ)
    (hleft : 22 ≤ left) (hneLeft25 : left ≠ 25)
    (hneLeft29 : left ≠ 29) (hlt : left < right)
    (hneRight25 : right ≠ 25) (hneRight29 : right ≠ 29)
    (hright : right < 42) :
    actionLocalSelectorsConflict left right = false ∧
      (actionLateSelectorSupport left right = true ∨
        (actionLateSelectorSupport left right = false ∧
          ((actionUsesAdviceColumn6 left ∧ actionUsesAdviceColumn6 right) ∨
            actionSelectorAnchorClass left = actionSelectorAnchorClass right ∨
            (left, right) ∈ actionLateExceptionalSelectorPairs))) := by
  have hleftUpper : left < 42 := Nat.lt_trans hlt hright
  exact List.forall_iff_forall_mem.mp
    (List.forall_iff_forall_mem.mp actionLatePackingSelectors_resolved
      left (mem_actionLatePackingSelectors left hleft hneLeft25
        hneLeft29 hleftUpper))
    right (mem_actionLatePackingSelectors right (Nat.le_trans hleft hlt.le)
      hneRight25 hneRight29 hright) hlt

private theorem actionActualSelectorConflict_eq_late_of_resolved
    (left right : ℕ) (hlt : left < right)
    (hlocal : actionLocalSelectorsConflict left right = false)
    (hresolved :
      actionLateSelectorSupport left right = true ∨
        (actionLateSelectorSupport left right = false ∧
          ((actionUsesAdviceColumn6 left ∧ actionUsesAdviceColumn6 right) ∨
            actionSelectorAnchorClass left = actionSelectorAnchorClass right ∨
            (left, right) ∈ actionLateExceptionalSelectorPairs))) :
    actionPackingActualConflict left right =
      actionLateSelectorConflict actionActualFirstLateSelectorConflict
        actionActualLateSelectorConflicts left right := by
  rw [← actionActualSelectorConflict_eq_reduced left right]
  rcases hresolved with hlate | ⟨hlate, hseparated⟩
  · exact (actionLateSelectorConflict_eq_actual_of_support
      left right hlate).symm
  · rw [actionLateSelectorConflict_eq_false_of_support _ _ _ _ hlate]
    rcases hseparated with hcolumn | hanchor | hexceptional
    · exact actionActualSelectorConflict_eq_false_of_sharedColumn
        left right hlt hlocal (.column .advice 6)
        (actionUsesAdviceColumn6_useColumn left hcolumn.1)
        (actionUsesAdviceColumn6_useColumn right hcolumn.2)
    · exact actionActualSelectorConflict_eq_false_of_anchor
        left right hlt hlocal hanchor
    · rw [actionActualSelectorConflict_eq_lateExceptional
          left right hexceptional]
      unfold actionLateSelectorSupport at hlate
      simp only [Bool.or_eq_false_eq_eq_false_and_eq_false] at hlate
      exact hlate.1

private theorem actionActualPackingRemainder_nine_eq :
    packingRemainderWith 9 actionPackingDegree
        actionPackingActualConflict 9 actionNonzeroSelectors =
      actionPackingRemainderNine := by
  rw [show 9 = 6 + 3 by omega,
    packingRemainderWith_add, actionActualPackingRemainder_six_eq]
  rw [show packingRemainderWith 9 actionPackingDegree
      actionPackingActualConflict 3 actionPackingRemainderSix =
    packingRemainderWith 9 actionPackingDegree
      (actionLateSelectorConflict actionActualFirstLateSelectorConflict
        actionActualLateSelectorConflicts)
      3 actionPackingRemainderSix by
    apply packingRemainderWith_eq_of_queries
    intro query hquery
    rw [expected_eq_any_of_mem_packingRemainderQueries
      9 3 actionPackingDegree
      (actionLateSelectorConflict actionActualFirstLateSelectorConflict
        actionActualLateSelectorConflicts)
      actionPackingRemainderSix query hquery]
    apply List.any_congr_of_forall_mem
    intro left hleft
    have hbounds := List.forall_iff_forall_mem.mp
      (List.forall_iff_forall_mem.mp actionLatePackingQueries_bounds
        query hquery) left hleft
    obtain ⟨hleftBound, hneLeft25, hneLeft29, hlt,
      hneRight25, hneRight29, hrightBound⟩ := hbounds
    have hresolved := actionLatePair_resolved left query.selector
      hleftBound hneLeft25 hneLeft29 hlt hneRight25 hneRight29
      hrightBound
    exact actionActualSelectorConflict_eq_late_of_resolved
      left query.selector hlt hresolved.1 hresolved.2]
  rw [actionActualFirstLateSelectorConflict_eq_reduced,
    actionActualLateSelectorConflicts_eq_reduced]
  decide +kernel

private def actionFinalPackingSelectors : List ℕ :=
  [42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55]

private theorem actionFinalPackingSelectors_resolved :
    actionFinalPackingSelectors.Forall fun left =>
      actionFinalPackingSelectors.Forall fun right =>
        left < right →
          actionLocalSelectorsConflict left right = false ∧
            actionUsesAdviceColumn6 left ∧ actionUsesAdviceColumn6 right := by
  decide +kernel

private theorem actionFinalPackingQueries_bounds
    (selectors : List ℕ)
    (hselectors : selectors = actionPackingRemainderNine ∨
      selectors = actionPackingRemainderTen) :
    (packingRemainderQueries 9 actionPackingDegree
      (fun _ _ => false) 1 selectors).Forall fun query =>
        query.combination.Forall fun left =>
          left ∈ actionFinalPackingSelectors ∧
            query.selector ∈ actionFinalPackingSelectors ∧
            left < query.selector := by
  rcases hselectors with rfl | rfl <;> decide +kernel

private theorem actionActualSelectorConflict_eq_false_of_finalPair
    (left right : ℕ) (hleft : left ∈ actionFinalPackingSelectors)
    (hright : right ∈ actionFinalPackingSelectors) (hlt : left < right) :
    actionPackingActualConflict left right = false := by
  rw [← actionActualSelectorConflict_eq_reduced left right]
  have hresolved := List.forall_iff_forall_mem.mp
    (List.forall_iff_forall_mem.mp actionFinalPackingSelectors_resolved
      left hleft) right hright hlt
  exact actionActualSelectorConflict_eq_false_of_sharedColumn
    left right hlt hresolved.1 (.column .advice 6)
    (actionUsesAdviceColumn6_useColumn left hresolved.2.1)
    (actionUsesAdviceColumn6_useColumn right hresolved.2.2)

private theorem actionActualPackingRemainder_final_eq
    (selectors : List ℕ)
    (hselectors : selectors = actionPackingRemainderNine ∨
      selectors = actionPackingRemainderTen) :
    packingRemainderWith 9 actionPackingDegree
        actionPackingActualConflict 1 selectors =
      packingRemainderWith 9 actionPackingDegree
        (fun _ _ => false) 1 selectors := by
  apply packingRemainderWith_eq_of_queries
  intro query hquery
  rw [expected_eq_any_of_mem_packingRemainderQueries
    9 1 actionPackingDegree (fun _ _ => false) selectors query hquery]
  apply List.any_congr_of_forall_mem
  intro left hleft
  have hbounds := List.forall_iff_forall_mem.mp
    (List.forall_iff_forall_mem.mp
      (actionFinalPackingQueries_bounds selectors hselectors) query hquery)
    left hleft
  rw [actionActualSelectorConflict_eq_false_of_finalPair
    left query.selector hbounds.1 hbounds.2.1 hbounds.2.2]

private theorem actionActualPackingRemainder_ten_eq :
    packingRemainderWith 9 actionPackingDegree
        actionPackingActualConflict 10 actionNonzeroSelectors =
      actionPackingRemainderTen := by
  rw [show 10 = 9 + 1 by omega,
    packingRemainderWith_add, actionActualPackingRemainder_nine_eq,
    actionActualPackingRemainder_final_eq actionPackingRemainderNine
      (Or.inl rfl)]
  decide +kernel

private theorem actionActualPackingRemainder_eleven_eq :
    packingRemainderWith 9 actionPackingDegree
        actionPackingActualConflict 11 actionNonzeroSelectors = [] := by
  rw [show 11 = 10 + 1 by omega,
    packingRemainderWith_add, actionActualPackingRemainder_ten_eq,
    actionActualPackingRemainder_final_eq actionPackingRemainderTen
      (Or.inr rfl)]
  decide +kernel

private theorem actionActualPacking_length_eq :
    (buildCombinationsWith 9 actionPackingDegree
      actionPackingActualConflict actionNonzeroSelectors.length
      actionNonzeroSelectors).length = 11 := by
  apply buildCombinationsWith_length_eq_of_checkpoints
  · omega
  · unfold actionNonzeroSelectors
    decide
  · rw [actionActualPackingRemainder_ten_eq]
    simp [actionPackingRemainderTen]
  · exact actionActualPackingRemainder_eleven_eq

private theorem actionActualPacking_length_eq_sourceDegree :
    (buildCombinationsWith 9
      (fun selector => actionSelectorDegrees[selector]!)
      actionPackingActualConflict actionNonzeroSelectors.length
      actionNonzeroSelectors).length = 11 := by
  simpa only [actionPackingDegree] using actionActualPacking_length_eq

private theorem actionReducedPacking_length_eq :
    (buildCombinationsWith 9
      (fun selector => actionSelectorDegrees[selector]!)
      (selectorActivationsConflict actionReducedSelectorActivations)
      actionNonzeroSelectors.length actionNonzeroSelectors).length = 11 := by
  simpa only [actionPackingActualConflict] using
    actionActualPacking_length_eq_sourceDegree

theorem actionSelectorColumnCount_eq :
    selectorColumnCountWith (List.range 56) 9
      (fun selector => actionSelectorDegrees[selector]!)
      (selectorActivationsConflict actionReducedSelectorActivations) = 15 := by
  have hcount := selectorColumnCountWith_eq_of_partitions
    (List.range 56) [2, 3, 25, 29] actionNonzeroSelectors 9 11
    (fun selector => actionSelectorDegrees[selector]!)
    (selectorActivationsConflict actionReducedSelectorActivations)
    actionSelectorDegreePartitions.1 actionSelectorDegreePartitions.2
    actionReducedPacking_length_eq
  norm_num only [List.length_cons, List.length_nil] at hcount
  exact hcount

end Zcash.Circuits.Action
