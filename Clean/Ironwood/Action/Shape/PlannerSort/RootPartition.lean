import Clean.Ironwood.Action.Shape.PlannerSort.RootPartitionData

/-! Kernel-checked evaluation of the Action sort's two-step root partition. -/

namespace Zcash.Circuits.Action.PlannerSort

open Halo2 FloorPlanner

set_option maxRecDepth 1000000 in
theorem rootSetup_eq :
    Pdqsort.preparePartition rootSelected rootPivotIndex less =
      rootSetup := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem rootBlockInput_eq :
    rootSetup.values.extract (1 + rootSetup.left) (1 + rootSetup.right) =
      rootBlockInput := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem rootBlockStep0 :
    Pdqsort.blockLoopStep rootSetup.pivot less
      (Pdqsort.initialBlockLoopState rootBlockInput) =
        .yield rootBlockState1 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem rootBlockStep1 :
    Pdqsort.blockLoopStep rootSetup.pivot less rootBlockState1 =
      .done rootBlockState2 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem rootBlockRun :
    Pdqsort.runSteps (Pdqsort.blockLoopStep rootSetup.pivot less)
      (rootBlockInput.size + 4)
      (Pdqsort.initialBlockLoopState rootBlockInput) = rootBlockState2 := by
  have hsize : rootBlockInput.size + 4 = 361 := by decide +kernel
  rw [hsize, Pdqsort.runSteps.eq_2, rootBlockStep0]
  simp only
  rw [Pdqsort.runSteps.eq_2, rootBlockStep1]

set_option maxRecDepth 1000000 in
theorem rootBlocks :
    Pdqsort.partitionInBlocks rootBlockInput rootSetup.pivot less =
      rootBlockResult := by
  rw [Pdqsort.partitionInBlocks_eq_partitionInBlocksBySteps]
  unfold Pdqsort.partitionInBlocksBySteps
  rw [rootBlockRun]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem rootPartition :
    Pdqsort.partitionP rootSelected rootPivotIndex less =
      rootPartitionResult := by
  rw [Pdqsort.partitionP_eq_partitionPFactored]
  unfold Pdqsort.partitionPFactored
  rw [rootSetup_eq]
  simp only
  rw [rootBlockInput_eq, rootBlocks]
  decide +kernel

end Zcash.Circuits.Action.PlannerSort
