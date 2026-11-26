import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem packingChecked : Checked StructuralCheckpoints.packingAction
    StructuralCheckpoints.paddingAfter StructuralCheckpoints.packingOutput StructuralCheckpoints.packingAfter
    ((WitnessCheckpoints.packingOperations 0).map WitnessErasure.Code.encode) := by
  conv => arg 5; cbv
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
