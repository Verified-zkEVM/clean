import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem paddingChecked : Checked StructuralCheckpoints.paddingAction
    StructuralCheckpoints.initialAfter StructuralCheckpoints.paddingOutput StructuralCheckpoints.paddingAfter
    ((WitnessCheckpoints.paddingOperations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
