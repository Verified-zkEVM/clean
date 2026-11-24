import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem publicChecked : Checked StructuralCheckpoints.publicAction
    StructuralCheckpoints.serialize7After StructuralCheckpoints.publicOutput StructuralCheckpoints.publicAfter
    ((WitnessCheckpoints.publicOperations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
