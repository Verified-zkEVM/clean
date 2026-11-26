import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round26Checked : Checked StructuralCheckpoints.round26Action
    StructuralCheckpoints.round25After StructuralCheckpoints.round26Output StructuralCheckpoints.round26After
    ((WitnessCheckpoints.round26Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round26
    sha256_witness_unfold round26
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
