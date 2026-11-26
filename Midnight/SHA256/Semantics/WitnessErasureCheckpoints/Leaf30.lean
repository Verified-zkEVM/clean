import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand26Checked : Checked StructuralCheckpoints.expand26Action
    StructuralCheckpoints.expand25After StructuralCheckpoints.expand26Output StructuralCheckpoints.expand26After
    ((WitnessCheckpoints.expand26Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand26
    sha256_witness_unfold expand26
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
