import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round3Checked : Checked StructuralCheckpoints.round3Action
    StructuralCheckpoints.round2After StructuralCheckpoints.round3Output StructuralCheckpoints.round3After
    ((WitnessCheckpoints.round3Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round3
    sha256_witness_unfold round3
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
