import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round2Checked : Checked StructuralCheckpoints.round2Action
    StructuralCheckpoints.round1After StructuralCheckpoints.round2Output StructuralCheckpoints.round2After
    ((WitnessCheckpoints.round2Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round2
    sha256_witness_unfold round2
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
