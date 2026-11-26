import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round13Checked : Checked StructuralCheckpoints.round13Action
    StructuralCheckpoints.round12After StructuralCheckpoints.round13Output StructuralCheckpoints.round13After
    ((WitnessCheckpoints.round13Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round13
    sha256_witness_unfold round13
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
