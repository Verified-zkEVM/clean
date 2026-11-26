import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round33Checked : Checked StructuralCheckpoints.round33Action
    StructuralCheckpoints.round32After StructuralCheckpoints.round33Output StructuralCheckpoints.round33After
    ((WitnessCheckpoints.round33Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round33
    sha256_witness_unfold round33
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
