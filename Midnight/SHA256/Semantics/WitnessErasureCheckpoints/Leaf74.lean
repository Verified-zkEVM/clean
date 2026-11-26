import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round6Checked : Checked StructuralCheckpoints.round6Action
    StructuralCheckpoints.round5After StructuralCheckpoints.round6Output StructuralCheckpoints.round6After
    ((WitnessCheckpoints.round6Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round6
    sha256_witness_unfold round6
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
