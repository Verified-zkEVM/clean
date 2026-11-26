import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round56Checked : Checked StructuralCheckpoints.round56Action
    StructuralCheckpoints.round55After StructuralCheckpoints.round56Output StructuralCheckpoints.round56After
    ((WitnessCheckpoints.round56Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round56
    sha256_witness_unfold round56
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
