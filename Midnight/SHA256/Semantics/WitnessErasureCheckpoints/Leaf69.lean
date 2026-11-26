import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round1Checked : Checked StructuralCheckpoints.round1Action
    StructuralCheckpoints.round0After StructuralCheckpoints.round1Output StructuralCheckpoints.round1After
    ((WitnessCheckpoints.round1Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round1
    sha256_witness_unfold round1
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
