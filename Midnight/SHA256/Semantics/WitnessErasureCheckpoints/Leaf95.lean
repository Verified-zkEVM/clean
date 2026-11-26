import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round27Checked : Checked StructuralCheckpoints.round27Action
    StructuralCheckpoints.round26After StructuralCheckpoints.round27Output StructuralCheckpoints.round27After
    ((WitnessCheckpoints.round27Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round27
    sha256_witness_unfold round27
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
