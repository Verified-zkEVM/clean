import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round53Checked : Checked StructuralCheckpoints.round53Action
    StructuralCheckpoints.round52After StructuralCheckpoints.round53Output StructuralCheckpoints.round53After
    ((WitnessCheckpoints.round53Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round53
    sha256_witness_unfold round53
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
