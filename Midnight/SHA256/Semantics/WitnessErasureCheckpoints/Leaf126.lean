import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round58Checked : Checked StructuralCheckpoints.round58Action
    StructuralCheckpoints.round57After StructuralCheckpoints.round58Output StructuralCheckpoints.round58After
    ((WitnessCheckpoints.round58Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round58
    sha256_witness_unfold round58
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
