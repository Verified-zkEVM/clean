import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round57Checked : Checked StructuralCheckpoints.round57Action
    StructuralCheckpoints.round56After StructuralCheckpoints.round57Output StructuralCheckpoints.round57After
    ((WitnessCheckpoints.round57Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round57
    sha256_witness_unfold round57
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
