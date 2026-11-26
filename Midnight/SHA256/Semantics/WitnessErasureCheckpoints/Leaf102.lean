import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round34Checked : Checked StructuralCheckpoints.round34Action
    StructuralCheckpoints.round33After StructuralCheckpoints.round34Output StructuralCheckpoints.round34After
    ((WitnessCheckpoints.round34Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round34
    sha256_witness_unfold round34
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
