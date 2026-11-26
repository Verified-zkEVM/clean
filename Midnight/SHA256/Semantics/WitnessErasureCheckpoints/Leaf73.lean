import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round5Checked : Checked StructuralCheckpoints.round5Action
    StructuralCheckpoints.round4After StructuralCheckpoints.round5Output StructuralCheckpoints.round5After
    ((WitnessCheckpoints.round5Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round5
    sha256_witness_unfold round5
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
