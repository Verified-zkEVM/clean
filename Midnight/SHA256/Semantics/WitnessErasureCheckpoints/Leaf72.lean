import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round4Checked : Checked StructuralCheckpoints.round4Action
    StructuralCheckpoints.round3After StructuralCheckpoints.round4Output StructuralCheckpoints.round4After
    ((WitnessCheckpoints.round4Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round4
    sha256_witness_unfold round4
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
