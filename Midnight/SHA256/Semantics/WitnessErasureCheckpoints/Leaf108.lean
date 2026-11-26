import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round40Checked : Checked StructuralCheckpoints.round40Action
    StructuralCheckpoints.round39After StructuralCheckpoints.round40Output StructuralCheckpoints.round40After
    ((WitnessCheckpoints.round40Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round40
    sha256_witness_unfold round40
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
