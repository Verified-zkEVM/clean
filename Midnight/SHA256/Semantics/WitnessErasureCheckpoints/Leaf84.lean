import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round16Checked : Checked StructuralCheckpoints.round16Action
    StructuralCheckpoints.round15After StructuralCheckpoints.round16Output StructuralCheckpoints.round16After
    ((WitnessCheckpoints.round16Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round16
    sha256_witness_unfold round16
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
