import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round41Checked : Checked StructuralCheckpoints.round41Action
    StructuralCheckpoints.round40After StructuralCheckpoints.round41Output StructuralCheckpoints.round41After
    ((WitnessCheckpoints.round41Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round41
    sha256_witness_unfold round41
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
