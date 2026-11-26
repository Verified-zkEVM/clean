import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round21Checked : Checked StructuralCheckpoints.round21Action
    StructuralCheckpoints.round20After StructuralCheckpoints.round21Output StructuralCheckpoints.round21After
    ((WitnessCheckpoints.round21Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round21
    sha256_witness_unfold round21
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
