import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round20Checked : Checked StructuralCheckpoints.round20Action
    StructuralCheckpoints.round19After StructuralCheckpoints.round20Output StructuralCheckpoints.round20After
    ((WitnessCheckpoints.round20Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round20
    sha256_witness_unfold round20
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
