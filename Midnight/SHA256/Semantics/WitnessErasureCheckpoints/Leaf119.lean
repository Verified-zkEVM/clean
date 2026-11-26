import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round51Checked : Checked StructuralCheckpoints.round51Action
    StructuralCheckpoints.round50After StructuralCheckpoints.round51Output StructuralCheckpoints.round51After
    ((WitnessCheckpoints.round51Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round51
    sha256_witness_unfold round51
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
