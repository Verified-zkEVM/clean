import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round50Checked : Checked StructuralCheckpoints.round50Action
    StructuralCheckpoints.round49After StructuralCheckpoints.round50Output StructuralCheckpoints.round50After
    ((WitnessCheckpoints.round50Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round50
    sha256_witness_unfold round50
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
