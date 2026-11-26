import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round25Checked : Checked StructuralCheckpoints.round25Action
    StructuralCheckpoints.round24After StructuralCheckpoints.round25Output StructuralCheckpoints.round25After
    ((WitnessCheckpoints.round25Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round25
    sha256_witness_unfold round25
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
