import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round39Checked : Checked StructuralCheckpoints.round39Action
    StructuralCheckpoints.round38After StructuralCheckpoints.round39Output StructuralCheckpoints.round39After
    ((WitnessCheckpoints.round39Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round39
    sha256_witness_unfold round39
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
