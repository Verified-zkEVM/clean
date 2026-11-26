import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round18Checked : Checked StructuralCheckpoints.round18Action
    StructuralCheckpoints.round17After StructuralCheckpoints.round18Output StructuralCheckpoints.round18After
    ((WitnessCheckpoints.round18Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round18
    sha256_witness_unfold round18
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
