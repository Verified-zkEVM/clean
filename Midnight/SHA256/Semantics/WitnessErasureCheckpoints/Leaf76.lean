import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round8Checked : Checked StructuralCheckpoints.round8Action
    StructuralCheckpoints.round7After StructuralCheckpoints.round8Output StructuralCheckpoints.round8After
    ((WitnessCheckpoints.round8Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round8
    sha256_witness_unfold round8
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
