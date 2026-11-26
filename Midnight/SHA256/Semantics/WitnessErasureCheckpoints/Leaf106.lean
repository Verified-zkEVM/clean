import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round38Checked : Checked StructuralCheckpoints.round38Action
    StructuralCheckpoints.round37After StructuralCheckpoints.round38Output StructuralCheckpoints.round38After
    ((WitnessCheckpoints.round38Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round38
    sha256_witness_unfold round38
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
