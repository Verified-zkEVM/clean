import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round12Checked : Checked StructuralCheckpoints.round12Action
    StructuralCheckpoints.round11After StructuralCheckpoints.round12Output StructuralCheckpoints.round12After
    ((WitnessCheckpoints.round12Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round12
    sha256_witness_unfold round12
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
