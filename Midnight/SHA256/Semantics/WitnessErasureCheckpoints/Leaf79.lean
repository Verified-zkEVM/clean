import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round11Checked : Checked StructuralCheckpoints.round11Action
    StructuralCheckpoints.round10After StructuralCheckpoints.round11Output StructuralCheckpoints.round11After
    ((WitnessCheckpoints.round11Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round11
    sha256_witness_unfold round11
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
