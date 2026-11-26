import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round59Checked : Checked StructuralCheckpoints.round59Action
    StructuralCheckpoints.round58After StructuralCheckpoints.round59Output StructuralCheckpoints.round59After
    ((WitnessCheckpoints.round59Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round59
    sha256_witness_unfold round59
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
