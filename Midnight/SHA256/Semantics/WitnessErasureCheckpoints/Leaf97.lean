import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round29Checked : Checked StructuralCheckpoints.round29Action
    StructuralCheckpoints.round28After StructuralCheckpoints.round29Output StructuralCheckpoints.round29After
    ((WitnessCheckpoints.round29Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round29
    sha256_witness_unfold round29
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
