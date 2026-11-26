import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand29Checked : Checked StructuralCheckpoints.expand29Action
    StructuralCheckpoints.expand28After StructuralCheckpoints.expand29Output StructuralCheckpoints.expand29After
    ((WitnessCheckpoints.expand29Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand29
    sha256_witness_unfold expand29
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
