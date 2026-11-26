import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand40Checked : Checked StructuralCheckpoints.expand40Action
    StructuralCheckpoints.expand39After StructuralCheckpoints.expand40Output StructuralCheckpoints.expand40After
    ((WitnessCheckpoints.expand40Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand40
    sha256_witness_unfold expand40
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
