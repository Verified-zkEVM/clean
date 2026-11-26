import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand39Checked : Checked StructuralCheckpoints.expand39Action
    StructuralCheckpoints.expand38After StructuralCheckpoints.expand39Output StructuralCheckpoints.expand39After
    ((WitnessCheckpoints.expand39Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand39
    sha256_witness_unfold expand39
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
