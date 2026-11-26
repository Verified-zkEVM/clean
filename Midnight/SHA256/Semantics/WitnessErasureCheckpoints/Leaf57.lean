import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand53Checked : Checked StructuralCheckpoints.expand53Action
    StructuralCheckpoints.expand52After StructuralCheckpoints.expand53Output StructuralCheckpoints.expand53After
    ((WitnessCheckpoints.expand53Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand53
    sha256_witness_unfold expand53
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
