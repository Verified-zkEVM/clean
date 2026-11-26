import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand46Checked : Checked StructuralCheckpoints.expand46Action
    StructuralCheckpoints.expand45After StructuralCheckpoints.expand46Output StructuralCheckpoints.expand46After
    ((WitnessCheckpoints.expand46Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand46
    sha256_witness_unfold expand46
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
