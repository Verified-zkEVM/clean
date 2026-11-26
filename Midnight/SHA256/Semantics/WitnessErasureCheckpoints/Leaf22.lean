import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand18Checked : Checked StructuralCheckpoints.expand18Action
    StructuralCheckpoints.expand17After StructuralCheckpoints.expand18Output StructuralCheckpoints.expand18After
    ((WitnessCheckpoints.expand18Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand18
    sha256_witness_unfold expand18
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
