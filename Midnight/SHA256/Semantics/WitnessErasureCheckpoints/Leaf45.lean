import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand41Checked : Checked StructuralCheckpoints.expand41Action
    StructuralCheckpoints.expand40After StructuralCheckpoints.expand41Output StructuralCheckpoints.expand41After
    ((WitnessCheckpoints.expand41Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand41
    sha256_witness_unfold expand41
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
