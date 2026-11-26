import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand47Checked : Checked StructuralCheckpoints.expand47Action
    StructuralCheckpoints.expand46After StructuralCheckpoints.expand47Output StructuralCheckpoints.expand47After
    ((WitnessCheckpoints.expand47Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand47
    sha256_witness_unfold expand47
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
