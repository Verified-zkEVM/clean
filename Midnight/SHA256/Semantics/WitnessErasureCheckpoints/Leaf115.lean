import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round47Checked : Checked StructuralCheckpoints.round47Action
    StructuralCheckpoints.round46After StructuralCheckpoints.round47Output StructuralCheckpoints.round47After
    ((WitnessCheckpoints.round47Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round47
    sha256_witness_unfold round47
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
