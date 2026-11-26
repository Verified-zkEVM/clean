import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round0Checked : Checked StructuralCheckpoints.round0Action
    StructuralCheckpoints.expand63After StructuralCheckpoints.round0Output StructuralCheckpoints.round0After
    ((WitnessCheckpoints.round0Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round0
    sha256_witness_unfold round0
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
