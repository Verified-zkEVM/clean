import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round24Checked : Checked StructuralCheckpoints.round24Action
    StructuralCheckpoints.round23After StructuralCheckpoints.round24Output StructuralCheckpoints.round24After
    ((WitnessCheckpoints.round24Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round24
    sha256_witness_unfold round24
    cbv
    repeat' apply And.intro
    all_goals trivial

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
