import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand27Checked : Checked StructuralCheckpoints.expand27Action
    StructuralCheckpoints.expand26After StructuralCheckpoints.expand27Output StructuralCheckpoints.expand27After
    ((WitnessCheckpoints.expand27Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand27
    sha256_witness_unfold expand27
    cbv
    repeat' apply And.intro
    all_goals trivial

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
