import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare1Checked : Checked StructuralCheckpoints.prepare1Action
    StructuralCheckpoints.prepare0After StructuralCheckpoints.prepare1Output StructuralCheckpoints.prepare1After
    ((WitnessCheckpoints.prepare1Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv
    repeat' apply And.intro
    all_goals trivial

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
