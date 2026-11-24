import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare9Checked : Checked StructuralCheckpoints.prepare9Action
    StructuralCheckpoints.prepare8After StructuralCheckpoints.prepare9Output StructuralCheckpoints.prepare9After
    ((WitnessCheckpoints.prepare9Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv
    repeat' apply And.intro
    all_goals trivial

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
