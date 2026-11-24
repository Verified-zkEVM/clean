import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare5Checked : Checked StructuralCheckpoints.prepare5Action
    StructuralCheckpoints.prepare4After StructuralCheckpoints.prepare5Output StructuralCheckpoints.prepare5After
    ((WitnessCheckpoints.prepare5Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv
    repeat' apply And.intro
    all_goals trivial

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
