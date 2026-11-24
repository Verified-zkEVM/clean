import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem serialize2Checked : Checked StructuralCheckpoints.serialize2Action
    StructuralCheckpoints.serialize1After StructuralCheckpoints.serialize2Output StructuralCheckpoints.serialize2After
    ((WitnessCheckpoints.serialize2Operations 0).map WitnessErasure.Code.encode) := by
  conv => arg 5; cbv
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv
    repeat' apply And.intro
    all_goals trivial

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
