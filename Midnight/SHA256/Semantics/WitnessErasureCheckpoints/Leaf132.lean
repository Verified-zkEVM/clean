import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem feedforwardChecked : Checked StructuralCheckpoints.feedforwardAction
    StructuralCheckpoints.round63After StructuralCheckpoints.feedforwardOutput StructuralCheckpoints.feedforwardAfter
    ((WitnessCheckpoints.feedforwardOperations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv
    repeat' apply And.intro
    all_goals trivial

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
