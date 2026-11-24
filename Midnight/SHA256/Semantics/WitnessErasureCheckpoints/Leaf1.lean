import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem initialChecked : Checked StructuralCheckpoints.initialAction
    StructuralCheckpoints.inputAfter StructuralCheckpoints.initialOutput StructuralCheckpoints.initialAfter
    ((WitnessCheckpoints.initialOperations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv
    repeat' apply And.intro
    all_goals trivial

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
