import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem serialize6Checked : Checked StructuralCheckpoints.serialize6Action
    StructuralCheckpoints.serialize5After StructuralCheckpoints.serialize6Output StructuralCheckpoints.serialize6After
    ((WitnessCheckpoints.serialize6Operations 0).map WitnessErasure.Code.encode) := by
  conv => arg 5; cbv
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
