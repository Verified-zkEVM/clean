import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem serialize7Checked : Checked StructuralCheckpoints.serialize7Action
    StructuralCheckpoints.serialize6After StructuralCheckpoints.serialize7Output StructuralCheckpoints.serialize7After
    ((WitnessCheckpoints.serialize7Operations 0).map WitnessErasure.Code.encode) := by
  conv => arg 5; cbv
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
