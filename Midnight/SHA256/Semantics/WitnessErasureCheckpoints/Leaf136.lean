import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem serialize3Checked : Checked StructuralCheckpoints.serialize3Action
    StructuralCheckpoints.serialize2After StructuralCheckpoints.serialize3Output StructuralCheckpoints.serialize3After
    ((WitnessCheckpoints.serialize3Operations 0).map WitnessErasure.Code.encode) := by
  conv => arg 5; cbv
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
