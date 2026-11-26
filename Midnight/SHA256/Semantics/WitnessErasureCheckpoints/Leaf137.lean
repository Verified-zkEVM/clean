import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem serialize4Checked : Checked StructuralCheckpoints.serialize4Action
    StructuralCheckpoints.serialize3After StructuralCheckpoints.serialize4Output StructuralCheckpoints.serialize4After
    ((WitnessCheckpoints.serialize4Operations 0).map WitnessErasure.Code.encode) := by
  conv => arg 5; cbv
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
