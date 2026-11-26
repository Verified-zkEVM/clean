import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare4Checked : Checked StructuralCheckpoints.prepare4Action
    StructuralCheckpoints.prepare3After StructuralCheckpoints.prepare4Output StructuralCheckpoints.prepare4After
    ((WitnessCheckpoints.prepare4Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
