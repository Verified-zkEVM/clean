import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare3Checked : Checked StructuralCheckpoints.prepare3Action
    StructuralCheckpoints.prepare2After StructuralCheckpoints.prepare3Output StructuralCheckpoints.prepare3After
    ((WitnessCheckpoints.prepare3Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
