import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare2Checked : Checked StructuralCheckpoints.prepare2Action
    StructuralCheckpoints.prepare1After StructuralCheckpoints.prepare2Output StructuralCheckpoints.prepare2After
    ((WitnessCheckpoints.prepare2Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
