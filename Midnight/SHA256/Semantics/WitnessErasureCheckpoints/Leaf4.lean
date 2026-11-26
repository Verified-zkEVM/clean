import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare0Checked : Checked StructuralCheckpoints.prepare0Action
    StructuralCheckpoints.packingAfter StructuralCheckpoints.prepare0Output StructuralCheckpoints.prepare0After
    ((WitnessCheckpoints.prepare0Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
