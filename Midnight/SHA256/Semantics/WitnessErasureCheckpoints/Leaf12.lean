import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare8Checked : Checked StructuralCheckpoints.prepare8Action
    StructuralCheckpoints.prepare7After StructuralCheckpoints.prepare8Output StructuralCheckpoints.prepare8After
    ((WitnessCheckpoints.prepare8Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
