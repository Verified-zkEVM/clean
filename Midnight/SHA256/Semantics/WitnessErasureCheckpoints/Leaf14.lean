import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare10Checked : Checked StructuralCheckpoints.prepare10Action
    StructuralCheckpoints.prepare9After StructuralCheckpoints.prepare10Output StructuralCheckpoints.prepare10After
    ((WitnessCheckpoints.prepare10Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
