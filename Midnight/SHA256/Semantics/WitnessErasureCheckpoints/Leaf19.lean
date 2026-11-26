import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare15Checked : Checked StructuralCheckpoints.prepare15Action
    StructuralCheckpoints.prepare14After StructuralCheckpoints.prepare15Output StructuralCheckpoints.prepare15After
    ((WitnessCheckpoints.prepare15Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
