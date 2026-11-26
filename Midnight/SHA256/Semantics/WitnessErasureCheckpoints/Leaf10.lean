import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare6Checked : Checked StructuralCheckpoints.prepare6Action
    StructuralCheckpoints.prepare5After StructuralCheckpoints.prepare6Output StructuralCheckpoints.prepare6After
    ((WitnessCheckpoints.prepare6Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
