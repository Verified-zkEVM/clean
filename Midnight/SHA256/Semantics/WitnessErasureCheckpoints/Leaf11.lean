import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare7Checked : Checked StructuralCheckpoints.prepare7Action
    StructuralCheckpoints.prepare6After StructuralCheckpoints.prepare7Output StructuralCheckpoints.prepare7After
    ((WitnessCheckpoints.prepare7Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
