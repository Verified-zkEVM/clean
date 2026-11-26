import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare12Checked : Checked StructuralCheckpoints.prepare12Action
    StructuralCheckpoints.prepare11After StructuralCheckpoints.prepare12Output StructuralCheckpoints.prepare12After
    ((WitnessCheckpoints.prepare12Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
