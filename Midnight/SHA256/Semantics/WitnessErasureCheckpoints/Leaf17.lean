import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare13Checked : Checked StructuralCheckpoints.prepare13Action
    StructuralCheckpoints.prepare12After StructuralCheckpoints.prepare13Output StructuralCheckpoints.prepare13After
    ((WitnessCheckpoints.prepare13Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
