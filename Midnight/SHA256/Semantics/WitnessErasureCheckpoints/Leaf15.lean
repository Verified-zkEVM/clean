import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem prepare11Checked : Checked StructuralCheckpoints.prepare11Action
    StructuralCheckpoints.prepare10After StructuralCheckpoints.prepare11Output StructuralCheckpoints.prepare11After
    ((WitnessCheckpoints.prepare11Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
