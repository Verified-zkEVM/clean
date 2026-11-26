import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand33Checked : Checked StructuralCheckpoints.expand33Action
    StructuralCheckpoints.expand32After StructuralCheckpoints.expand33Output StructuralCheckpoints.expand33After
    ((WitnessCheckpoints.expand33Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand33
    sha256_witness_unfold expand33
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
