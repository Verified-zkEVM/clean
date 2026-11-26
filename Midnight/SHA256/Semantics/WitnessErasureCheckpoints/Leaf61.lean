import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand57Checked : Checked StructuralCheckpoints.expand57Action
    StructuralCheckpoints.expand56After StructuralCheckpoints.expand57Output StructuralCheckpoints.expand57After
    ((WitnessCheckpoints.expand57Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand57
    sha256_witness_unfold expand57
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
