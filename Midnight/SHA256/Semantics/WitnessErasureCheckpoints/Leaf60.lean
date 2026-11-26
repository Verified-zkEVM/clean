import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand56Checked : Checked StructuralCheckpoints.expand56Action
    StructuralCheckpoints.expand55After StructuralCheckpoints.expand56Output StructuralCheckpoints.expand56After
    ((WitnessCheckpoints.expand56Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand56
    sha256_witness_unfold expand56
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
