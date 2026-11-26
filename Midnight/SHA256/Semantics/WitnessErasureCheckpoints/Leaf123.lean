import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round55Checked : Checked StructuralCheckpoints.round55Action
    StructuralCheckpoints.round54After StructuralCheckpoints.round55Output StructuralCheckpoints.round55After
    ((WitnessCheckpoints.round55Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round55
    sha256_witness_unfold round55
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
