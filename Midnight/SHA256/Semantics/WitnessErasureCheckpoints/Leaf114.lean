import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round46Checked : Checked StructuralCheckpoints.round46Action
    StructuralCheckpoints.round45After StructuralCheckpoints.round46Output StructuralCheckpoints.round46After
    ((WitnessCheckpoints.round46Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round46
    sha256_witness_unfold round46
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
