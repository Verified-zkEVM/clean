import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round30Checked : Checked StructuralCheckpoints.round30Action
    StructuralCheckpoints.round29After StructuralCheckpoints.round30Output StructuralCheckpoints.round30After
    ((WitnessCheckpoints.round30Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round30
    sha256_witness_unfold round30
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
