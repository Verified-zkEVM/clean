import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round23Checked : Checked StructuralCheckpoints.round23Action
    StructuralCheckpoints.round22After StructuralCheckpoints.round23Output StructuralCheckpoints.round23After
    ((WitnessCheckpoints.round23Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round23
    sha256_witness_unfold round23
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
