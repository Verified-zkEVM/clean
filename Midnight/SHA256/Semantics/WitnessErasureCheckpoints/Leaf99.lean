import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round31Checked : Checked StructuralCheckpoints.round31Action
    StructuralCheckpoints.round30After StructuralCheckpoints.round31Output StructuralCheckpoints.round31After
    ((WitnessCheckpoints.round31Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round31
    sha256_witness_unfold round31
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
