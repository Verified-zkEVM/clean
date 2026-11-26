import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round52Checked : Checked StructuralCheckpoints.round52Action
    StructuralCheckpoints.round51After StructuralCheckpoints.round52Output StructuralCheckpoints.round52After
    ((WitnessCheckpoints.round52Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round52
    sha256_witness_unfold round52
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
