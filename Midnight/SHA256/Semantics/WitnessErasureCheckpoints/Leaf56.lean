import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand52Checked : Checked StructuralCheckpoints.expand52Action
    StructuralCheckpoints.expand51After StructuralCheckpoints.expand52Output StructuralCheckpoints.expand52After
    ((WitnessCheckpoints.expand52Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand52
    sha256_witness_unfold expand52
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
