import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand42Checked : Checked StructuralCheckpoints.expand42Action
    StructuralCheckpoints.expand41After StructuralCheckpoints.expand42Output StructuralCheckpoints.expand42After
    ((WitnessCheckpoints.expand42Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand42
    sha256_witness_unfold expand42
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
