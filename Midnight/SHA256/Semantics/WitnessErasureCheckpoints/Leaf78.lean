import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round10Checked : Checked StructuralCheckpoints.round10Action
    StructuralCheckpoints.round9After StructuralCheckpoints.round10Output StructuralCheckpoints.round10After
    ((WitnessCheckpoints.round10Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round10
    sha256_witness_unfold round10
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
