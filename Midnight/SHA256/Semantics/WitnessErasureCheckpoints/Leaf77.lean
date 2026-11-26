import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round9Checked : Checked StructuralCheckpoints.round9Action
    StructuralCheckpoints.round8After StructuralCheckpoints.round9Output StructuralCheckpoints.round9After
    ((WitnessCheckpoints.round9Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round9
    sha256_witness_unfold round9
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
