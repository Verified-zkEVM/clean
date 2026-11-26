import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round42Checked : Checked StructuralCheckpoints.round42Action
    StructuralCheckpoints.round41After StructuralCheckpoints.round42Output StructuralCheckpoints.round42After
    ((WitnessCheckpoints.round42Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round42
    sha256_witness_unfold round42
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
