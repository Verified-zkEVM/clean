import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round43Checked : Checked StructuralCheckpoints.round43Action
    StructuralCheckpoints.round42After StructuralCheckpoints.round43Output StructuralCheckpoints.round43After
    ((WitnessCheckpoints.round43Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round43
    sha256_witness_unfold round43
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
