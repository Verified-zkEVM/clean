import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round14Checked : Checked StructuralCheckpoints.round14Action
    StructuralCheckpoints.round13After StructuralCheckpoints.round14Output StructuralCheckpoints.round14After
    ((WitnessCheckpoints.round14Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round14
    sha256_witness_unfold round14
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
