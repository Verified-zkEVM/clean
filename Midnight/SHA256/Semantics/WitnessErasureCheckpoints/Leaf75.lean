import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round7Checked : Checked StructuralCheckpoints.round7Action
    StructuralCheckpoints.round6After StructuralCheckpoints.round7Output StructuralCheckpoints.round7After
    ((WitnessCheckpoints.round7Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round7
    sha256_witness_unfold round7
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
