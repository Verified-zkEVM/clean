import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round48Checked : Checked StructuralCheckpoints.round48Action
    StructuralCheckpoints.round47After StructuralCheckpoints.round48Output StructuralCheckpoints.round48After
    ((WitnessCheckpoints.round48Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round48
    sha256_witness_unfold round48
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
