import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round35Checked : Checked StructuralCheckpoints.round35Action
    StructuralCheckpoints.round34After StructuralCheckpoints.round35Output StructuralCheckpoints.round35After
    ((WitnessCheckpoints.round35Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round35
    sha256_witness_unfold round35
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
