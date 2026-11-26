import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand51Checked : Checked StructuralCheckpoints.expand51Action
    StructuralCheckpoints.expand50After StructuralCheckpoints.expand51Output StructuralCheckpoints.expand51After
    ((WitnessCheckpoints.expand51Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand51
    sha256_witness_unfold expand51
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
