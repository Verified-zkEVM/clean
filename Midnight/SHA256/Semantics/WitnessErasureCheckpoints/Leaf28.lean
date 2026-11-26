import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand24Checked : Checked StructuralCheckpoints.expand24Action
    StructuralCheckpoints.expand23After StructuralCheckpoints.expand24Output StructuralCheckpoints.expand24After
    ((WitnessCheckpoints.expand24Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand24
    sha256_witness_unfold expand24
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
