import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand17Checked : Checked StructuralCheckpoints.expand17Action
    StructuralCheckpoints.expand16After StructuralCheckpoints.expand17Output StructuralCheckpoints.expand17After
    ((WitnessCheckpoints.expand17Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand17
    sha256_witness_unfold expand17
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
