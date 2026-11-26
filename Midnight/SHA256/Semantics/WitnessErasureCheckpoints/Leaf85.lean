import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round17Checked : Checked StructuralCheckpoints.round17Action
    StructuralCheckpoints.round16After StructuralCheckpoints.round17Output StructuralCheckpoints.round17After
    ((WitnessCheckpoints.round17Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round17
    sha256_witness_unfold round17
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
