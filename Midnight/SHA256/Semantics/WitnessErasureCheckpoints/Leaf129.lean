import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round61Checked : Checked StructuralCheckpoints.round61Action
    StructuralCheckpoints.round60After StructuralCheckpoints.round61Output StructuralCheckpoints.round61After
    ((WitnessCheckpoints.round61Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round61
    sha256_witness_unfold round61
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
