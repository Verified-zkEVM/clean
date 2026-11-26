import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round62Checked : Checked StructuralCheckpoints.round62Action
    StructuralCheckpoints.round61After StructuralCheckpoints.round62Output StructuralCheckpoints.round62After
    ((WitnessCheckpoints.round62Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round62
    sha256_witness_unfold round62
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
