import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round49Checked : Checked StructuralCheckpoints.round49Action
    StructuralCheckpoints.round48After StructuralCheckpoints.round49Output StructuralCheckpoints.round49After
    ((WitnessCheckpoints.round49Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round49
    sha256_witness_unfold round49
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
