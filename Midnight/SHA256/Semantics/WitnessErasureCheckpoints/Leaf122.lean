import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round54Checked : Checked StructuralCheckpoints.round54Action
    StructuralCheckpoints.round53After StructuralCheckpoints.round54Output StructuralCheckpoints.round54After
    ((WitnessCheckpoints.round54Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round54
    sha256_witness_unfold round54
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
