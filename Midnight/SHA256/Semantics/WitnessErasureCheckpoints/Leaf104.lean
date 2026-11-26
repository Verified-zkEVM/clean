import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round36Checked : Checked StructuralCheckpoints.round36Action
    StructuralCheckpoints.round35After StructuralCheckpoints.round36Output StructuralCheckpoints.round36After
    ((WitnessCheckpoints.round36Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round36
    sha256_witness_unfold round36
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
