import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand36Checked : Checked StructuralCheckpoints.expand36Action
    StructuralCheckpoints.expand35After StructuralCheckpoints.expand36Output StructuralCheckpoints.expand36After
    ((WitnessCheckpoints.expand36Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand36
    sha256_witness_unfold expand36
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
