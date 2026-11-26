import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand54Checked : Checked StructuralCheckpoints.expand54Action
    StructuralCheckpoints.expand53After StructuralCheckpoints.expand54Output StructuralCheckpoints.expand54After
    ((WitnessCheckpoints.expand54Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand54
    sha256_witness_unfold expand54
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
