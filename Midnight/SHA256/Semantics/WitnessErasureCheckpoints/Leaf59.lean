import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand55Checked : Checked StructuralCheckpoints.expand55Action
    StructuralCheckpoints.expand54After StructuralCheckpoints.expand55Output StructuralCheckpoints.expand55After
    ((WitnessCheckpoints.expand55Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand55
    sha256_witness_unfold expand55
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
