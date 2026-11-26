import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand34Checked : Checked StructuralCheckpoints.expand34Action
    StructuralCheckpoints.expand33After StructuralCheckpoints.expand34Output StructuralCheckpoints.expand34After
    ((WitnessCheckpoints.expand34Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand34
    sha256_witness_unfold expand34
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
