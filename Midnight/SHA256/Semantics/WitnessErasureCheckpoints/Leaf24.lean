import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand20Checked : Checked StructuralCheckpoints.expand20Action
    StructuralCheckpoints.expand19After StructuralCheckpoints.expand20Output StructuralCheckpoints.expand20After
    ((WitnessCheckpoints.expand20Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand20
    sha256_witness_unfold expand20
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
