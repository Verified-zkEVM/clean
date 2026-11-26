import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand19Checked : Checked StructuralCheckpoints.expand19Action
    StructuralCheckpoints.expand18After StructuralCheckpoints.expand19Output StructuralCheckpoints.expand19After
    ((WitnessCheckpoints.expand19Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand19
    sha256_witness_unfold expand19
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
