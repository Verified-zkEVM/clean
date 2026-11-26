import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand35Checked : Checked StructuralCheckpoints.expand35Action
    StructuralCheckpoints.expand34After StructuralCheckpoints.expand35Output StructuralCheckpoints.expand35After
    ((WitnessCheckpoints.expand35Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand35
    sha256_witness_unfold expand35
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
