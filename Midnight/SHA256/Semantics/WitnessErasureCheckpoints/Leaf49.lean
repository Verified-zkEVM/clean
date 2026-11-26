import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand45Checked : Checked StructuralCheckpoints.expand45Action
    StructuralCheckpoints.expand44After StructuralCheckpoints.expand45Output StructuralCheckpoints.expand45After
    ((WitnessCheckpoints.expand45Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand45
    sha256_witness_unfold expand45
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
