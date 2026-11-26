import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand25Checked : Checked StructuralCheckpoints.expand25Action
    StructuralCheckpoints.expand24After StructuralCheckpoints.expand25Output StructuralCheckpoints.expand25After
    ((WitnessCheckpoints.expand25Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand25
    sha256_witness_unfold expand25
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
