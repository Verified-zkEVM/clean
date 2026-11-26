import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand31Checked : Checked StructuralCheckpoints.expand31Action
    StructuralCheckpoints.expand30After StructuralCheckpoints.expand31Output StructuralCheckpoints.expand31After
    ((WitnessCheckpoints.expand31Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand31
    sha256_witness_unfold expand31
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
