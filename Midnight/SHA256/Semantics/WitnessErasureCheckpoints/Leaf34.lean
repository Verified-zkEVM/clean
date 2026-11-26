import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand30Checked : Checked StructuralCheckpoints.expand30Action
    StructuralCheckpoints.expand29After StructuralCheckpoints.expand30Output StructuralCheckpoints.expand30After
    ((WitnessCheckpoints.expand30Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand30
    sha256_witness_unfold expand30
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
