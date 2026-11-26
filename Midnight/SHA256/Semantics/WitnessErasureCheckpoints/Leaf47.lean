import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand43Checked : Checked StructuralCheckpoints.expand43Action
    StructuralCheckpoints.expand42After StructuralCheckpoints.expand43Output StructuralCheckpoints.expand43After
    ((WitnessCheckpoints.expand43Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand43
    sha256_witness_unfold expand43
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
