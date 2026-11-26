import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand16Checked : Checked StructuralCheckpoints.expand16Action
    StructuralCheckpoints.prepare15After StructuralCheckpoints.expand16Output StructuralCheckpoints.expand16After
    ((WitnessCheckpoints.expand16Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand16
    sha256_witness_unfold expand16
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
