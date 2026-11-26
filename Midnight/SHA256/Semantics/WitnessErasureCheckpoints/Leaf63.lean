import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand59Checked : Checked StructuralCheckpoints.expand59Action
    StructuralCheckpoints.expand58After StructuralCheckpoints.expand59Output StructuralCheckpoints.expand59After
    ((WitnessCheckpoints.expand59Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand59
    sha256_witness_unfold expand59
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
