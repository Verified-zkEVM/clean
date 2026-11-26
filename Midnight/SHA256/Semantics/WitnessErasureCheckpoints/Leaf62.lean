import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand58Checked : Checked StructuralCheckpoints.expand58Action
    StructuralCheckpoints.expand57After StructuralCheckpoints.expand58Output StructuralCheckpoints.expand58After
    ((WitnessCheckpoints.expand58Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand58
    sha256_witness_unfold expand58
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
