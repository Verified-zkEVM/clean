import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand60Checked : Checked StructuralCheckpoints.expand60Action
    StructuralCheckpoints.expand59After StructuralCheckpoints.expand60Output StructuralCheckpoints.expand60After
    ((WitnessCheckpoints.expand60Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand60
    sha256_witness_unfold expand60
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
