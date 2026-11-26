import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round60Checked : Checked StructuralCheckpoints.round60Action
    StructuralCheckpoints.round59After StructuralCheckpoints.round60Output StructuralCheckpoints.round60After
    ((WitnessCheckpoints.round60Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round60
    sha256_witness_unfold round60
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
