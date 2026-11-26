import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round44Checked : Checked StructuralCheckpoints.round44Action
    StructuralCheckpoints.round43After StructuralCheckpoints.round44Output StructuralCheckpoints.round44After
    ((WitnessCheckpoints.round44Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round44
    sha256_witness_unfold round44
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
