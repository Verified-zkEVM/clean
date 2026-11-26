import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round45Checked : Checked StructuralCheckpoints.round45Action
    StructuralCheckpoints.round44After StructuralCheckpoints.round45Output StructuralCheckpoints.round45After
    ((WitnessCheckpoints.round45Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round45
    sha256_witness_unfold round45
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
