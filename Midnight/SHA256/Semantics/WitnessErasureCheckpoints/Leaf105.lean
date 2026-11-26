import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round37Checked : Checked StructuralCheckpoints.round37Action
    StructuralCheckpoints.round36After StructuralCheckpoints.round37Output StructuralCheckpoints.round37After
    ((WitnessCheckpoints.round37Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round37
    sha256_witness_unfold round37
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
