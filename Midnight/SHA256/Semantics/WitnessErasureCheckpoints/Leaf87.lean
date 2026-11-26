import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round19Checked : Checked StructuralCheckpoints.round19Action
    StructuralCheckpoints.round18After StructuralCheckpoints.round19Output StructuralCheckpoints.round19After
    ((WitnessCheckpoints.round19Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round19
    sha256_witness_unfold round19
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
