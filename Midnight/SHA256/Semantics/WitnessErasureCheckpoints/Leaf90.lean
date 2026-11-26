import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round22Checked : Checked StructuralCheckpoints.round22Action
    StructuralCheckpoints.round21After StructuralCheckpoints.round22Output StructuralCheckpoints.round22After
    ((WitnessCheckpoints.round22Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round22
    sha256_witness_unfold round22
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
