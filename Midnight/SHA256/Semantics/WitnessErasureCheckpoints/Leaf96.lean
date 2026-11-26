import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round28Checked : Checked StructuralCheckpoints.round28Action
    StructuralCheckpoints.round27After StructuralCheckpoints.round28Output StructuralCheckpoints.round28After
    ((WitnessCheckpoints.round28Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round28
    sha256_witness_unfold round28
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
