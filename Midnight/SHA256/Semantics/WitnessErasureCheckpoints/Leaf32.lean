import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand28Checked : Checked StructuralCheckpoints.expand28Action
    StructuralCheckpoints.expand27After StructuralCheckpoints.expand28Output StructuralCheckpoints.expand28After
    ((WitnessCheckpoints.expand28Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand28
    sha256_witness_unfold expand28
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
