import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand63Checked : Checked StructuralCheckpoints.expand63Action
    StructuralCheckpoints.expand62After StructuralCheckpoints.expand63Output StructuralCheckpoints.expand63After
    ((WitnessCheckpoints.expand63Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand63
    sha256_witness_unfold expand63
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
