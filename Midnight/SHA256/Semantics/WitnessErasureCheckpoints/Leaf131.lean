import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round63Checked : Checked StructuralCheckpoints.round63Action
    StructuralCheckpoints.round62After StructuralCheckpoints.round63Output StructuralCheckpoints.round63After
    ((WitnessCheckpoints.round63Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round63
    sha256_witness_unfold round63
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
