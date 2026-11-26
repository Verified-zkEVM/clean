import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round32Checked : Checked StructuralCheckpoints.round32Action
    StructuralCheckpoints.round31After StructuralCheckpoints.round32Output StructuralCheckpoints.round32After
    ((WitnessCheckpoints.round32Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round32
    sha256_witness_unfold round32
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
