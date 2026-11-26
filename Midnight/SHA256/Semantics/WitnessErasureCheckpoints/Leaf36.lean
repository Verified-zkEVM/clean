import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand32Checked : Checked StructuralCheckpoints.expand32Action
    StructuralCheckpoints.expand31After StructuralCheckpoints.expand32Output StructuralCheckpoints.expand32After
    ((WitnessCheckpoints.expand32Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand32
    sha256_witness_unfold expand32
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
