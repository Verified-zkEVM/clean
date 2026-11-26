import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand23Checked : Checked StructuralCheckpoints.expand23Action
    StructuralCheckpoints.expand22After StructuralCheckpoints.expand23Output StructuralCheckpoints.expand23After
    ((WitnessCheckpoints.expand23Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand23
    sha256_witness_unfold expand23
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
