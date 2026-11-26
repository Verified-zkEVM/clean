import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand21Checked : Checked StructuralCheckpoints.expand21Action
    StructuralCheckpoints.expand20After StructuralCheckpoints.expand21Output StructuralCheckpoints.expand21After
    ((WitnessCheckpoints.expand21Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand21
    sha256_witness_unfold expand21
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
