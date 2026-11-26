import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand48Checked : Checked StructuralCheckpoints.expand48Action
    StructuralCheckpoints.expand47After StructuralCheckpoints.expand48Output StructuralCheckpoints.expand48After
    ((WitnessCheckpoints.expand48Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand48
    sha256_witness_unfold expand48
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
