import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand49Checked : Checked StructuralCheckpoints.expand49Action
    StructuralCheckpoints.expand48After StructuralCheckpoints.expand49Output StructuralCheckpoints.expand49After
    ((WitnessCheckpoints.expand49Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand49
    sha256_witness_unfold expand49
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
