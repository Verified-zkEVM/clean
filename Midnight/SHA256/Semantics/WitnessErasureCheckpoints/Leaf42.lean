import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand38Checked : Checked StructuralCheckpoints.expand38Action
    StructuralCheckpoints.expand37After StructuralCheckpoints.expand38Output StructuralCheckpoints.expand38After
    ((WitnessCheckpoints.expand38Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand38
    sha256_witness_unfold expand38
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
