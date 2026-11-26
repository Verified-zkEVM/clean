import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand61Checked : Checked StructuralCheckpoints.expand61Action
    StructuralCheckpoints.expand60After StructuralCheckpoints.expand61Output StructuralCheckpoints.expand61After
    ((WitnessCheckpoints.expand61Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand61
    sha256_witness_unfold expand61
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
