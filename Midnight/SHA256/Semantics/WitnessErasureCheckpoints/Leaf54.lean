import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand50Checked : Checked StructuralCheckpoints.expand50Action
    StructuralCheckpoints.expand49After StructuralCheckpoints.expand50Output StructuralCheckpoints.expand50After
    ((WitnessCheckpoints.expand50Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand50
    sha256_witness_unfold expand50
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
