import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem round15Checked : Checked StructuralCheckpoints.round15Action
    StructuralCheckpoints.round14After StructuralCheckpoints.round15Output StructuralCheckpoints.round15After
    ((WitnessCheckpoints.round15Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold round15
    sha256_witness_unfold round15
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
