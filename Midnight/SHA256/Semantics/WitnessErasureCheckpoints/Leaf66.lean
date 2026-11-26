import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand62Checked : Checked StructuralCheckpoints.expand62Action
    StructuralCheckpoints.expand61After StructuralCheckpoints.expand62Output StructuralCheckpoints.expand62After
    ((WitnessCheckpoints.expand62Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand62
    sha256_witness_unfold expand62
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
