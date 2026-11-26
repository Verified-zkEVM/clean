import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem expand22Checked : Checked StructuralCheckpoints.expand22Action
    StructuralCheckpoints.expand21After StructuralCheckpoints.expand22Output StructuralCheckpoints.expand22After
    ((WitnessCheckpoints.expand22Operations 0).map WitnessErasure.Code.encode) := by
  intro priorTrace
  cases priorTrace with
  | mk data =>
    sha256_structural_unfold expand22
    sha256_witness_unfold expand22
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
