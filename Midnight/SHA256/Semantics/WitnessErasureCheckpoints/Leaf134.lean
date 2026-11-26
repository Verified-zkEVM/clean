import Midnight.SHA256.Semantics.WitnessErasureCheckpoints.Reduction

namespace Midnight.SHA256.Semantics.WitnessErasureCheckpoints
open Halo2

sha256_erasure_reduction in

theorem serialize1Checked : Checked StructuralCheckpoints.serialize1Action
    StructuralCheckpoints.serialize0After StructuralCheckpoints.serialize1Output StructuralCheckpoints.serialize1After
    ((WitnessCheckpoints.serialize1Operations 0).map WitnessErasure.Code.encode) := by
  conv => arg 5; cbv
  intro priorTrace
  cases priorTrace with
  | mk data =>
    cbv

end Midnight.SHA256.Semantics.WitnessErasureCheckpoints
