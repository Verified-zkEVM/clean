import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

set_option cbv.maxSteps 200000
sha256_relocation_reduction in

theorem serialize3Relocates (offset : Nat) :
    WitnessErasure.operations (serialize3Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (serialize3Operations 0)) := by
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
