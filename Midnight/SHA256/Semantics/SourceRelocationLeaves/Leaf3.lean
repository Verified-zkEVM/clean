import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem packingRelocates (offset : Nat) :
    WitnessErasure.operations (packingOperations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (packingOperations 0)) := by
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
