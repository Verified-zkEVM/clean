import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem paddingRelocates (offset : Nat) :
    WitnessErasure.operations (paddingOperations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (paddingOperations 0)) := by
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
