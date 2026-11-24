import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem prepare0Relocates (offset : Nat) :
    WitnessErasure.operations (prepare0Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (prepare0Operations 0)) := by
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
