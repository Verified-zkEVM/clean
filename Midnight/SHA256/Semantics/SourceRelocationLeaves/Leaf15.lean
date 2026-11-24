import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem prepare11Relocates (offset : Nat) :
    WitnessErasure.operations (prepare11Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (prepare11Operations 0)) := by
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
