import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem round4Relocates (offset : Nat) :
    WitnessErasure.operations (round4Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (round4Operations 0)) := by
  sha256_witness_unfold round4
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
