import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem round17Relocates (offset : Nat) :
    WitnessErasure.operations (round17Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (round17Operations 0)) := by
  sha256_witness_unfold round17
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
