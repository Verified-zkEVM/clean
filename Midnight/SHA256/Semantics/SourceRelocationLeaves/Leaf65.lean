import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem expand61Relocates (offset : Nat) :
    WitnessErasure.operations (expand61Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (expand61Operations 0)) := by
  sha256_witness_unfold expand61
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
