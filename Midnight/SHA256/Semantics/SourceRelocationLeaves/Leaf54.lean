import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem expand50Relocates (offset : Nat) :
    WitnessErasure.operations (expand50Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (expand50Operations 0)) := by
  sha256_witness_unfold expand50
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
