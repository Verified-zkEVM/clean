import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem expand36Relocates (offset : Nat) :
    WitnessErasure.operations (expand36Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (expand36Operations 0)) := by
  sha256_witness_unfold expand36
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
