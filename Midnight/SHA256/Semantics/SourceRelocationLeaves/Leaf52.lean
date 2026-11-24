import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem expand48Relocates (offset : Nat) :
    WitnessErasure.operations (expand48Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (expand48Operations 0)) := by
  sha256_witness_unfold expand48
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
