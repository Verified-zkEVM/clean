import Midnight.SHA256.Semantics.SourceRelocationLeaves.Reduction

namespace Midnight.SHA256.Semantics.WitnessCheckpoints
open Halo2 WitnessCircuit WitnessCheckpoint WitnessCheckpointModel

sha256_relocation_reduction in

theorem expand37Relocates (offset : Nat) :
    WitnessErasure.operations (expand37Operations offset) =
      Chips.Relocation.operations offset (WitnessErasure.operations (expand37Operations 0)) := by
  sha256_witness_unfold expand37
  cbv

end Midnight.SHA256.Semantics.WitnessCheckpoints
