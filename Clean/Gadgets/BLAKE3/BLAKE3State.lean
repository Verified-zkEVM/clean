import Clean.Types.U32
import Clean.Circuit.Provable
import Clean.Specs.BLAKE3

namespace Gadgets.BLAKE3
open Specs.BLAKE3

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

-- definitions

@[reducible] def BLAKE3State := ProvableVector U32 16

def BLAKE3State.is_normalized (state : BLAKE3State (F p)) :=
  ∀ i : Fin 16, state[i.val].is_normalized

def BLAKE3State.value (state : BLAKE3State (F p)) := state.map U32.value

end Gadgets.BLAKE3
