import Midnight.Frontend.Poseidon
import Midnight.Keygen.Encoding

/-! The Poseidon-only architecture's configuration: `Frontend.Poseidon.configure` compiled by the
Midnight backend. `Backend.Checks.poseidon_cs` compares it with a frozen fixture. -/
namespace Midnight.Poseidon
open Midnight.Keygen

def configured : CS := Backend.compile Frontend.Poseidon.configure

/-- `PoseidonExample::used_chips`: Poseidon only. -/
def architecture : Architecture := { poseidon := true }

end Midnight.Poseidon
