import Clean.Types.U64
import Clean.Circuit.Provable
import Clean.Utils.Field

namespace Gadgets.Keccak256

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

@[reducible] def KeccakState := ProvableVector U64 25

@[reducible] def KeccakRow := ProvableVector U64 5

end Gadgets.Keccak256
