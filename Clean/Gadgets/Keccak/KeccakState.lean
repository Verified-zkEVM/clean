import Clean.Types.U64
import Clean.Circuit.Provable

namespace Clean.Gadgets.Keccak256

@[reducible] def KeccakState := ProvableVector U64 25
