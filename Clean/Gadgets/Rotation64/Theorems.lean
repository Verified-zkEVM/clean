import Clean.Types.U64
import Clean.Utils.Field

variable {p : ℕ} [Fact p.Prime]
variable [p_large_enough: Fact (p > 512)]

namespace Gadgets.Rotation64.Theorems

def rot64 (x : ℕ) (offset : ℕ) : ℕ :=
  let offset := offset % 64
  let low := x % (2^offset)
  let high := x / (2^offset)
  low * (2^(64 - offset)) + high


end Gadgets.Rotation64.Theorems
