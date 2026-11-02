module

public import CleanCompStark.KeccakShowcase
public import CompStark.KoalaBear.Fast

/-! # The keccak-air showcase's AIR

The CompStark AIR of Clean's keccak-air component, over KoalaBear's fast field: the AIR the
showcase proves, and whose quotient kernel `KeccakShowcase.Kernel` generates.
-/

@[expose] public section

namespace KeccakShowcase
open CompStark CompStark.Stark CleanCompStark

abbrev F := KoalaBear.Fast.Field
abbrev EF := KoalaBear.Fast.Ext4

/-- The CompStark AIR of Clean's keccak-air component on `2 ^ logN` rows. -/
def air (logN : ℕ) : Air F := toAir koalaBear (CleanCompStark.KeccakAir.component logN) logN

end KeccakShowcase
