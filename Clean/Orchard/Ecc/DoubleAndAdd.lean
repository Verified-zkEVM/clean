import Clean.Circuit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-!
# Double-and-add row (incomplete addition)

The `(x_A, x_P, λ₁, λ₂)` cells of one incomplete-addition double-and-add step and the
derived `x_R`/`Y_A` formulas. This is shared ECC machinery used by both scalar
multiplication and the Sinsemilla hash, so it lives under `Orchard.Ecc` rather than
inside Sinsemilla.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul/incomplete.rs`
- `DoubleAndAdd::x_r`
- `DoubleAndAdd::Y_A`
-/

namespace Orchard.Ecc

structure DoubleAndAddRow (F : Type) where
  xA : F
  xP : F
  lambda1 : F
  lambda2 : F
deriving ProvableStruct

namespace DoubleAndAdd

def xR {K : Type} [Sub K] [Mul K] (row : DoubleAndAddRow K) : K :=
  row.lambda1 * row.lambda1 - row.xA - row.xP

def yA {K : Type} [Add K] [Sub K] [Mul K] (row : DoubleAndAddRow K) : K :=
  (row.lambda1 + row.lambda2) * (row.xA - xR row)

end DoubleAndAdd

end Orchard.Ecc
