import Clean.Ironwood.Ecc.WitnessPoint
import Clean.Ironwood.Ecc.AddIncomplete
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.Mul
import Clean.Ironwood.Ecc.MulFixed
import Clean.Ironwood.Ecc.MulFixed.FullWidth
import Clean.Ironwood.Ecc.MulFixed.Short
import Clean.Ironwood.Ecc.MulFixed.BaseFieldElem

/-!
# ECC chip configure (Ironwood)

The aggregate ECC configuration, in VK-exact registration order: witness point, incomplete
addition, complete addition, variable-base mul, the shared `mul_fixed` core, then the
full-width / short / base-field-element wrappers.

Reference: `halo2_gadgets/src/ecc/chip.rs`.
-/

namespace Zcash.Circuits.Ecc

open Halo2

structure EccConfig where
  -- Witness point.
  witnessPoint : WitnessPoint.Config
  -- Incomplete addition.
  addIncomplete : AddIncomplete.Config
  -- Complete addition.
  add : Add.Config
  -- Variable-base scalar multiplication.
  mul : Mul.Config
  -- Fixed-base full-width scalar multiplication.
  mulFixedFull : MulFixed.FullWidth.Config
  -- Fixed-base signed short scalar multiplication.
  mulFixedShort : MulFixed.Short.Config
  -- Fixed-base mul using a base field element as a scalar.
  mulFixedBaseField : MulFixed.BaseFieldElem.Config

/-- The aggregate ECC configuration, in VK-exact registration order. All `advices` columns are
equality-enabled. -/
def configure (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) : Configure Fp EccConfig := do
  -- witness point gate
  let witnessPoint ← WitnessPoint.configure (advices 0) (advices 1)
  -- incomplete point addition gate
  let addIncomplete ← AddIncomplete.add.configure
    (advices 0, advices 1, advices 2, advices 3)
  -- complete point addition gate
  let add ← Add.add.configure
    (advices 0, advices 1, advices 2, advices 3, advices 4, advices 5,
     advices 6, advices 7, advices 8)
  -- variable-base scalar mul gates
  let mul ← Mul.configure add rangeCheck advices
  -- the shared fixed-base mul core (short, base-field, and full-width)
  let mulFixed ← MulFixed.configure lagrangeCoeffs (advices 4) (advices 5)
    add addIncomplete
  -- full-width fixed-base mul gate
  let mulFixedFull ← MulFixed.FullWidth.configure mulFixed
  -- short fixed-base mul gate
  let mulFixedShort ← MulFixed.Short.configure mulFixed
  -- base-field-element fixed-base mul gate
  let mulFixedBaseField ← MulFixed.BaseFieldElem.configure
    ![advices 6, advices 7, advices 8] rangeCheck mulFixed
  return { witnessPoint, addIncomplete, add, mul, mulFixedFull, mulFixedShort,
           mulFixedBaseField }

instance (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) :
    ElaboratedConfigure (configure advices lagrangeCoeffs rangeCheck) := by
  unfold configure
  infer_instance

end Zcash.Circuits.Ecc
