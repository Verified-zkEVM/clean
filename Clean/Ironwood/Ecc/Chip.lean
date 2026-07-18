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

Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip.rs::EccChip::configure`
(lines 246-337): the aggregate ECC configuration, VK-exact in registration order —
witness point, incomplete addition, complete addition, variable-base mul, the shared
`mul_fixed` core, then the full-width / short / base-field-element wrappers.
-/

namespace Halo2.Ironwood.Ecc

open Halo2.Ironwood (Fp)

/-- Rust `EccConfig` (`chip.rs:221-243`): the chip sub-configs (the `advices` bundle and
the shared lookup config are carried by the parent). -/
structure EccConfig where
  witnessPoint : WitnessPoint.Config
  addIncomplete : AddIncomplete.Config
  add : Add.Config
  mul : Mul.Config
  mulFixedFull : MulFixed.FullWidth.Config
  mulFixedShort : MulFixed.Short.Config
  mulFixedBaseField : MulFixed.BaseFieldElem.Config

/-- Rust `EccChip::configure` (`chip.rs:246-337`), VK-exact registration order. -/
def configure (advices : Fin 10 → Column .advice)
    (lagrangeCoeffs : Fin 8 → Column .fixed)
    (rangeCheck : LookupRangeCheck.Config 10) : Configure Fp EccConfig := do
  -- chip.rs:252 — witness point gates
  let witnessPoint ← WitnessPoint.configure (advices 0) (advices 1)
  -- chip.rs:255-256 — incomplete point addition gate
  let addIncomplete ← AddIncomplete.add.configure
    (advices 0, advices 1, advices 2, advices 3)
  -- chip.rs:259-262 — complete point addition gate
  let add ← Add.add.configure
    (advices 0, advices 1, advices 2, advices 3, advices 4, advices 5,
     advices 6, advices 7, advices 8)
  -- chip.rs:265 — variable-base scalar mul gates
  let mul ← Mul.configure add rangeCheck advices
  -- chip.rs:269-276 — the shared fixed-base mul core
  let mulFixed ← MulFixed.configure lagrangeCoeffs (advices 4) (advices 5)
    add addIncomplete
  -- chip.rs:279-280 — full-width fixed-base mul gate
  let mulFixedFull ← MulFixed.FullWidth.configure mulFixed
  -- chip.rs:283-284 — short fixed-base mul gate
  let mulFixedShort ← MulFixed.Short.configure mulFixed
  -- chip.rs:287-293 — base-field-element fixed-base mul gate
  let mulFixedBaseField ← MulFixed.BaseFieldElem.configure
    ![advices 6, advices 7, advices 8] rangeCheck mulFixed
  return { witnessPoint, addIncomplete, add, mul, mulFixedFull, mulFixedShort,
           mulFixedBaseField }

end Halo2.Ironwood.Ecc
