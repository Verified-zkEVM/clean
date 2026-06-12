import Clean.Orchard.Ecc.ScalarMul.Mul
import Clean.Orchard.Ecc.ScalarMul.Mul.Incomplete
import Clean.Orchard.Ecc.ScalarMul.Mul.Complete
import Clean.Orchard.Ecc.ScalarMul.Mul.Overflow
import Clean.Orchard.Ecc.Add

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul.rs::Config::assign`
(`CircuitVersion::AnchoredBase`).

Variable-base scalar multiplication: computes `[alpha] base` where `alpha : Fp` is a
Pallas base-field element. The working scalar is `k = alpha.val + t_q`, decomposed
MSB-first into 255 bits and processed as

1. `acc = [2]base` via complete addition,
2. a running sum `z` starting at the constant 0,
3. the `hi` incomplete half — 125 double-and-add steps for bits `k_254..k_130`,
4. the `lo` incomplete half — 126 double-and-add steps for bits `k_129..k_4`,
5. three complete-addition bits `k_3..k_1`,
6. the LSB step `k_0` — a correction point (identity if `k_0 = 1`, else `-base`)
   pinned by `GATE LSB check` and added with complete addition,
7. the overflow check on `z_0`, `z_130`, `k_254`.

Soundness rests on the identity `2^254 + t_q ≡ 0 (mod q)`: the double-and-add
accumulates `[2^254 + k] base = [alpha] base`.
-/

namespace Orchard.Ecc.ScalarMul.Mul.Assign

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open Incomplete.DoubleAndAdd (BitsHint)

/-- `t_q` as a natural number (`q = 2^254 + tQNat` for the Pallas group order). -/
def tQNat : ℕ := 45560315531506369815346746415080538113

/-- The working scalar `k = alpha.val + t_q`. -/
def kNat (alpha : Fp) : ℕ := alpha.val + tQNat

/-- MSB-first bits of the working scalar: `kBits alpha i = k_{254-i}`. -/
def kBits (alpha : Fp) : BitsHint := fun i => (kNat alpha).testBit (254 - i)

/-- Inputs of variable-base scalar mul: the scalar cell and the non-identity base. -/
structure Input (F : Type) where
  alpha : F
  base : Ecc.Point F
deriving ProvableStruct

def main (input : Var Input Fp) : Circuit Fp (Var Ecc.Point Fp) := do
  -- initialize the accumulator `acc = [2]base` using complete addition
  let acc ← Ecc.Add.circuit { p := input.base, q := input.base }
  -- initialize the running sum to zero (`assign_advice_from_constant`)
  let zInit ← witnessField fun _ => 0
  zInit === 0
  -- double-and-add over the `hi` half of the scalar decomposition (125 bits)
  let hi ← Incomplete.DoubleAndAdd.circuit 124 {
    base := input.base, xA := acc.x, yA := acc.y, z := zInit,
    bits := fun env => fun i => kBits (env input.alpha) i }
  -- double-and-add over the `lo` half (126 bits), running sum chained
  let lo ← Incomplete.DoubleAndAdd.circuit 125 {
    base := input.base, xA := hi.xA, yA := hi.yA,
    z := hi.zs[124],
    bits := fun env => fun i => kBits (env input.alpha) (125 + i) }
  -- complete addition for bits `k_3..k_1`
  let comp ← Complete.AssignRegion.circuit {
    base := input.base, xA := lo.xA, yA := lo.yA,
    z := lo.zs[125],
    bits := fun env => fun i => kBits (env input.alpha) (251 + i) }
  -- process the least significant bit: z_0 = 2⋅z_1 + k_0
  let z0 ← witnessField fun env =>
    2 * env (comp.zs[2]) + (if kBits (env input.alpha) 254 then 1 else 0)
  -- copy in base_x, base_y for the LSB gate
  let baseX <== input.base.x
  let baseY <== input.base.y
  -- the correction point: identity if k_0 = 1, else -base
  let corrX ← witnessField fun env =>
    if kBits (env input.alpha) 254 then 0 else env input.base.x
  let corrY ← witnessField fun env =>
    if kBits (env input.alpha) 254 then 0 else -(env input.base.y)
  Mul.circuit { z1 := comp.zs[2], z0, xP := corrX, yP := corrY, baseX, baseY }
  -- the result of the final complete addition is `[alpha] base`
  let result ← Ecc.Add.circuit { p := { x := corrX, y := corrY }, q := comp.acc }
  -- overflow check on z_0 (full sum), z_130 (after the hi half), k_254 (first bit)
  Overflow.OverflowCheck.circuit {
    alpha := input.alpha, z0,
    z130 := hi.zs[124],
    k254 := hi.zs[0] }
  return result

instance elaborated : ElaboratedCircuit Fp Input Ecc.Point main := by
  elaborate_circuit

def Assumptions (input : Input Fp) : Prop :=
  Pallas.OnCurve input.base.coords

/-- The circuit computes the variable-base scalar multiplication `[alpha] base`,
with the identity encoded as `(0, 0)` coordinates. -/
def Spec (input : Input Fp) (output : Ecc.Point Fp) : Prop :=
  ∀ B : SWPoint Pallas.curve, B ≠ 0 → input.base.coords = (B.x, B.y) →
    output.coords = ((input.alpha.val • B).x, (input.alpha.val • B).y)

theorem soundness : Soundness Fp main Assumptions Spec := by
  sorry

theorem completeness : Completeness Fp main Assumptions := by
  sorry

/-- `mul.rs::Config::assign` (`CircuitVersion::AnchoredBase`):
variable-base scalar multiplication by a base-field element. -/
def circuit : FormalCircuit Fp Input Ecc.Point where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end Orchard.Ecc.ScalarMul.Mul.Assign
