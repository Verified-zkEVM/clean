import Clean.Ironwood.Ecc.Defs
import Clean.Ironwood.Ecc.MulIncompleteTheorems
import Clean.Ironwood.Ecc.AddTheorems
import CompElliptic.CurveForms.ShortWeierstrass

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul/complete.rs`.
-/

namespace Halo2.Ironwood.Ecc.Mul.Complete

structure Input (F : Type) where
  zPrev : F
  zNext : F
  baseY : F
  yP : F
deriving ProvableStruct

def bit {K : Type} [Sub K] [Mul K] [OfNat K 2] (row : Input K) : K :=
  row.zNext - 2 * row.zPrev

def ySwitch {K : Type} [Zero K] [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (row : Input K) : K :=
  ternary (bit row) (row.baseY - row.yP) (row.baseY + row.yP)

def SelectedCompleteBitPointNegation (row : Input Fp) : Prop :=
  ∀ baseX : Fp,
    (bit row = 0 →
      (baseX, row.yP) =
        CompElliptic.CurveForms.ShortWeierstrass.neg (baseX, row.baseY)) ∧
      (bit row = 1 →
        (baseX, row.yP) = (baseX, row.baseY))

def Spec (row : Input Fp) : Prop :=
  IsBool (bit row) ∧ SelectedCompleteBitPointNegation row

/-!
### `complete.rs::Config::assign_region`

The three complete-addition bits `k_3, k_2, k_1` of variable-base scalar mul. Each bit
extends the running sum, conditionally negates the base y-coordinate (checked by the
decomposition gate above), and performs two complete additions:
`acc ← acc + (acc + U)` with `U = (base.x, ±base.y)`.
-/

namespace AssignRegion

open CompElliptic.Curves.Pasta
open Incomplete.DoubleAndAdd (BitsHint zRunValue)

/-- Inputs: the base point, the accumulator cells from incomplete addition, the
running-sum cell, and the prover-side complete-range bits (indexed `0..2`). -/
structure Input (F : Type) where
  base : Point F
  xA : F
  yA : F
  z : F
  bits : UnconstrainedNative BitsHint F
deriving CircuitType

structure Output (F : Type) where
  acc : Point F
  zs : Vector F 3
deriving ProvableStruct

/-- One complete-addition step on coordinate pairs:
`acc + (U + acc)` with `U = (base.x, ±base.y)`. -/
def stepValue (baseX baseY : Fp) (acc : Fp × Fp) (bit : Bool) : Fp × Fp :=
  CompElliptic.CurveForms.ShortWeierstrass.add pallasA acc
    (CompElliptic.CurveForms.ShortWeierstrass.add pallasA
      (baseX, if bit then baseY else -baseY) acc)

/-- The accumulator after the first `b` complete-addition steps. -/
def accValue (baseX baseY : Fp) (acc : Fp × Fp) (bits : ℕ → Bool) : ℕ → Fp × Fp
  | 0 => acc
  | b + 1 => stepValue baseX baseY (accValue baseX baseY acc bits b) (bits b)

private def accValuePoint (baseX baseY xA yA : Fp) (bits : ℕ → Bool) :
    ℕ → Point Fp
  | 0 => { x := xA, y := yA }
  | b + 1 =>
      let acc := accValuePoint baseX baseY xA yA bits b
      acc + ({ x := baseX, y := if bits b then baseY else -baseY } + acc)

private theorem accValuePoint_coords
    (baseX baseY xA yA : Fp) (bits : ℕ → Bool) :
    (accValuePoint baseX baseY xA yA bits 3).coords
      = accValue baseX baseY (xA, yA) bits 3 := by
  simp only [accValuePoint, accValue, stepValue, Point.coords_add]
  simp [Point.coords]

def Spec (input : Value Input Fp) (output : Output Fp) (_ : ProverData Fp) : Prop :=
  ∃ bits : ℕ → Bool,
    (output.zs[0] = 2 * input.z + (if bits 0 then 1 else 0) ∧
      ∀ b : Fin 2, output.zs[b.val + 1] =
        2 * output.zs[b.val]'(by have := b.isLt; omega) +
          (if bits (b.val + 1) then 1 else 0)) ∧
    (({ x := input.xA, y := input.yA } : Point Fp).Valid → input.base.Valid →
      output.acc.Valid ∧
        output.acc.coords = accValue input.base.x input.base.y (input.xA, input.yA) bits 3)

def ProverAssumptions (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  ({ x := input.xA, y := input.yA } : Point Fp).Valid ∧ input.base.Valid

def ProverSpec (input : ProverValue Input Fp) (output : Output Fp)
    (_ : ProverHint Fp) : Prop :=
  (∀ b : Fin 3, output.zs[b.val] = zRunValue input.z input.bits b.val) ∧
  output.acc.coords = accValue input.base.x input.base.y (input.xA, input.yA) input.bits 3

/-- The evaluations of the prepended running-sum cells, by computation. Stating this
over an abstract `v` (pinned by `hv`) lets the `getElem`s elaborate; the concrete
append term would not. -/
private theorem eval_z (env : Environment Fp) (i₀ : ℕ) (v : Vector (Expression Fp) 4)
    (hv : v = (#v[var { index := i₀ }] : Vector (Expression Fp) 1) ++
      (Vector.mapRange 3 fun i => var { index := i₀ + 1 + i } :
        Vector (Expression Fp) 3)) :
    Expression.eval env v[0] = env.get i₀ ∧
    Expression.eval env v[1] = env.get (i₀ + 1) ∧
    Expression.eval env v[2] = env.get (i₀ + 1 + 1) ∧
    Expression.eval env v[3] = env.get (i₀ + 1 + 2) := by
  subst hv
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- One complete bit: the decomposition gate facts pin the running-sum step and the
conditionally-negated `y_p` in terms of the decidable bit `z' = 2z + 1`. -/
private theorem bit_facts {zP zN bY yP : Fp}
    (hbool : IsBool (Complete.bit { zPrev := zP, zNext := zN, baseY := bY, yP := yP }))
    (hsel : SelectedCompleteBitPointNegation
      { zPrev := zP, zNext := zN, baseY := bY, yP := yP }) :
    (zN = 2 * zP + if zN = 2 * zP + 1 then 1 else 0) ∧
      yP = if zN = 2 * zP + 1 then bY else -bY := by
  rcases hbool with h | h
  · have hz : zN = 2 * zP := by
      simp only [Complete.bit] at h
      linear_combination h
    have hcond : ¬(zN = 2 * zP + 1) := by
      rw [hz]
      intro hc
      exact one_ne_zero (by linear_combination -hc)
    have hy := (hsel 0).1 h
    simp only [CompElliptic.CurveForms.ShortWeierstrass.neg, Prod.mk.injEq] at hy
    rw [if_neg hcond, if_neg hcond]
    exact ⟨by rw [hz]; ring, hy.2⟩
  · have hz : zN = 2 * zP + 1 := by
      simp only [Complete.bit] at h
      linear_combination h
    have hy := (hsel 0).2 h
    simp only [Prod.mk.injEq] at hy
    rw [if_pos hz, if_pos hz]
    exact ⟨hz, hy.2⟩

/-- The honest assignment of one complete bit satisfies the decomposition gate. -/
private theorem bit_facts_complete (zP bY : Fp) (b : Bool) :
    IsBool (Complete.bit
      { zPrev := zP, zNext := 2 * zP + (if b = true then 1 else 0), baseY := bY,
        yP := if b = true then bY else -bY }) ∧
    SelectedCompleteBitPointNegation
      { zPrev := zP, zNext := 2 * zP + (if b = true then 1 else 0), baseY := bY,
        yP := if b = true then bY else -bY } := by
  constructor
  · cases b <;> simp [Complete.bit, IsBool]
  · intro baseX
    cases b
    · refine ⟨fun _ => ?_, fun h => ?_⟩
      · simp [CompElliptic.CurveForms.ShortWeierstrass.neg]
      · simp [Complete.bit] at h
    · refine ⟨fun h => ?_, fun _ => by simp⟩
      simp [Complete.bit] at h

end AssignRegion

end Halo2.Ironwood.Ecc.Mul.Complete
