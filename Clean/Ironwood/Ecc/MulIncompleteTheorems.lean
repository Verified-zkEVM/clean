import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.Defs
import Clean.Ironwood.Ecc.DoubleAndAdd

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul/incomplete.rs`.
-/

namespace Zcash.Circuits.Ecc.Mul.Incomplete

open Clean

namespace Init

structure Input (F : Type) where
  yAWitnessed : F
  next : DoubleAndAddRow F
deriving ProvableStruct

def Spec (input : Input Fp) : Prop :=
  2 * input.yAWitnessed = DoubleAndAdd.yA input.next

end Init

namespace Loop

structure Input (F : Type) where
  zCur : F
  zPrev : F
  cur : DoubleAndAddRow F
  xANext : F
  yPCur : F
  yANextDouble : F
deriving ProvableStruct

def bit {K : Type} [Sub K] [Mul K] [OfNat K 2] (row : Input K) : K :=
  row.zCur - row.zPrev * 2

def gradient1 {K : Type} [One K] [Add K] [Sub K] [Mul K] [OfNat K 2]
    (row : Input K) : K :=
  2 * row.cur.lambda1 * (row.cur.xA - row.cur.xP) - DoubleAndAdd.yA row.cur +
    2 * ((bit row * 2 - 1) * row.yPCur)

def secantLine {K : Type} [Sub K] [Mul K] (row : Input K) : K :=
  row.cur.lambda2 * row.cur.lambda2 - row.xANext -
    DoubleAndAdd.xR row.cur - row.cur.xA

def gradient2 {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 2] (row : Input K) : K :=
  2 * row.cur.lambda2 * (row.cur.xA - row.xANext) - DoubleAndAdd.yA row.cur - row.yANextDouble

def Spec (row : Input Fp) : Prop :=
  IsBool (bit row) ∧
    2 * row.cur.lambda1 * (row.cur.xA - row.cur.xP) +
        2 * ((bit row * 2 - 1) * row.yPCur) = DoubleAndAdd.yA row.cur ∧
    row.cur.lambda2 * row.cur.lambda2 =
        row.xANext + DoubleAndAdd.xR row.cur + row.cur.xA ∧
    2 * row.cur.lambda2 * (row.cur.xA - row.xANext) =
        DoubleAndAdd.yA row.cur + row.yANextDouble

end Loop

namespace MainLoop

structure Input (F : Type) extends Loop.Input F where
  xPNext : F
  yPNext : F
deriving ProvableStruct

def xPCheck {K : Type} [Sub K] (row : Input K) : K :=
  row.cur.xP - row.xPNext

def yPCheck {K : Type} [Sub K] (row : Input K) : K :=
  row.yPCur - row.yPNext

def Spec (row : Input Fp) : Prop :=
  row.cur.xP = row.xPNext ∧ row.yPCur = row.yPNext ∧ Loop.Spec row.toInput

end MainLoop

/-!
### `incomplete.rs::Config::double_and_add`

The synthesis-level double-and-add over `numBits = n + 1` incomplete-addition rows,
shared by the `hi` (125 bits) and `lo` (126 bits) halves of variable-base scalar
multiplication. This ports the `CircuitVersion::AnchoredBase` variant: the first row's
`x_p, y_p` cells are copies of `base`, and the `q_mul_2` constancy checks propagate the
base to every row.

The scalar bits are prover-side `Value<bool>`s, modeled as an `UnconstrainedNative` hint
(MSB-first, indexed from the first processed bit).

The running accumulator's y-coordinate is not a per-row cell in the source; it exists
only as the derived expression `y_{A,i} = Y_{A,i}/2`. Only the initial y (copied into
the `lambda_1` column) and the final y (witnessed after the last row) are cells.

Cell order matches the source's assignment order: the three starting copies
(`z`, `x_a`, `y_a`), then per loop row the cells `z, x_p, y_p, λ1, λ2, x_a(next)`
in the order `assign_advice` is called, then the final `y_a`. Gates are asserted
after witnessing; in the source they are global polynomial identities whose
selectors are enabled before any assignment, so assertion order carries no content.
-/

namespace DoubleAndAdd

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

/-- Prover-side scalar bits, MSB-first, indexed from the first processed bit. -/
def BitsHint : Type := ℕ → Bool

instance : Inhabited BitsHint := ⟨fun _ => false⟩

/-- The inputs of `double_and_add`: the non-identity base point, the accumulator cells
`(x_a, y_a)`, the starting running-sum cell `z`, and the prover-side scalar bits. -/
structure Input (F : Type) where
  base : Point F
  xA : F
  yA : F
  z : F
  bits : UnconstrainedNative BitsHint F
deriving CircuitType

/-- The cells freshly witnessed for the first row (its `x_p, y_p` are copies of
`base` in the anchored circuit version). -/
structure LambdaCells (F : Type) where
  lambda1 : F
  lambda2 : F
  xANext : F
deriving ProvableStruct

/-- The outputs of `double_and_add`: the final accumulator cells and all interstitial
running-sum cells (excluding the copied starting `z`). -/
structure Output (numBits : ℕ) (F : Type) where
  xA : F
  yA : F
  zs : Vector F numBits
deriving ProvableStruct

/-! ### Honest-prover witness values -/

/-- The running sum after bit `b` (MSB-first): `z_b = 2 z_{b-1} + k_b`. -/
def zRunValue (zIn : Fp) (bits : ℕ → Bool) : ℕ → Fp
  | 0 => 2 * zIn + (if bits 0 then 1 else 0)
  | b + 1 => 2 * zRunValue zIn bits b + (if bits (b + 1) then 1 else 0)

/-- Honest lambda cells of one double-and-add row, from the accumulator `(x_a, y_a)`
entering the row and the row's bit. The assigned `x_p, y_p` cells always hold the base
coordinates; the conditional negation `(2k-1) y_p` only enters `λ1`. -/
def lambdaCellsValue (baseX baseY xA yA : Fp) (bit : Bool) : LambdaCells Fp :=
  let yP := if bit then baseY else -baseY
  let lambda1 := (yA - yP) / (xA - baseX)
  let xR := lambda1 * lambda1 - xA - baseX
  let lambda2 := 2 * yA / (xA - xR) - lambda1
  { lambda1, lambda2, xANext := lambda2 * lambda2 - xA - xR }

/-- The honest accumulator `(x_a, y_a)` entering row `r`
(`incomplete.rs::double_and_add` assignment formulas, total via `0⁻¹ = 0`). -/
def accVal (baseX baseY xA yA : Fp) (bits : ℕ → Bool) : ℕ → Fp × Fp
  | 0 => (xA, yA)
  | r + 1 =>
    let p := accVal baseX baseY xA yA bits r
    let l := lambdaCellsValue baseX baseY p.1 p.2 (bits r)
    (l.xANext, l.lambda2 * (p.1 - l.xANext) - p.2)

/-- The honest lambda cells of row `r`. -/
def rowLambdaValue (baseX baseY xA yA : Fp) (bits : ℕ → Bool) (r : ℕ) : LambdaCells Fp :=
  lambdaCellsValue baseX baseY
    (accVal baseX baseY xA yA bits r).1 (accVal baseX baseY xA yA bits r).2 (bits r)

/-- The accumulated multiplier after `b` double-and-add steps starting from `[m]P`:
each step computes `(acc + (2k-1) P) + acc`, so `m_b = 2 m_{b-1} + 2 k_{b-1} - 1`. -/
def accScalar (m : ℕ) (bits : ℕ → Bool) : ℕ → ℕ
  | 0 => m
  | b + 1 => 2 * accScalar m bits b + (if bits b then 1 else 0) * 2 - 1

/-- The conditionally-negated per-bit point `(2k-1) P` added by each step. -/
def stepPoint (P : Point Fp) (bit : Bool) : Point Fp :=
  if bit then P else -P

/-- A non-degenerate double-and-add step on a small positive multiple of the base:
`([m]P ⸭ (2k-1)P) ⸭ [m]P = [2m + 2k - 1]P`. -/
theorem step_nsmul {P : Point Fp} (hP : P.OnCurve) (bits : ℕ → Bool)
    {m : ℕ} (h2 : 2 ≤ m) (hBound : 2 * m + 1 < PALLAS_SCALAR_CARD) (b : ℕ) :
    Point.doubleAndAdd (m • P) (if bits b then P else -P)
      = some ((2 * m + (if bits b then 1 else 0) * 2 - 1) • P) := by
  have hA0 : m • P ≠ 0 := Point.nsmul_ne_zero hP (n := m) (by omega) (by omega)
  have hxm1 : (m • P).x ≠ P.x := by
    have h := Point.nsmul_x_ne hP (s := 1) (t := m) (by omega) (by omega) (by omega)
    exact h
  rw [Point.doubleAndAdd]
  by_cases hb : bits b
  · rw [if_pos hb,
      Point.incompleteAdd_some (p := m • P) (q := P)
        hA0 (Point.ne_zero_of_onCurve hP) hxm1,
      Point.nsmul_add_one hP m]
    change ((m + 1) • P ⸭ m • P) =
      some ((2 * m + (if bits b then 1 else 0) * 2 - 1) • P)
    rw [
      Point.incompleteAdd_some (p := (m + 1) • P) (q := m • P)
        (Point.nsmul_ne_zero hP (by omega) (by omega)) hA0
        (Point.nsmul_x_ne hP (s := m) (t := m + 1) (by omega) (by omega) (by omega)),
      Point.nsmul_add_nsmul hP (m + 1) m]
    rw [if_pos hb]
    norm_num
    congr 1
    omega
  · rw [if_neg hb,
      Point.incompleteAdd_some (p := m • P) (q := -P)
        hA0 (Point.neg_ne_zero_of_ne_zero (Point.ne_zero_of_onCurve hP))
        hxm1,
      Point.nsmul_add_neg_one hP h2]
    change ((m - 1) • P ⸭ m • P) =
      some ((2 * m + (if bits b then 1 else 0) * 2 - 1) • P)
    rw [
      Point.incompleteAdd_some (p := (m - 1) • P) (q := m • P)
        (Point.nsmul_ne_zero hP (by omega) (by omega)) hA0
        (Ne.symm (Point.nsmul_x_ne hP (s := m - 1) (t := m) (by omega) (by omega)
          (by omega))),
      Point.nsmul_add_nsmul hP (m - 1) m]
    rw [if_neg hb]
    norm_num
    congr 1
    omega

/-! ### Circuit -/

/-- The six cells assigned by one loop iteration of `double_and_add`, in source
assignment order. A plain expression-level bag; never evaluated as a unit. -/
structure RowCells (F : Type) where
  z : F
  xP : F
  yP : F
  lambda1 : F
  lambda2 : F
  xANext : F

/-- Soundness contract. The constraints pin a bit sequence through the running-sum
chain, and — for any base/accumulator interpretation satisfying the incomplete-addition
preconditions — force the output accumulator to be the double-and-add result. -/
def Spec (n : ℕ) (input : Value Input Fp)
    (output : Output (n + 1) Fp) (_ : ProverData Fp) : Prop :=
  let base : Point Fp := input.base
  ∃ bits : ℕ → Bool,
    (output.zs[0] = 2 * input.z + (if bits 0 then 1 else 0) ∧
      ∀ b : Fin n, output.zs[b.val + 1] =
        2 * output.zs[b.val] + (if bits (b.val + 1) then 1 else 0)) ∧
    ∀ (m : ℕ),
      Point.ofCoords (input.xA, input.yA) = m • base →
      2 ≤ m → 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254 →
      Point.ofCoords (output.xA, output.yA) = (accScalar m bits (n + 1)) • base

def Assumptions (_n : ℕ) (input : Value Input Fp) (_ : ProverData Fp) : Prop :=
  let base : Point Fp := input.base
  base.OnCurve

def ProverAssumptions (n : ℕ) (input : ProverValue Input Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  let base : Point Fp := input.base
  base.OnCurve ∧ ∃ m : ℕ,
    Point.ofCoords (input.xA, input.yA) = m • base ∧
    2 ≤ m ∧ 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254

def ProverSpec (n : ℕ) (input : ProverValue Input Fp) (output : Output (n + 1) Fp)
    (_ : ProverHint Fp) : Prop :=
  let base : Point Fp := input.base
  (∀ b : Fin (n + 1), output.zs[b.val] = zRunValue input.z input.bits b.val) ∧
  ∀ (m : ℕ),
    Point.ofCoords (input.xA, input.yA) = m • base →
    2 ≤ m → 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254 →
    Point.ofCoords (output.xA, output.yA) = (accScalar m input.bits (n + 1)) • base

theorem accScalar_two_le {m : ℕ} (h2 : 2 ≤ m) (bits : ℕ → Bool) :
    ∀ b, 2 ≤ accScalar m bits b
  | 0 => h2
  | b + 1 => by
    have ih := accScalar_two_le h2 bits b
    simp only [accScalar]
    rcases Bool.dichotomy (bits b) with hb | hb <;> rw [hb] <;> norm_num <;> omega

theorem accScalar_le {m : ℕ} (bits : ℕ → Bool) :
    ∀ b, accScalar m bits b ≤ 2 ^ b * (m + 1) - 1
  | 0 => by simp [accScalar]
  | b + 1 => by
    have ih := accScalar_le (m := m) bits b
    have hpos : 0 < 2 ^ b * (m + 1) := by positivity
    have hsplit : 2 ^ (b + 1) * (m + 1) = 2 * (2 ^ b * (m + 1)) := by ring
    simp only [accScalar]
    rcases Bool.dichotomy (bits b) with hb | hb <;> rw [hb] <;> norm_num <;> omega

theorem pow254_lt_card : 2 ^ 254 < PALLAS_SCALAR_CARD := by
  norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]

/-- The witnessed `z` cell of loop row `r`. -/
private def rowZ (env : Environment Fp) (i₀ : ℕ) (r : ℕ) : Fp :=
  env.get (i₀ + 1 + 1 + 1 + r * 6)

/-- The `x_a` cell entering row `r`: the copied accumulator for row 0, the previous
row's witnessed `x_a'` afterwards. -/
private def rowXA (env : Environment Fp) (i₀ : ℕ) (r : ℕ) : Fp :=
  if r = 0 then env.get (i₀ + 1)
  else env.get (i₀ + 1 + 1 + 1 + (r - 1) * 6 + 1 + 1 + 1 + 1 + 1)

/-- The `x_p` cell of row `r` (row 0's is the anchored copy of `base.x`). -/
private def rowXP (env : Environment Fp) (i₀ : ℕ) (r : ℕ) : Fp :=
  env.get (i₀ + 1 + 1 + 1 + r * 6 + 1)

/-- The `y_p` cell of row `r` (row 0's is the anchored copy of `base.y`). -/
private def rowYP (env : Environment Fp) (i₀ : ℕ) (r : ℕ) : Fp :=
  env.get (i₀ + 1 + 1 + 1 + r * 6 + 1 + 1)

/-- The `λ₁` cell of row `r`. -/
private def rowL1 (env : Environment Fp) (i₀ : ℕ) (r : ℕ) : Fp :=
  env.get (i₀ + 1 + 1 + 1 + r * 6 + 1 + 1 + 1)

/-- The `λ₂` cell of row `r`. -/
private def rowL2 (env : Environment Fp) (i₀ : ℕ) (r : ℕ) : Fp :=
  env.get (i₀ + 1 + 1 + 1 + r * 6 + 1 + 1 + 1 + 1)

/-- The double-and-add row struct of row `r`. -/
private def rowD (env : Environment Fp) (i₀ r : ℕ) : DoubleAndAddRow Fp :=
  { xA := rowXA env i₀ r, xP := rowXP env i₀ r,
    lambda1 := rowL1 env i₀ r, lambda2 := rowL2 env i₀ r }

/--
The chain induction of variable-base double-and-add over cleaned row facts:
`XA, XP, YP, L1, L2` are the per-row cell values, `YAD r` the derived `Y_A` expression
value of row `r` (with `YAD (n+1)` the witnessed doubled final `y`), and `bits` the bit
values. Splitting this from `soundness` keeps each declaration within the elaboration
budget.
-/
theorem soundness_aux (n : ℕ) (P : Point Fp) (hP : P.OnCurve)
    (m : ℕ) (h2 : 2 ≤ m) (hbound : 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254)
    (XA XP YP L1 L2 YAD : ℕ → Fp) (bits : ℕ → Bool)
    (hxA0 : XA 0 = (m • P).x)
    (hYAD0 : YAD 0 = 2 * (m • P).y)
    (hyad : ∀ r, r ≤ n → YAD r = (L1 r + L2 r) * (XA r - (L1 r * L1 r - XA r - XP r)))
    (hxp : ∀ r, r ≤ n → XP r = P.x)
    (hyp : ∀ r, r ≤ n → YP r = P.y)
    (hg1 : ∀ r, r ≤ n → 2 * L1 r * (XA r - XP r) +
      2 * (((if bits r then 1 else 0) * 2 - 1) * YP r) = YAD r)
    (hsec : ∀ r, r ≤ n → L2 r * L2 r
      = XA (r + 1) + (L1 r * L1 r - XA r - XP r) + XA r)
    (hg2 : ∀ r, r ≤ n → 2 * L2 r * (XA r - XA (r + 1)) = YAD r + YAD (r + 1)) :
    XA (n + 1) = (accScalar m bits (n + 1) • P).x ∧
      YAD (n + 1) = 2 * (accScalar m bits (n + 1) • P).y := by
  -- the inductive invariant: row r enters with the accumulator `[accScalar m bits r] P`
  suffices hinv : ∀ r, r ≤ n + 1 →
      XA r = (accScalar m bits r • P).x ∧ YAD r = 2 * (accScalar m bits r • P).y by
    exact hinv (n + 1) (by omega)
  intro r hr
  induction r with
  | zero => exact ⟨hxA0, hYAD0⟩
  | succ v ih =>
    obtain ⟨ihx, ihy⟩ := ih (by omega)
    have hv : v ≤ n := by omega
    -- bounds on the accumulated multiplier
    have hMle : accScalar m bits v ≤ 2 ^ v * (m + 1) - 1 := accScalar_le bits v
    have hM2 : 2 ≤ accScalar m bits v := accScalar_two_le h2 bits v
    have hpow : 2 ^ v * (m + 1) ≤ 2 ^ (n + 1) * (m + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hMbound : 2 * accScalar m bits v + 1 < PALLAS_SCALAR_CARD := by
      have h254 := pow254_lt_card
      have hsplit : 2 ^ (n + 2) * (m + 1) = 2 * (2 ^ (n + 1) * (m + 1)) := by ring
      omega
    -- the non-degenerate spec-level step
    have hstep := step_nsmul hP bits hM2 hMbound v
    -- the entering accumulator point
    set M := accScalar m bits v with hM
    have hA0 : M • P ≠ 0 :=
      Point.nsmul_ne_zero hP (by omega) (by omega)
    -- the row equations in step_pinned's shape
    have hstepXP : XP v = (stepPoint P (bits v)).x := by
      rw [hxp v hv]
      unfold stepPoint
      rcases Bool.dichotomy (bits v) with hb | hb <;> rw [hb]
      · rfl
      · rfl
    have hstepYP : 2 * (M • P).y - 2 * L1 v * ((M • P).x - XP v)
        = 2 * (stepPoint P (bits v)).y := by
      have h := hg1 v hv
      rw [← ihx]
      unfold stepPoint
      rcases Bool.dichotomy (bits v) with hb | hb <;>
        rw [hb] at h ⊢ <;>
        simp only [Bool.false_eq_true, if_false, if_true] at h ⊢
      · show _ = 2 * (-P).y
        rw [Point.neg_y]
        linear_combination -h - ihy - 2 * hyp v hv
      · show _ = 2 * P.y
        linear_combination -h - ihy + 2 * hyp v hv
    have hstepYA : 2 * (M • P).y
        = (L1 v + L2 v) * ((M • P).x - (L1 v * L1 v - (M • P).x - XP v)) := by
      rw [← ihx, ← ihy]
      exact hyad v hv
    have hstepSec : L2 v * L2 v
        = XA (v + 1) + (L1 v * L1 v - (M • P).x - XP v) + (M • P).x := by
      rw [← ihx]
      exact hsec v hv
    have hstepYC : 4 * L2 v * ((M • P).x - XA (v + 1))
        = 4 * (M • P).y + 2 * YAD (v + 1) := by
      have h := hg2 v hv
      rw [← ihx]
      linear_combination 2 * h + 2 * ihy
    have hstep' : Point.doubleAndAdd (M • P) (stepPoint P (bits v)) =
        some ((2 * M + (if bits v then 1 else 0) * 2 - 1) • P) := hstep
    have hcoords := DoubleAndAdd.coordinates_of_constraints
      hstep' hstepYP hstepXP hstepYA hstepSec hstepYC
    have haccv : accScalar m bits (v + 1) = 2 * M + (if bits v then 1 else 0) * 2 - 1 :=
      rfl
    constructor
    · rw [haccv]
      exact hcoords.1
    · rw [haccv]
      exact hcoords.2

/--
The honest row at a small positive multiple of the base: the gate equations hold for
`lambdaCellsValue`'s cells, and they step the accumulator to `[2m + 2k - 1] P`.
-/
theorem honest_step {P : Point Fp} (hP : P.OnCurve) (bits : ℕ → Bool)
    {m : ℕ} (h2 : 2 ≤ m) (hBound : 2 * m + 1 < PALLAS_SCALAR_CARD) (b : ℕ) :
    2 * (m • P).y - 2 * (lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).lambda1 *
        ((m • P).x - P.x)
      = 2 * (stepPoint P (bits b)).y ∧
    2 * (m • P).y
      = ((lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).lambda1 +
          (lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).lambda2) *
        ((m • P).x -
          ((lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).lambda1 *
            (lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).lambda1 -
            (m • P).x - P.x)) ∧
    (lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).xANext
      = ((2 * m + (if bits b then 1 else 0) * 2 - 1) • P).x ∧
    (lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).lambda2 *
        ((m • P).x - (lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b)).xANext) -
        (m • P).y
      = ((2 * m + (if bits b then 1 else 0) * 2 - 1) • P).y := by
  set l := lambdaCellsValue P.x P.y (m • P).x (m • P).y (bits b) with hl
  have hA0 : m • P ≠ 0 := Point.nsmul_ne_zero hP (by omega) (by omega)
  have hxne1 : (m • P).x ≠ P.x := by
    have h := Point.nsmul_x_ne hP (s := 1) (t := m) (by omega) (by omega) (by omega)
    exact h
  have hxne1' : (m • P).x - P.x ≠ 0 := sub_ne_zero.mpr hxne1
  -- λ1 is the chord slope through `[m]P` and `±P`
  have hYP : 2 * (m • P).y - 2 * l.lambda1 * ((m • P).x - P.x)
      = 2 * (stepPoint P (bits b)).y := by
    rw [hl]
    unfold stepPoint lambdaCellsValue
    rcases Bool.dichotomy (bits b) with hb | hb <;> rw [hb] <;> simp only [if_true]
    · show _ = 2 * (-P).y
      rw [Point.neg_y]
      field_simp
      norm_num
    · field_simp
      ring
  -- the first incomplete addition: `x_R` is the x-coordinate of `[m ± 1] P`
  have hyPval : (if bits b then P.y else -P.y) = (stepPoint P (bits b)).y := by
    unfold stepPoint
    rcases Bool.dichotomy (bits b) with hb | hb <;> rw [hb]
    · rfl
    · rfl
  have hstep := step_nsmul hP bits h2 hBound b
  -- the spec-level step is two incomplete additions; recover the intermediate point
  rw [Point.doubleAndAdd] at hstep
  have hS0 : stepPoint P (bits b) ≠ 0 := by
    by_cases hb : bits b
    · rw [stepPoint, if_pos hb]
      exact Point.ne_zero_of_onCurve hP
    · rw [stepPoint, if_neg hb]
      exact Point.neg_ne_zero_of_ne_zero (Point.ne_zero_of_onCurve hP)
  have hxSP : (stepPoint P (bits b)).x = P.x := by
    unfold stepPoint
    rcases Bool.dichotomy (bits b) with hb | hb <;> rw [hb]
    · rfl
    · rfl
  change (do
      let t ← (m • P) ⸭ stepPoint P (bits b)
      t ⸭ (m • P)) =
    some ((2 * m + (if bits b then 1 else 0) * 2 - 1) • P) at hstep
  rw [Point.incompleteAdd_some hA0 hS0 (by rw [hxSP]; exact hxne1)] at hstep
  change (m • P + stepPoint P (bits b)) ⸭ m • P =
    some ((2 * m + (if bits b then 1 else 0) * 2 - 1) • P) at hstep
  set R := m • P + stepPoint P (bits b) with hR
  have hRne : R ≠ 0 ∧ R.x ≠ (m • P).x := by
    constructor
    · intro h0
      rw [Point.incompleteAdd_def, if_pos (Or.inl h0)] at hstep
      simp at hstep
    · intro hx
      rw [Point.incompleteAdd_def, if_pos (Or.inr (Or.inr hx))] at hstep
      simp at hstep
  have hRadd := Point.nondegenerateAdd_eq_add
    (p := m • P)
    (q := stepPoint P (bits b))
    hA0 hS0 (by rw [hxSP]; exact hxne1)
  rw [← hR] at hRadd
  simp only [Point.nondegenerateAdd] at hRadd
  rw [hxSP] at hRadd
  have hlam1 : l.lambda1 = ((m • P).y - (stepPoint P (bits b)).y) / ((m • P).x - P.x) := by
    rw [hl, ← hyPval]
    rfl
  have hxne2 : P.x - (m • P).x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxne1)
  have hRx : l.lambda1 * l.lambda1 - (m • P).x - P.x = R.x := by
    have h := congrArg Point.x hRadd
    simp only at h
    rw [← h, hlam1]
    field_simp
    ring
  have hxRne : (m • P).x - (l.lambda1 * l.lambda1 - (m • P).x - P.x) ≠ 0 := by
    rw [hRx]
    exact sub_ne_zero.mpr fun h => hRne.2 h.symm
  -- λ2's defining identity
  have hlam2 : l.lambda2
      = 2 * (m • P).y / ((m • P).x - (l.lambda1 * l.lambda1 - (m • P).x - P.x))
        - l.lambda1 := by
    rw [hl]
    rfl
  have hYA : 2 * (m • P).y
      = (l.lambda1 + l.lambda2) *
        ((m • P).x - (l.lambda1 * l.lambda1 - (m • P).x - P.x)) := by
    rw [hlam2]
    have hD : (m • P).x - (l.lambda1 ^ 2 - (m • P).x - P.x) ≠ 0 := by
      rw [pow_two]
      exact hxRne
    field_simp
    ring
  -- pin the outputs with the row engine
  have hstepSpec : Point.doubleAndAdd (m • P) (stepPoint P (bits b)) =
      some ((2 * m + (if bits b then 1 else 0) * 2 - 1) • P) :=
    step_nsmul hP bits h2 hBound b
  have hcoords := DoubleAndAdd.coordinates_of_constraints hstepSpec
    (xp := P.x) (lambda1 := l.lambda1) (lambda2 := l.lambda2)
    (xB := l.xANext)
    (YB := 2 * (l.lambda2 * ((m • P).x - l.xANext) - (m • P).y))
    hYP (by rw [hxSP]) hYA
    (by rw [hl]; unfold lambdaCellsValue; ring)
    (by ring)
  refine ⟨hYP, hYA, hcoords.1, ?_⟩
  have h := hcoords.2
  exact mul_left_cancel₀ two_ne_zero h

/-- The honest accumulator entering row `r` is `[accScalar m bits r] P`, by induction
over `honest_step`'s output conclusions. -/
theorem accVal_eq_nsmul {P : Point Fp} (hP : P.OnCurve) (bits : ℕ → Bool)
    {m : ℕ} (h2 : 2 ≤ m) (n : ℕ) (hbound : 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254) :
    ∀ r, r ≤ n + 1 →
      accVal P.x P.y (m • P).x (m • P).y bits r
        = ((accScalar m bits r • P).x, (accScalar m bits r • P).y) := by
  intro r hr
  induction r with
  | zero => rfl
  | succ v ih =>
    have hacc := ih (by omega)
    have hM2 : 2 ≤ accScalar m bits v := accScalar_two_le h2 bits v
    have hMle : accScalar m bits v ≤ 2 ^ v * (m + 1) - 1 := accScalar_le bits v
    have hpow : 2 ^ v * (m + 1) ≤ 2 ^ (n + 1) * (m + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hMbound : 2 * accScalar m bits v + 1 < PALLAS_SCALAR_CARD := by
      have h254 := pow254_lt_card
      have hsplit : 2 ^ (n + 2) * (m + 1) = 2 * (2 ^ (n + 1) * (m + 1)) := by ring
      omega
    have hstep := honest_step hP bits hM2 hMbound v
    simp only [accVal]
    rw [hacc]
    exact Prod.ext hstep.2.2.1 hstep.2.2.2

end DoubleAndAdd

end Zcash.Circuits.Ecc.Mul.Incomplete
