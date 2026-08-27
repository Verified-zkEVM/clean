import Clean.Ironwood.Ecc.MulFixed.Theorems
import Clean.Ironwood.Ecc.AddIncompleteTheorems
import Clean.Ironwood.Ecc.AddTheorems
import Clean.Ironwood.Utilities.RunningSum

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul_fixed/base_field_elem.rs`.

`Gate.circuit` (`Canonicity checks`, namespace `Gate` below) is the custom gate enabled
on the canonicity-check rows. `circuit` is the source-level entry point
`base_field_elem.rs::Config::assign` (gadget API `FixedPointBaseField::mul`): it
decomposes the 255-bit base-field element into 85 three-bit windows with a strict
running sum, runs the shared fixed-base windowed multiplication (window-table coordinate
checks, incomplete additions, offset-corrected most significant window, complete
addition), then enforces canonicity of the base-field element via a 13-window lookup
range check on `α_0 + 2¹³⁰ - t_p` and the `Canonicity checks` gate.

The windowed multiplication + complete addition is factored into the `RunningSumMul`
subcircuit (a purely virtual boundary; no extra constraints or wiring), which exposes
the running-sum cells `z₄₃`, `z₄₄`, `z₈₄` that the canonicity check copies in.
-/

namespace Zcash.Circuits.Ecc.MulFixed.BaseFieldElem

open Clean

namespace Gate

structure Input (F : Type) where
  alpha : F
  z84Alpha : F
  alpha1 : F
  alpha2 : F
  alpha0Prime : F
  z13Alpha0Prime : F
  z44Alpha : F
  z43Alpha : F
deriving ProvableStruct

def alpha0 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 252)] (row : Input K) : K :=
  row.alpha - row.z84Alpha * OfNat.ofNat (2 ^ 252)

def alpha1RangeCheck {K : Type} [One K] [Sub K] [Mul K] [OfNat K 2] [OfNat K 3]
    (row : Input K) : K :=
  row.alpha1 * (1 - row.alpha1) * (2 - row.alpha1) * (3 - row.alpha1)

def z84AlphaCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 4] (row : Input K) : K :=
  row.z84Alpha - (row.alpha1 + row.alpha2 * 4)

def alpha0PrimeCheck (row : Input (Expression Fp)) : Expression Fp :=
  row.alpha0Prime - (alpha0 row + Expression.const ((2 ^ 130 : ℕ) : Fp) -
    Expression.const tP)

def alpha0Hi120 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 120)] (row : Input K) : K :=
  row.z44Alpha - row.z84Alpha * OfNat.ofNat (2 ^ 120)

def a43 {K : Type} [Sub K] [Mul K] [OfNat K 8] (row : Input K) : K :=
  row.z43Alpha - row.z44Alpha * 8

def IsAlpha1 (alpha1 : Fp) : Prop :=
  alpha1 = 0 ∨ alpha1 = 1 ∨ alpha1 = 2 ∨ alpha1 = 3

def DecomposesBaseFieldElem (row : Input Fp) : Prop :=
  row.z84Alpha = row.alpha1 + row.alpha2 * 4 ∧
    row.alpha0Prime = alpha0 row + OfNat.ofNat (2 ^ 130) - tP

def CanonicalHighBit (row : Input Fp) : Prop :=
  row.alpha2 = 1 →
    row.alpha1 = 0 ∧ alpha0Hi120 row = 0 ∧ IsBool (a43 row) ∧ row.z13Alpha0Prime = 0

def Spec (row : Input Fp) : Prop :=
  IsAlpha1 row.alpha1 ∧ IsBool row.alpha2 ∧ DecomposesBaseFieldElem row ∧
    CanonicalHighBit row

end Gate

open CompElliptic.Curves.Pasta CompElliptic.CurveForms
open ShortWeierstrass (SWPoint)
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD PALLAS_BASE_CARD)

/-!
### Windowed multiplication subcircuit (`RunningSumMul`)

Region 1+2 of `base_field_elem.rs::Config::assign`: the strict running-sum
decomposition of `α` into 85 three-bit windows, the shared fixed-base windowed
multiplication, and the final complete addition producing `[α]B`. Exposes the
running-sum cells `z₄₃`, `z₄₄`, `z₈₄` that the canonicity check copies in.

Value model: `windowVal α w` is window `w` of the base-`8` decomposition of `α.val`,
`zValue α w = ⌊α.val / 8^w⌋` is the running-sum value, and `rowTailValue` is the
honest-prover assignment of one window row's witnessed cells.
-/

namespace RunningSumMul

/-- Window `w` of the base-`8` decomposition of `α.val`. -/
def windowVal (α : Fp) (w : ℕ) : ℕ := α.val / 8 ^ w % 8

theorem windowVal_lt (α : Fp) (w : ℕ) : windowVal α w < 8 :=
  Nat.mod_lt _ (by norm_num)

/-- The honest-prover running-sum value `z_w = ⌊α.val / 8^w⌋`. -/
def zValue (α : Fp) (w : ℕ) : Fp := ((α.val / 8 ^ w : ℕ) : Fp)

/-- The honest-prover witnessed cells of window row `w`: the next running-sum value,
the window-table point's coordinates, and the table square root `u`. -/
structure RowTail (F : Type) where
  zNext : F
  xP : F
  yP : F
  u : F
deriving ProvableStruct

def rowTailValue (B : MulFixed.FixedBase) (α : Fp) (w : ℕ) : RowTail Fp where
  zNext := zValue α (w + 1)
  xP := (MulFixed.windowPoint B.point w (windowVal α w)).x
  yP := (MulFixed.windowPoint B.point w (windowVal α w)).y
  u := B.u w (windowVal α w)

/-- Output: the multiplication result `[α]B`, and the running-sum cells the canonicity
check inspects (`z₄₃ = z_43`, `z₄₄ = z_44`, `z₈₄ = z_84`). -/
structure Output (F : Type) where
  result : Point F
  z43 : F
  z44 : F
  z84 : F
deriving ProvableStruct

/-- The witness program of one window row: take window `w` of the base-8 decomposition
of the committed base-field element (`k = α.val / 8^w % 8`, matching `windowVal`
definitionally), witness the next running-sum value, and read the three window-table
columns at `k`. -/
def rowProgram (B : MulFixed.FixedBase) (alpha : Expression Fp) (w : ℕ) :
    Witgen.M Fp (RowTail (FExpr Fp)) := do
  let xs := Vector.ofFn fun k : Fin 8 => (MulFixed.windowPoint B.point w k.val).x
  let ys := Vector.ofFn fun k : Fin 8 => (MulFixed.windowPoint B.point w k.val).y
  let us := Vector.ofFn fun k : Fin 8 => B.u w k.val
  let s := alpha.val
  let k := s / (8 ^ w : ℕ) % 8
  return RowTail.mk (s / (8 ^ (w + 1) : ℕ)).toField xs[k] ys[k] us[k]

/-- Soundness contract: the witnessed windows decompose `α` (as a value `< 8^85`), the
output is `[that value]·B`, and the exposed running-sum cells are the corresponding
partial running sums. -/
def Spec (B : MulFixed.FixedBase) (alpha : Fp) (output : Output Fp)
    (_ : ProverData Fp) : Prop :=
  ∃ ks : ℕ → ℕ, (∀ w < 85, ks w < 8) ∧
    let V := ∑ j ∈ Finset.range 85, ks j * 8 ^ j
    alpha = (V : Fp) ∧
    output.result = { x := (V • B.point).x, y := (V • B.point).y } ∧
    output.z43 = ((V / 8 ^ 43 : ℕ) : Fp) ∧
    output.z44 = ((V / 8 ^ 44 : ℕ) : Fp) ∧
    output.z84 = ((V / 8 ^ 84 : ℕ) : Fp)

def ProverAssumptions (alpha : Fp) (_ : ProverData Fp) (_ : ProverHint Fp) : Prop :=
  alpha.val < PALLAS_BASE_CARD

def ProverSpec (B : MulFixed.FixedBase) (alpha : Fp) (output : Output Fp)
    (_ : ProverHint Fp) : Prop :=
  output.result = (alpha.val : Fq) • B ∧
    output.z43 = zValue alpha 43 ∧ output.z44 = zValue alpha 44 ∧
    output.z84 = zValue alpha 84

/-! #### Helper lemmas (ported from `Short`/`MulFixed`, scaled to 85 windows) -/

/-- A `2^3`-range check pins the word to a window value `k < 8`. -/
private theorem exists_lt_of_inRange {x : Fp}
    (h : Utilities.RunningSum.InRange (2 ^ 3) x) :
    ∃ k : ℕ, k < 8 ∧ x = (k : Fp) := by
  simp [Utilities.RunningSum.InRange, Utilities.RunningSum.rangeCheckValues,
    show (2 : ℕ) ^ 3 = 8 from rfl, List.range_succ, List.range_zero] at h
  rcases h with h | h | h | h | h | h | h | h
  · exact ⟨0, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨1, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨2, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨3, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨4, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨5, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨6, by norm_num, by rw [h]; norm_num⟩
  · exact ⟨7, by norm_num, by rw [h]; norm_num⟩

/-- Casts of naturals below `8` are injective in `Fp`. -/
theorem natCast_inj_of_lt_8 {j k : ℕ} (hj : j < 8) (hk : k < 8)
    (h : (j : Fp) = (k : Fp)) : j = k := by
  have hcard : (8 : ℕ) < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this

/-- Convert the range-check word equation into the running-sum step relation. -/
private theorem step_of_word {a b : Fp} {k : ℕ}
    (h : Utilities.RunningSum.word 3 { zCur := a, zNext := b } = (k : Fp)) :
    a = (k : Fp) + 8 * b := by
  simp only [Utilities.RunningSum.word, Utilities.RunningSum.twoPowWindow] at h
  have h8 : (((2 : ℕ) ^ 3 : ℕ) : Fp) = 8 := by norm_num
  rw [h8] at h
  linear_combination h

/-- The telescoped running sum: if every step satisfies the decomposition relation and
the final value is zero, the initial value is the weighted digit sum. -/
private theorem chain_eq_sum (z : ℕ → Fp) (ks : ℕ → ℕ)
    (hword : ∀ w < 85, z w = (ks w : Fp) + 8 * z (w + 1))
    (hz85 : z 85 = 0) :
    z 0 = ((∑ j ∈ Finset.range 85, ks j * 8 ^ j : ℕ) : Fp) := by
  have key : ∀ w ≤ 85,
      z 0 = ((∑ j ∈ Finset.range w, ks j * 8 ^ j : ℕ) : Fp) + z w * ((8 ^ w : ℕ) : Fp) := by
    intro w hw
    induction w with
    | zero => simp
    | succ v ih =>
      rw [ih (by omega), hword v (by omega), Finset.sum_range_succ]
      push_cast
      ring
  have h85 := key 85 (by omega)
  rw [hz85, zero_mul, _root_.add_zero] at h85
  exact h85

/-- Weighted base-8 digit sums are bounded by `8^n`. -/
theorem sum_lt_of_windows {ks : ℕ → ℕ} {n : ℕ} (hk : ∀ j < n, ks j < 8) :
    ∑ j ∈ Finset.range n, ks j * 8 ^ j < 8 ^ n := by
  induction n with
  | zero => simp
  | succ v ih =>
    have hv := hk v (by omega)
    have := ih fun j hj => hk j (by omega)
    rw [Finset.sum_range_succ]
    have : ks v * 8 ^ v ≤ 7 * 8 ^ v := Nat.mul_le_mul_right _ (by omega)
    have h8 : (8 : ℕ) ^ (v + 1) = 8 * 8 ^ v := by ring
    omega

/-- The window decomposition recombines to the decomposed value: the `+2` offsets of the
lower 84 windows cancel against `offset_acc` in the most significant window. -/
theorem windowScalar_partialSum (ks : ℕ → ℕ) :
    MulFixed.windowScalar 84 (ks 84) + (MulFixed.partialSum ks 83 : Fq)
      = ((∑ j ∈ Finset.range 85, ks j * 8 ^ j : ℕ) : Fq) := by
  have hoffset : MulFixed.offsetAcc = ∑ j ∈ Finset.range 84, 2 * 8 ^ j := by
    unfold MulFixed.offsetAcc
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_add, pow_mul]
    norm_num [mul_comm]
  have hsplit : MulFixed.partialSum ks 83
      = (∑ j ∈ Finset.range 84, ks j * 8 ^ j) + MulFixed.offsetAcc := by
    rw [MulFixed.partialSum_eq_sum, hoffset, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [show (∑ j ∈ Finset.range 85, ks j * 8 ^ j)
      = (∑ j ∈ Finset.range 84, ks j * 8 ^ j) + ks 84 * 8 ^ 84 from
    Finset.sum_range_succ _ _]
  unfold MulFixed.windowScalar
  rw [if_pos rfl, hsplit]
  push_cast
  ring

theorem inv_lt_card {S j : ℕ} (hS : S < 2 * 8 ^ (j + 1)) (hj : j ≤ 83) :
    S < PALLAS_SCALAR_CARD := by
  have hpow : (8 : ℕ) ^ (j + 1) ≤ 8 ^ 84 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard : 2 * 8 ^ 84 < PALLAS_SCALAR_CARD := by norm_num [PALLAS_SCALAR_CARD]
  omega

theorem step_sum_lt {S t j : ℕ} (hS : S < 2 * 8 ^ (j + 1))
    (ht : t ≤ 9 * 8 ^ (j + 1)) (hj : j ≤ 82) : S + t < PALLAS_SCALAR_CARD := by
  have hpow : (8 : ℕ) ^ (j + 1) ≤ 8 ^ 83 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard : 11 * 8 ^ 83 < PALLAS_SCALAR_CARD := by norm_num [PALLAS_SCALAR_CARD]
  omega

private theorem step_lt_next {S t j : ℕ} (hS : S < 2 * 8 ^ (j + 1))
    (ht : t ≤ 9 * 8 ^ (j + 1)) : t + S < 2 * 8 ^ (j + 1 + 1) := by
  have h16 : 2 * 8 ^ (j + 1 + 1) = 16 * 8 ^ (j + 1) := by ring
  omega

/-- The base-`8` digit of `V = ∑ ks j 8^j` at position `w < 85` is `ks w`. -/
private theorem digit_eq {ks : ℕ → ℕ} (hk : ∀ w, ks w < 8) {w : ℕ} (hw : w < 85) :
    (∑ j ∈ Finset.range 85, ks j * 8 ^ j) / 8 ^ w % 8 = ks w := by
  -- split `V = low + 8^w * (ks w + 8 * high)`, with `low < 8^w`
  obtain ⟨high, hhigh⟩ : ∃ high, (∑ j ∈ Finset.range 85, ks j * 8 ^ j)
      = (∑ j ∈ Finset.range w, ks j * 8 ^ j) + 8 ^ w * (ks w + 8 * high) := by
    refine ⟨∑ j ∈ Finset.range (85 - (w + 1)), ks (w + 1 + j) * 8 ^ j, ?_⟩
    rw [show (85 : ℕ) = (w + 1) + (85 - (w + 1)) from by omega, Finset.sum_range_add,
      Finset.sum_range_succ, mul_add, _root_.add_assoc,
      show w + 1 + (85 - (w + 1)) - (w + 1) = 85 - (w + 1) from by omega]
    congr 1
    rw [mul_comm (8 ^ w) (ks w)]
    congr 1
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show w + 1 + j = w + (j + 1) from by omega, pow_add, pow_succ]; ring
  have hlow : ∑ j ∈ Finset.range w, ks j * 8 ^ j < 8 ^ w := sum_lt_of_windows fun j _ => hk j
  rw [hhigh, Nat.add_mul_div_left _ _ (pow_pos (show 0 < 8 by norm_num) w),
    Nat.div_eq_of_lt hlow, _root_.zero_add, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt (hk w)]

/-- The running-sum value at window `w` is `⌊V / 8^w⌋`: from the step relation and the
strict terminating zero, each running-sum cell equals the corresponding floor division of
the decomposed value `V = ∑ ks j 8^j`. -/
private theorem chain_div (z : ℕ → Fp) (ks : ℕ → ℕ) (hk : ∀ w, ks w < 8)
    (hword : ∀ w < 85, z w = (ks w : Fp) + 8 * z (w + 1))
    (hz85 : z 85 = 0) :
    ∀ d w, w + d = 85 → z w = (((∑ j ∈ Finset.range 85, ks j * 8 ^ j) / 8 ^ w : ℕ) : Fp) := by
  intro d
  induction d with
  | zero =>
    intro w hw
    obtain rfl : w = 85 := by omega
    rw [hz85]
    have hVlt : ∑ j ∈ Finset.range 85, ks j * 8 ^ j < 8 ^ 85 :=
      sum_lt_of_windows fun j _ => hk j
    rw [Nat.div_eq_of_lt hVlt]; simp
  | succ m ih =>
    intro w hw
    have hw85 : w < 85 := by omega
    rw [hword w hw85, ih (w + 1) (by omega)]
    -- `V / 8^w = (V/8^w % 8) + 8 * (V / 8^{w+1})`, with digit `= ks w`
    have hdig := digit_eq hk hw85
    have hdiv : (∑ j ∈ Finset.range 85, ks j * 8 ^ j) / 8 ^ w
        = ks w + 8 * ((∑ j ∈ Finset.range 85, ks j * 8 ^ j) / 8 ^ (w + 1)) := by
      conv_lhs => rw [← Nat.div_add_mod ((∑ j ∈ Finset.range 85, ks j * 8 ^ j) / 8 ^ w) 8]
      rw [hdig, pow_succ, ← Nat.div_div_eq_div_mul]
      ring
    rw [hdiv]; push_cast; ring

/-- The cell holding the running-sum value `z_{j+1} = ⌊V / 8^{j+1}⌋` (the `zNext` cell of
window `j`), relative to a circuit starting at offset `i₀`. Each window row consumes 10
cells. -/
private def zCell (i₀ : ℕ) : ℕ → ℕ
  | 0 => i₀ + 1
  | j + 1 => i₀ + 1 + 4 + j * 10

private theorem zCell_succ (i₀ j : ℕ) : zCell i₀ (j + 1) = i₀ + 1 + 4 + j * 10 := rfl

private theorem zCell_pos {j : ℕ} (i₀ : ℕ) (hj : 1 ≤ j) :
    zCell i₀ j = i₀ + 1 + 4 + (j - 1) * 10 := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [zCell_succ]; congr 1

/-- The evaluated accumulator after processing windows `0..j` (relative to a circuit
starting at offset `i₀`). Window `0` initializes the accumulator with its window point;
every subsequent window's output lives at a uniform `+10` stride. -/
private def accPt (env : Environment Fp) (i₀ : ℕ) : ℕ → Point Fp
  | 0 => { x := env.get (i₀ + 1 + 1), y := env.get (i₀ + 1 + 1 + 1) }
  | j + 1 =>
    { x := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + j * 10 + 4 + 2 + 2)).x,
      y := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + j * 10 + 4 + 2 + 2)).y }

private theorem accPt_succ (env : Environment Fp) (i₀ j : ℕ) :
    accPt env i₀ (j + 1) =
      { x := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + j * 10 + 4 + 2 + 2)).x,
        y := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + j * 10 + 4 + 2 + 2)).y } :=
  rfl

private theorem accPt_pos {j : ℕ} (env : Environment Fp) (i₀ : ℕ) (hj : 1 ≤ j) :
    accPt env i₀ j =
      { x := Expression.eval env
          (varFromOffset Point (i₀ + 1 + 4 + (j - 1) * 10 + 4 + 2 + 2)).x,
        y := Expression.eval env
          (varFromOffset Point (i₀ + 1 + 4 + (j - 1) * 10 + 4 + 2 + 2)).y } := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  rw [accPt_succ, Nat.add_sub_cancel]

/-- The cast `(↑V).val • B.point = V • B.point` (the value spec uses the raw `ℕ`-smul). -/
theorem natCast_val_nsmul (B : MulFixed.FixedBase) (V : ℕ) :
    ((V : Fq).val) • B.point = V • B.point := by
  apply B.nsmul_congr
  rw [ZMod.val_natCast]
  exact Nat.mod_modEq _ _

/-- Extract the four field equations from a witnessed `RowTail`, keeping the row opaque
(see `env_get_row` in `FullWidth.lean` and `doc/performance-problems.md`). -/
private theorem env_get_rowTail {env : ProverEnvironment Fp} {n : ℕ} {r : RowTail Fp}
    (h : ({ zNext := env.get n, xP := env.get (n + 1), yP := env.get (n + 1 + 1),
            u := env.get (n + 1 + 1 + 1) } : RowTail Fp) = r) :
    env.get n = r.zNext ∧ env.get (n + 1) = r.xP ∧
      env.get (n + 1 + 1) = r.yP ∧ env.get (n + 1 + 1 + 1) = r.u :=
  ⟨congrArg RowTail.zNext h, congrArg RowTail.xP h,
    congrArg RowTail.yP h, congrArg RowTail.u h⟩

/-- `rfl` bridges between `rowTailValue` fields and their honest values, stated at
symbolic `w` (`doc/performance-problems.md`). -/
private theorem rowTailValue_zNext (B : MulFixed.FixedBase) (α : Fp) (w : ℕ) :
    (rowTailValue B α w).zNext = zValue α (w + 1) := rfl

private theorem rowTailValue_xP (B : MulFixed.FixedBase) (α : Fp) (w : ℕ) :
    (rowTailValue B α w).xP = (MulFixed.windowPoint B.point w (windowVal α w)).x := rfl

private theorem rowTailValue_yP (B : MulFixed.FixedBase) (α : Fp) (w : ℕ) :
    (rowTailValue B α w).yP = (MulFixed.windowPoint B.point w (windowVal α w)).y := rfl

private theorem rowTailValue_u (B : MulFixed.FixedBase) (α : Fp) (w : ℕ) :
    (rowTailValue B α w).u = B.u w (windowVal α w) := rfl

/-- The evaluated row program is the honest `rowTailValue`, stated at symbolic `w` and
an opaque base-field element `α`, where every reduction is cheap. The LHS is the
`circuit_norm` normal form of the witness-IR completeness hypothesis:
`FiniteField.fromNat`/`FiniteField.val` from `NExpr.toField`/`Expression.val`, and one
range-guarded window-table read per column from the `.listGet` evaluation (see
`rowProgram_value` in `FullWidth.lean`). -/
private theorem rowProgram_value (B : MulFixed.FixedBase) (α : Fp) (w : ℕ) :
    RowTail.mk (F := Fp) (FiniteField.fromNat (FiniteField.val α / 8 ^ (w + 1)))
      (if _ : FiniteField.val α / 8 ^ w % 8 < 8 then
        (MulFixed.windowPoint B.point w (FiniteField.val α / 8 ^ w % 8)).x else 0)
      (if _ : FiniteField.val α / 8 ^ w % 8 < 8 then
        (MulFixed.windowPoint B.point w (FiniteField.val α / 8 ^ w % 8)).y else 0)
      (if _ : FiniteField.val α / 8 ^ w % 8 < 8 then
        B.u w (FiniteField.val α / 8 ^ w % 8) else 0)
    = rowTailValue B α w := by
  have h8 : FiniteField.val α / 8 ^ w % 8 < 8 := Nat.mod_lt _ (by norm_num)
  simp only [dif_pos h8]
  rfl

/-- The running sum step relation on honest values. -/
private theorem zValue_step (α : Fp) (w : ℕ) :
    zValue α w = (windowVal α w : Fp) + 8 * zValue α (w + 1) := by
  unfold zValue windowVal
  rw [show α.val / 8 ^ (w + 1) = α.val / 8 ^ w / 8 by
    rw [Nat.div_div_eq_div_mul, pow_succ]]
  conv_lhs => rw [show α.val / 8 ^ w
    = α.val / 8 ^ w % 8 + 8 * (α.val / 8 ^ w / 8) by omega]
  push_cast
  ring

/-- Membership of small casts in the range-check set. -/
private theorem inRange_of_lt {k : ℕ} (hk : k < 8) :
    Utilities.RunningSum.InRange (2 ^ 3) ((k : Fp)) := by
  simp [Utilities.RunningSum.InRange, Utilities.RunningSum.rangeCheckValues,
    show (2 : ℕ) ^ 3 = 8 from rfl, List.range_succ, List.range_zero]
  interval_cases k <;> norm_num

/-- The honest running sum values satisfy the range check. -/
private theorem word_inRange (α : Fp) (w : ℕ) {a b : Fp}
    (ha : a = zValue α w) (hb : b = zValue α (w + 1)) :
    Utilities.RunningSum.InRange (2 ^ 3)
      (Utilities.RunningSum.word 3 { zCur := a, zNext := b }) := by
  have hword : Utilities.RunningSum.word 3 { zCur := a, zNext := b }
      = (windowVal α w : Fp) := by
    show a - Utilities.RunningSum.twoPowWindow 3 * b = _
    have h8 : (Utilities.RunningSum.twoPowWindow 3 : Fp) = 8 := by
      norm_num [Utilities.RunningSum.twoPowWindow]
    rw [ha, hb, h8]
    linear_combination zValue_step α w
  rw [hword]
  exact inRange_of_lt (windowVal_lt α w)

/-- The honest row values satisfy the coordinates check. -/
private theorem coordsRow_spec (B : MulFixed.FixedBase) (α : Fp) {w : ℕ} (hw : w < 85)
    {row : MulFixed.RunningSumCoords.Input Fp}
    (hzc : row.zCur = zValue α w) (hzn : row.zNext = zValue α (w + 1))
    (hx : row.xP = (MulFixed.windowPoint B.point w (windowVal α w)).x)
    (hy : row.yP = (MulFixed.windowPoint B.point w (windowVal α w)).y)
    (hu : row.u = B.u w (windowVal α w)) :
    Coords.Spec (B.params w) (MulFixed.RunningSumCoords.coordsRow row) := by
  have hwin : (MulFixed.RunningSumCoords.coordsRow row).window = (windowVal α w : Fp) := by
    show row.zCur - row.zNext * 8 = _
    rw [hzc, hzn]
    linear_combination zValue_step α w
  refine ⟨?_, ?_, ?_⟩
  · rw [show (MulFixed.RunningSumCoords.coordsRow row).xP = row.xP from rfl, hx,
      hwin, B.interpolate_eq w hw _ (windowVal_lt α w)]
  · rw [show (MulFixed.RunningSumCoords.coordsRow row).u = row.u from rfl,
      show (MulFixed.RunningSumCoords.coordsRow row).yP = row.yP from rfl, hu, hy]
    exact B.u_mul_u w hw _ (windowVal_lt α w)
  · rw [show (MulFixed.RunningSumCoords.coordsRow row).yP = row.yP from rfl,
      show (MulFixed.RunningSumCoords.coordsRow row).xP = row.xP from rfl, hx, hy]
    have h := B.windowPoint_onCurve (w := w) (k := windowVal α w) (windowVal_lt α w)
    dsimp [Point.OnCurve] at h
    linear_combination h

/-- The running sum starts at the base-field element itself. -/
private theorem zValue_zero (α : Fp) : zValue α 0 = α := by
  unfold zValue
  rw [pow_zero, Nat.div_one, ZMod.natCast_zmod_val]

/-- The strict running sum terminates at zero for a canonical base-field element. -/
private theorem zValue_85_eq_zero {α : Fp} (hα : α.val < PALLAS_BASE_CARD) :
    zValue α 85 = 0 := by
  unfold zValue
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hα (by norm_num [PALLAS_BASE_CARD]))]
  exact Nat.cast_zero

/-- Base-8 digit recombination of the base-field element. -/
private theorem sum_windowVal {α : Fp} (hα : α.val < PALLAS_BASE_CARD) :
    ∑ j ∈ Finset.range 85, windowVal α j * 8 ^ j = α.val := by
  unfold windowVal
  have h := MulFixed.sum_base8 α.val 85
  rwa [Nat.mod_eq_of_lt (lt_of_lt_of_le hα (by norm_num [PALLAS_BASE_CARD]))] at h

-- TODO(4.30 bump): legacy defeq so `circuit_norm`'s witness-IR completeness lemmas
-- indices (lean4#12179).
end RunningSumMul

/-!
### Entry circuit (`Assign`)

`base_field_elem.rs::Config::assign`: the full source-level `FixedPointBaseField::mul`.
Composes `RunningSumMul` with the canonicity tail — a 13-window lookup range check on
`α_0 + 2¹³⁰ - t_p` and the `Canonicity checks` gate — and returns `[α]B`.
-/

open Gate

/-- `t_p` as a natural number (`p = 2^254 + tPNat` for the Pallas base field). -/
def tPNat : ℕ := 45560315531419706090280762371685220353

/-- `p = 2^254 + t_p` for the Pallas base field. -/
theorem base_card_eq : PALLAS_BASE_CARD = 2 ^ 254 + tPNat := by
  norm_num [PALLAS_BASE_CARD, tPNat]

/-- From the lookup digit sum `S < 2^130` and the field equation `S = α0 + 2^130 - t_p`
(with `α0 < 2^132` ruling out wraparound), conclude `α0 < t_p`. Factored so the heavy
`ZMod.val` reasoning is kernel-checked in isolation. -/
theorem alpha0_lt_tp {S α0 : ℕ} (hSlt : S < 2 ^ 130) (hα0lt : α0 < 2 ^ 132)
    (heq : (S : Fp) = (α0 : Fp) + (2 : Fp) ^ 130 - (tPNat : Fp)) : α0 < tPNat := by
  -- additive form (no `Nat.cast_sub`): `↑(S + t_p) = ↑(α0 + 2^130)`
  have hadd : ((S + tPNat : ℕ) : Fp) = ((α0 + 2 ^ 130 : ℕ) : Fp) := by
    push_cast; linear_combination heq
  have hmod := (ZMod.natCast_eq_natCast_iff _ _ _).mp hadd
  -- the two literal facts (powers stay opaque to `omega`)
  have hlit : (2 : ℕ) ^ 130 + tPNat < PALLAS_BASE_CARD ∧ 2 ^ 132 + 2 ^ 130 < PALLAS_BASE_CARD := by
    norm_num [PALLAS_BASE_CARD, tPNat]
  have hSp : S + tPNat < PALLAS_BASE_CARD := by omega
  have hMp : α0 + 2 ^ 130 < PALLAS_BASE_CARD := by omega
  rw [Nat.ModEq, Nat.mod_eq_of_lt hSp, Nat.mod_eq_of_lt hMp] at hmod
  omega

/-- The honest-prover canonicity-gate obligation, proved over an **abstract** row whose
field values are pinned to the honest assignment. Stating it generically keeps the heavy
whnf/kernel work off the giant `m.z84` running-sum term that the concrete entry-circuit
row carries (see `doc/performance-problems.md`, the giant-foldl cliff). The hypotheses are
exactly the honest cell values: `d := α.val / 8^84` is the top window, `α1 = d % 4`,
`α2 = d / 4`, `α0' = α - d·2²⁵² + 2¹³⁰ - t_p`, and the running-sum cells `z₄₄`, `z₄₃`,
plus the lookup output `z₁₃ = ⌊α0'.val / 2¹³⁰⌋`. Canonicity (`α.val < p`) forces the high
window to `4` and `α0 < t_p` in the `α2 = 1` branch. -/
theorem honest_canon_spec {row : Input Fp} {α : Fp}
    (hcanon : α.val < PALLAS_BASE_CARD)
    (ha : row.alpha = α)
    (hz84 : row.z84Alpha = ((α.val / 8 ^ 84 : ℕ) : Fp))
    (ha1 : row.alpha1 = ((α.val / 8 ^ 84 % 4 : ℕ) : Fp))
    (ha2 : row.alpha2 = ((α.val / 8 ^ 84 / 4 : ℕ) : Fp))
    (hap : row.alpha0Prime
      = α - ((α.val / 8 ^ 84 : ℕ) : Fp) * (2 : Fp) ^ 252 + (2 : Fp) ^ 130 - (tPNat : Fp))
    (hz44 : row.z44Alpha = ((α.val / 8 ^ 44 : ℕ) : Fp))
    (hz43 : row.z43Alpha = ((α.val / 8 ^ 43 : ℕ) : Fp))
    (hz13 : row.z13Alpha0Prime = ((row.alpha0Prime.val / 2 ^ 130 : ℕ) : Fp)) :
    DecomposesBaseFieldElem row ∧ CanonicalHighBit row := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- z84_check: `d = d%4 + 4·(d/4)`
    rw [hz84, ha1, ha2]
    have key : α.val / 8 ^ 84 % 4 + 4 * (α.val / 8 ^ 84 / 4) = α.val / 8 ^ 84 :=
      Nat.mod_add_div _ _
    conv_lhs => rw [← key]
    push_cast; ring
  · -- alpha0Prime_check: the OfNat ↔ `(2:Fp)^n` and `t_p` bridges
    rw [hap]
    unfold alpha0
    rw [ha, hz84, show (OfNat.ofNat (2 ^ 252) : Fp) = (2 : Fp) ^ 252 from by norm_num,
      show (OfNat.ofNat (2 ^ 130) : Fp) = (2 : Fp) ^ 130 from by norm_num]
    push_cast [tP, tPNat]
    ring
  · -- CanonicalHighBit: the `α2 = 1` branch
    intro hα2eq
    rw [ha2] at hα2eq
    -- `d < 5` from canonicity (`p < 5·2²⁵²`), and `d/4 = 1`, so `d = 4`
    have hb5 : PALLAS_BASE_CARD < 8 ^ 84 * 5 := by norm_num [PALLAS_BASE_CARD]
    have hdlt5 : α.val / 8 ^ 84 < 5 := Nat.div_lt_of_lt_mul (lt_trans hcanon hb5)
    have hd4 : α.val / 8 ^ 84 / 4 = 1 :=
      RunningSumMul.natCast_inj_of_lt_8 (by omega) (by norm_num) (by rw [hα2eq]; norm_num)
    have hd_eq4 : α.val / 8 ^ 84 = 4 := by omega
    -- split `α.val = α0 + 2²⁵⁴` with `α0 = α.val % 2²⁵² < t_p`
    have h884 : (8 : ℕ) ^ 84 = 2 ^ 252 := by norm_num
    have hd_eq4' : α.val / 2 ^ 252 = 4 := by rw [← h884]; exact hd_eq4
    have hsplit : α.val = α.val % 2 ^ 252 + 2 ^ 254 := by
      have hdm := Nat.div_add_mod α.val (2 ^ 252)
      rw [hd_eq4'] at hdm
      have hpp : (2 : ℕ) ^ 252 * 4 = 2 ^ 254 := by ring
      omega
    have hbc := base_card_eq
    have hα0tp : α.val % 2 ^ 252 < tPNat := by omega
    -- division facts for the running-sum cells
    have htp129 : tPNat < 2 ^ 129 := by norm_num [tPNat]
    have htp132 : tPNat < 2 ^ 132 := by norm_num [tPNat]
    have htp130 : tPNat < 2 ^ 130 := by norm_num [tPNat]
    have h44 : α.val / 8 ^ 44 = 2 ^ 122 := by
      rw [show (8 : ℕ) ^ 44 = 2 ^ 132 from by norm_num, hsplit,
        show (2 : ℕ) ^ 254 = 2 ^ 122 * 2 ^ 132 from by ring,
        Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt (lt_trans hα0tp htp132), _root_.zero_add]
    have h43 : α.val / 8 ^ 43 = 2 ^ 125 := by
      rw [show (8 : ℕ) ^ 43 = 2 ^ 129 from by norm_num, hsplit,
        show (2 : ℕ) ^ 254 = 2 ^ 125 * 2 ^ 129 from by ring,
        Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt (lt_trans hα0tp htp129), _root_.zero_add]
    -- the lookup element `α0' = ↑(α0 + 2¹³⁰ - t_p)`, a value `< 2¹³⁰`
    have hge : tPNat ≤ α.val % 2 ^ 252 + 2 ^ 130 := by omega
    have hαval : α = ((α.val % 2 ^ 252 + 2 ^ 254 : ℕ) : Fp) := by
      rw [← hsplit]; exact (ZMod.natCast_zmod_val α).symm
    have hNnat : row.alpha0Prime = ((α.val % 2 ^ 252 + 2 ^ 130 - tPNat : ℕ) : Fp) := by
      rw [hap, hd_eq4, Nat.cast_sub hge]
      conv_lhs => rw [hαval]
      push_cast; ring
    have hNlt : α.val % 2 ^ 252 + 2 ^ 130 - tPNat < 2 ^ 130 := by omega
    have hNltp : α.val % 2 ^ 252 + 2 ^ 130 - tPNat < PALLAS_BASE_CARD := by
      have h2130P : (2 : ℕ) ^ 130 < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
      omega
    have hap_val : row.alpha0Prime.val < 2 ^ 130 := by
      rw [hNnat, ZMod.val_natCast_of_lt hNltp]; exact hNlt
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- α1 = 0
      rw [ha1, hd_eq4]; norm_num
    · -- alpha0_hi_120 = 0
      unfold alpha0Hi120
      rw [hz44, hz84, h44, hd_eq4,
        show (OfNat.ofNat (2 ^ 120) : Fp) = (2 : Fp) ^ 120 from by norm_num]
      push_cast; ring
    · -- IsBool a43
      refine Or.inl ?_
      unfold a43
      rw [hz43, hz44, h43, h44]
      push_cast; ring
    · -- z13 = 0
      rw [hz13, Nat.div_eq_of_lt hap_val]; norm_num

end Zcash.Circuits.Ecc.MulFixed.BaseFieldElem
