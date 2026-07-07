import Clean.Orchard.Ecc.MulFixed
import Clean.Orchard.Ecc.AddIncomplete
import Clean.Orchard.Ecc.Add
import Clean.Orchard.Utilities

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

namespace Orchard.Ecc.MulFixed.BaseFieldElem

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

def main (row : Var Input Fp) : Circuit Fp Unit := do
  assertZero (row.alpha2 * row.alpha1)
  assertZero (row.alpha2 * alpha0Hi120 row)
  assertZero (row.alpha2 * (a43 row * (a43 row - 1)))
  assertZero (row.alpha2 * row.z13Alpha0Prime)
  assertZero (alpha1RangeCheck row)
  assertBool row.alpha2
  assertZero (z84AlphaCheck row)
  assertZero (alpha0PrimeCheck row)

def circuit : FormalAssertion Fp Input where
  name := "GATE Canonicity checks"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, IsAlpha1, DecomposesBaseFieldElem,
      CanonicalHighBit, alpha0, alpha1RangeCheck, z84AlphaCheck, alpha0PrimeCheck,
      alpha0Hi120, a43, tP]
    rcases h_holds with ⟨hAlpha21, hAlpha2Hi, hAlpha2A43, hAlpha2Z13, hAlpha1Range,
      hAlpha2Bool, hZ84, hAlpha0Prime⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases mul_eq_zero.mp hAlpha1Range with hPrefix | h3
      · rcases mul_eq_zero.mp hPrefix with hPrefix | h2
        · rcases mul_eq_zero.mp hPrefix with h0 | h1
          · exact Or.inl h0
          · exact Or.inr (Or.inl (by linear_combination -h1))
        · exact Or.inr (Or.inr (Or.inl (by linear_combination -h2)))
      · exact Or.inr (Or.inr (Or.inr (by linear_combination -h3)))
    · exact hAlpha2Bool
    · constructor
      · exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hZ84)
      · exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hAlpha0Prime)
    · intro hAlpha2
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hAlpha2] at hAlpha21
        simpa using hAlpha21
      · rw [hAlpha2] at hAlpha2Hi
        simpa [sub_eq_add_neg] using hAlpha2Hi
      · have hA43Poly :
            (input_z43Alpha - input_z44Alpha * 8) *
              ((input_z43Alpha - input_z44Alpha * 8) - 1) = 0 := by
          have hMul :
              input_alpha2 * ((input_z43Alpha - input_z44Alpha * 8) *
                ((input_z43Alpha - input_z44Alpha * 8) - 1)) = 0 := by
            simpa [sub_eq_add_neg] using hAlpha2A43
          rw [hAlpha2] at hMul
          simpa using hMul
        exact IsBool.iff_mul_sub_one.mpr hA43Poly
      · rw [hAlpha2] at hAlpha2Z13
        simpa using hAlpha2Z13
  completeness := by
    circuit_proof_start [main, Spec, IsAlpha1, DecomposesBaseFieldElem,
      CanonicalHighBit, alpha0, alpha1RangeCheck, z84AlphaCheck, alpha0PrimeCheck,
      alpha0Hi120, a43, tP]
    rcases h_spec with ⟨hAlpha1, hAlpha2, ⟨hZ84, hAlpha0Prime⟩, hCanon⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · exact by
          rw [h1, (hCanon h1).1]
          ring
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · rw [h1]
        simpa [sub_eq_add_neg] using (hCanon h1).2.1
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · exact by
          have hBoolA43 := IsBool.iff_mul_sub_one.mp (hCanon h1).2.2.1
          rw [h1]
          simpa [sub_eq_add_neg] using hBoolA43
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · rw [h1, (hCanon h1).2.2.2]
        ring
    · rcases hAlpha1 with h0 | h1 | h2 | h3
      · rw [h0]
        ring
      · rw [h1]
        ring
      · rw [h2]
        ring
      · rw [h3]
        ring
    · exact hAlpha2
    · rw [hZ84]
      ring
    · rw [hAlpha0Prime]
      ring

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
    Witgen.M Fp (RowTail (Witgen.FExpr Fp)) := do
  let xs := Vector.ofFn fun k : Fin 8 => (MulFixed.windowPoint B.point w k.val).x
  let ys := Vector.ofFn fun k : Fin 8 => (MulFixed.windowPoint B.point w k.val).y
  let us := Vector.ofFn fun k : Fin 8 => B.u w k.val
  let s := alpha.val
  let k := s / (8 ^ w : ℕ) % 8
  return RowTail.mk (s / (8 ^ (w + 1) : ℕ)).toField xs[k] ys[k] us[k]

def main (B : MulFixed.FixedBase) (alpha : Var field Fp) :
    Circuit Fp (Var Output Fp) := do
  -- `copy_decompose`: `z_0` is a copy of `α`
  let z₀ <== alpha
  -- window 0 initializes the accumulator
  let t₀ : Var RowTail Fp ← witnessProgram (rowProgram B alpha 0)
  Utilities.RunningSum.circuit 3 { zCur := z₀, zNext := t₀.zNext }
  MulFixed.RunningSumCoords.circuit (B.params 0)
    { zCur := z₀, zNext := t₀.zNext, xP := t₀.xP, yP := t₀.yP, u := t₀.u }
  let acc₀ : Var Point Fp := { x := t₀.xP, y := t₀.yP }
  -- windows 1..42 are added with incomplete addition; final `zCur = z_43`
  let (acc₄₂, z₄₃) ← Circuit.foldl (Vector.finRange 42) (acc₀, t₀.zNext) fun (acc, zCur) i => do
    let t : Var RowTail Fp ← witnessProgram (rowProgram B alpha (i.val + 1))
    Utilities.RunningSum.circuit 3 { zCur := zCur, zNext := t.zNext }
    MulFixed.RunningSumCoords.circuit (B.params (i.val + 1))
      { zCur := zCur, zNext := t.zNext, xP := t.xP, yP := t.yP, u := t.u }
    let acc' ← AddIncomplete.circuit { p := { x := t.xP, y := t.yP }, q := acc }
    return (acc', t.zNext)
  -- explicit window 43; `t₄₃.zNext = z_44`
  let t₄₃ : Var RowTail Fp ← witnessProgram (rowProgram B alpha 43)
  Utilities.RunningSum.circuit 3 { zCur := z₄₃, zNext := t₄₃.zNext }
  MulFixed.RunningSumCoords.circuit (B.params 43)
    { zCur := z₄₃, zNext := t₄₃.zNext, xP := t₄₃.xP, yP := t₄₃.yP, u := t₄₃.u }
  let acc₄₃ ← AddIncomplete.circuit { p := { x := t₄₃.xP, y := t₄₃.yP }, q := acc₄₂ }
  -- windows 44..83 are added with incomplete addition; final `zCur = z_84`
  let (acc₈₃, z₈₄) ← Circuit.foldl (Vector.finRange 40) (acc₄₃, t₄₃.zNext) fun (acc, zCur) i => do
    let t : Var RowTail Fp ← witnessProgram (rowProgram B alpha (i.val + 44))
    Utilities.RunningSum.circuit 3 { zCur := zCur, zNext := t.zNext }
    MulFixed.RunningSumCoords.circuit (B.params (i.val + 44))
      { zCur := zCur, zNext := t.zNext, xP := t.xP, yP := t.yP, u := t.u }
    let acc' ← AddIncomplete.circuit { p := { x := t.xP, y := t.yP }, q := acc }
    return (acc', t.zNext)
  -- most significant window 84
  let t₈₄ : Var RowTail Fp ← witnessProgram (rowProgram B alpha 84)
  Utilities.RunningSum.circuit 3 { zCur := z₈₄, zNext := t₈₄.zNext }
  MulFixed.RunningSumCoords.circuit (B.params 84)
    { zCur := z₈₄, zNext := t₈₄.zNext, xP := t₈₄.xP, yP := t₈₄.yP, u := t₈₄.u }
  -- strict decomposition: the final running sum value is zero
  t₈₄.zNext === (0 : Expression Fp)
  -- `[α]B` by complete addition of the most significant window
  let result ← Add.circuit { p := { x := t₈₄.xP, y := t₈₄.yP }, q := acc₈₃ }
  return { result := result, z43 := z₄₃, z44 := t₄₃.zNext, z84 := z₈₄ }

instance elaborated (B : MulFixed.FixedBase) :
    ElaboratedCircuit Fp field Output (main B) := by
  elaborate_circuit

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
private theorem natCast_inj_of_lt_8 {j k : ℕ} (hj : j < 8) (hk : k < 8)
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
private theorem sum_lt_of_windows {ks : ℕ → ℕ} {n : ℕ} (hk : ∀ j < n, ks j < 8) :
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
private theorem windowScalar_partialSum (ks : ℕ → ℕ) :
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

private theorem inv_lt_card {S j : ℕ} (hS : S < 2 * 8 ^ (j + 1)) (hj : j ≤ 83) :
    S < PALLAS_SCALAR_CARD := by
  have hpow : (8 : ℕ) ^ (j + 1) ≤ 8 ^ 84 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard : 2 * 8 ^ 84 < PALLAS_SCALAR_CARD := by norm_num [PALLAS_SCALAR_CARD]
  omega

private theorem step_sum_lt {S t j : ℕ} (hS : S < 2 * 8 ^ (j + 1))
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
private theorem natCast_val_nsmul (B : MulFixed.FixedBase) (V : ℕ) :
    ((V : Fq).val) • B.point = V • B.point := by
  apply B.nsmul_congr
  rw [ZMod.val_natCast]
  exact Nat.mod_modEq _ _

theorem soundness (B : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main B) (fun _ _ => True) (Spec B) := by
  circuit_proof_start [main, Spec,
    Utilities.RunningSum.circuit, Utilities.RunningSum.Spec,
    MulFixed.RunningSumCoords.circuit, MulFixed.RunningSumCoords.Spec,
    AddIncomplete.circuit, AddIncomplete.Spec, AddIncomplete.Assumptions,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨h_z0, h_rs0, h_coords0, ⟨h_seg1_w1, h_seg1_loop⟩, h_rs43, h_coords43, h_inc43,
    ⟨h_seg2_w44, h_seg2_loop⟩, h_rs84, h_coords84, h_z85, h_add⟩ := h_holds
  simp only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub] at h_seg1_w1 h_seg1_loop h_rs43 h_coords43 h_inc43 h_seg2_w44 h_seg2_loop h_rs84 h_coords84 h_z85 h_add ⊢
  -- unified per-window hypothesis for windows `1..83` (gluing the two foldl segments and
  -- the explicit window 43); window of iteration `j` is `j + 1`
  have h_loop' : ∀ (j : ℕ), j < 83 →
      Utilities.RunningSum.InRange (2 ^ 3) (Utilities.RunningSum.word 3
        { zCur := env.get (zCell i₀ j), zNext := env.get (zCell i₀ (j + 1)) }) ∧
      Coords.Spec (B.params (j + 1)) (MulFixed.RunningSumCoords.coordsRow
        { zCur := env.get (zCell i₀ j), zNext := env.get (zCell i₀ (j + 1)),
          xP := env.get (i₀ + 1 + 4 + j * 10 + 1),
          yP := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1),
          u := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1 + 1) }) ∧
      (({ x := env.get (i₀ + 1 + 4 + j * 10 + 1),
            y := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) } : Point Fp).OnCurve ∧
          (accPt env i₀ j).OnCurve ∧
          ¬env.get (i₀ + 1 + 4 + j * 10 + 1) = (accPt env i₀ j).x →
        (accPt env i₀ (j + 1)).OnCurve ∧
          accPt env i₀ (j + 1) =
            { x := env.get (i₀ + 1 + 4 + j * 10 + 1),
              y := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) } +
              accPt env i₀ j) := by
    intro j hj
    -- dispatch on which circuit segment covers window `j + 1`
    rcases Nat.lt_or_ge j 1 with hj0 | hj1
    · -- window 1
      obtain rfl : j = 0 := by omega
      exact h_seg1_w1
    rcases Nat.lt_or_ge j 42 with hj42 | hj42'
    · -- windows 2..42 (foldl1 generic, `i = j - 1`)
      have h := h_seg1_loop (j - 1) (by omega)
      rw [show j - 1 + 1 = j from by omega] at h
      rw [zCell_pos i₀ (by omega), accPt_pos env i₀ (by omega)]
      exact h
    rcases Nat.lt_or_ge j 43 with hj43 | hj43'
    · -- window 43 (explicit)
      obtain rfl : j = 42 := by omega
      exact ⟨h_rs43, h_coords43, h_inc43⟩
    rcases Nat.lt_or_ge j 44 with hj44 | hj44'
    · -- window 44 (foldl2 first)
      obtain rfl : j = 43 := by omega
      exact h_seg2_w44
    · -- windows 45..83 (foldl2 generic, `i = j - 44`)
      have h := h_seg2_loop (j - 44) (by omega)
      rw [show j - 44 + 1 = j - 43 from by omega] at h
      rw [show i₀ + 1 + 4 + 42 * 10 + 4 + 6 + (j - 44) * 10 = i₀ + 1 + 4 + (j - 1) * 10 from by
          omega,
        show i₀ + 1 + 4 + 42 * 10 + 4 + 6 + (j - 43) * 10 = i₀ + 1 + 4 + j * 10 from by omega,
        show j - 43 + 44 = j + 1 from by omega] at h
      rw [zCell_pos i₀ (by omega), zCell_succ, accPt_pos env i₀ (by omega)]
      exact h
  -- window values from the range checks
  obtain ⟨k0, hk0_lt, hw0⟩ := exists_lt_of_inRange h_rs0
  obtain ⟨k84, hk84_lt, hw84⟩ := exists_lt_of_inRange h_rs84
  have hkE : ∀ j : Fin 83, ∃ k : ℕ, k < 8 ∧
      Utilities.RunningSum.word 3
          { zCur := env.get (zCell i₀ j.val), zNext := env.get (zCell i₀ (j.val + 1)) }
        = (k : Fp) :=
    fun j => exists_lt_of_inRange (h_loop' j.1 j.2).1
  choose kf hkf_lt hkf using hkE
  -- combined window function, kept opaque (see `doc/performance-problems.md`)
  obtain ⟨ks, hks_def⟩ : ∃ ks' : ℕ → ℕ, ks' = fun w =>
      if w = 0 then k0 else if h : w - 1 < 83 then kf ⟨w - 1, h⟩ else k84 := ⟨_, rfl⟩
  have hks0 : ks 0 = k0 := by simp [hks_def]
  have hksj : ∀ (j : ℕ) (hj : j < 83), ks (j + 1) = kf ⟨j, hj⟩ := by
    intro j hj
    simp [hks_def, hj]
  have hks84 : ks 84 = k84 := by norm_num [hks_def]
  have hks_lt : ∀ w, ks w < 8 := by
    intro w
    simp only [hks_def]
    split_ifs
    · exact hk0_lt
    · exact hkf_lt _
    · exact hk84_lt
  -- the running sum values as an opaque function
  obtain ⟨zf, hzf_def⟩ : ∃ zf' : ℕ → Fp, zf' = fun w =>
      if w = 0 then env.get i₀
      else if h : w ≤ 84 then env.get (zCell i₀ (w - 1))
      else env.get (zCell i₀ 84) := ⟨_, rfl⟩
  have hzf0 : zf 0 = env.get i₀ := by simp [hzf_def]
  have hzf_succ : ∀ j, j ≤ 83 → zf (j + 1) = env.get (zCell i₀ j) := by
    intro j hj
    simp only [hzf_def]
    rw [if_neg (by omega), dif_pos (by omega), Nat.add_sub_cancel]
  have hzf85 : zf 85 = env.get (zCell i₀ 84) := by
    simp only [hzf_def]
    rw [if_neg (by omega), dif_neg (by omega)]
  -- telescope the running sum into the decomposed value
  have hchain : ∀ w < 85, zf w = (ks w : Fp) + 8 * zf (w + 1) := by
    intro w hw
    rcases w with _ | w
    · rw [hzf0, hzf_succ 0 (by omega), hks0]
      exact step_of_word hw0
    · rcases Nat.lt_or_ge w 83 with hj | hj
      · rw [hzf_succ w (by omega), hzf_succ (w + 1) (by omega), hksj w hj]
        have hk := hkf ⟨w, hj⟩
        rw [show (⟨w, hj⟩ : Fin 83).val = w from rfl] at hk
        exact step_of_word hk
      · have hweq : w = 83 := by omega
        subst hweq
        rw [hzf_succ 83 (by omega), hzf85, hks84]
        exact step_of_word (by
          have h83' : env.get (zCell i₀ 83) = env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10) := rfl
          have h84' : env.get (zCell i₀ 84) = env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10) := rfl
          rw [h83', h84']; exact hw84)
  obtain ⟨V, hV_def⟩ : ∃ V : ℕ, V = ∑ j ∈ Finset.range 85, ks j * 8 ^ j := ⟨_, rfl⟩
  have hαV : input = (V : Fp) := by
    rw [← h_z0, ← hzf0, chain_eq_sum zf ks hchain (by rw [hzf85]; exact h_z85), hV_def]
  -- bound: `V < 8^85`
  have hVlt : V < 8 ^ 85 := by rw [hV_def]; exact sum_lt_of_windows fun j _ => hks_lt j
  -- accumulator invariant: after windows `0..w`, the accumulator is `[partialSum ks w]B`
  have h_inv : ∀ (w : ℕ), w ≤ 83 →
      accPt env i₀ w
        = { x := (MulFixed.partialSum ks w • B.point).x,
            y := (MulFixed.partialSum ks w • B.point).y } := by
    intro w hw
    induction w with
    | zero =>
      have hwindow : (MulFixed.RunningSumCoords.coordsRow
          { zCur := env.get i₀, zNext := env.get (i₀ + 1), xP := env.get (i₀ + 1 + 1),
            yP := env.get (i₀ + 1 + 1 + 1),
            u := env.get (i₀ + 1 + 1 + 1 + 1) } : MulFixed.CoordsRow Fp).window = (k0 : Fp) := by
        show env.get i₀ - env.get (i₀ + 1) * 8 = (k0 : Fp)
        linear_combination step_of_word hw0
      obtain ⟨hpx, hpy⟩ := B.coords_eq_windowPoint (by norm_num) hk0_lt hwindow h_coords0
      have hval0 : (MulFixed.windowScalar 0 k0).val = MulFixed.partialSum ks 0 := by
        rw [MulFixed.windowScalar_val (by norm_num) hk0_lt, MulFixed.partialSum, hks0]
        simp
      show ({ x := env.get (i₀ + 1 + 1), y := env.get (i₀ + 1 + 1 + 1) } : Point Fp) = _
      rw [show (MulFixed.RunningSumCoords.coordsRow
          { zCur := env.get i₀, zNext := env.get (i₀ + 1), xP := env.get (i₀ + 1 + 1),
            yP := env.get (i₀ + 1 + 1 + 1),
            u := env.get (i₀ + 1 + 1 + 1 + 1) } : MulFixed.CoordsRow Fp).xP
          = env.get (i₀ + 1 + 1) from rfl] at hpx
      rw [show (MulFixed.RunningSumCoords.coordsRow
          { zCur := env.get i₀, zNext := env.get (i₀ + 1), xP := env.get (i₀ + 1 + 1),
            yP := env.get (i₀ + 1 + 1 + 1),
            u := env.get (i₀ + 1 + 1 + 1 + 1) } : MulFixed.CoordsRow Fp).yP
          = env.get (i₀ + 1 + 1 + 1) from rfl] at hpy
      rw [hpx, hpy]
      unfold MulFixed.windowPoint
      rw [hval0]
    | succ j ih =>
      have hj : j < 83 := by omega
      have hacc := ih (by omega)
      obtain ⟨_, h_coordsRow, h_inc⟩ := h_loop' j hj
      have hwindow : (MulFixed.RunningSumCoords.coordsRow
          { zCur := env.get (zCell i₀ j), zNext := env.get (zCell i₀ (j + 1)),
            xP := env.get (i₀ + 1 + 4 + j * 10 + 1),
            yP := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1),
            u := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1 + 1) } : MulFixed.CoordsRow Fp).window
          = (kf ⟨j, hj⟩ : Fp) := by
        show env.get (zCell i₀ j) - env.get (zCell i₀ (j + 1)) * 8 = (kf ⟨j, hj⟩ : Fp)
        linear_combination step_of_word (hkf ⟨j, hj⟩)
      obtain ⟨hpx, hpy⟩ :=
        B.coords_eq_windowPoint (show j + 1 < 85 by omega) (hkf_lt ⟨j, hj⟩) hwindow h_coordsRow
      replace hpx : env.get (i₀ + 1 + 4 + j * 10 + 1)
          = (MulFixed.windowPoint B.point (j + 1) (kf ⟨j, hj⟩)).x := hpx
      replace hpy : env.get (i₀ + 1 + 4 + j * 10 + 1 + 1)
          = (MulFixed.windowPoint B.point (j + 1) (kf ⟨j, hj⟩)).y := hpy
      rw [← hksj j hj] at hpx hpy
      set t := (MulFixed.windowScalar (j + 1) (ks (j + 1))).val with ht_def
      have hval : t = (ks (j + 1) + 2) * 8 ^ (j + 1) :=
        MulFixed.windowScalar_val (by omega) (hks_lt (j + 1))
      have hS_lt := MulFixed.partialSum_lt ks j fun _ _ => hks_lt _
      have hS_pos := MulFixed.partialSum_pos ks j
      have hpow : 0 < (8 : ℕ) ^ (j + 1) := pow_pos (by norm_num) _
      have ht_lower : 2 * 8 ^ (j + 1) ≤ t := by
        rw [hval]; exact Nat.mul_le_mul_right _ (by omega)
      have ht_upper : t ≤ 9 * 8 ^ (j + 1) := by
        rw [hval]; exact Nat.mul_le_mul_right _ (by have := hks_lt (j + 1); omega)
      have hS_card := inv_lt_card hS_lt (by omega)
      have hsum_card := step_sum_lt hS_lt ht_upper (by omega)
      have hwp : MulFixed.windowPoint B.point (j + 1) (ks (j + 1)) = t • B.point := rfl
      rw [hwp] at hpx hpy
      have h_spec := h_inc ⟨by
          rw [hpx, hpy]
          exact B.nsmul_onCurve (by omega) (by omega),
        by
          rw [hacc]
          exact B.nsmul_onCurve hS_pos hS_card,
        by
          rw [hpx, hacc]
          show (t • B.point).x ≠ (MulFixed.partialSum ks j • B.point).x
          exact B.nsmul_x_ne hS_pos (by omega) hsum_card⟩
      rw [h_spec.2, hpx, hpy, hacc]
      rw [Point.nsmul_add_nsmul B.onCurve]
      congr 1
      rw [MulFixed.partialSum, hval]
      omega
  -- the window-84 point
  have hwindow84 : (MulFixed.RunningSumCoords.coordsRow
      { zCur := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10),
        zNext := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10),
        xP := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1),
        yP := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1),
        u := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1 + 1) }
        : MulFixed.CoordsRow Fp).window = (k84 : Fp) := by
    show env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10)
        - env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10) * 8 = (k84 : Fp)
    linear_combination step_of_word hw84
  obtain ⟨hpx84, hpy84⟩ :=
    B.coords_eq_windowPoint (show (84 : ℕ) < 85 by norm_num) hk84_lt hwindow84 h_coords84
  -- window-84 and accumulated scalars kept opaque (`doc/performance-problems.md`)
  obtain ⟨t84, ht84_def⟩ : ∃ t : ℕ, t = (MulFixed.windowScalar 84 k84).val := ⟨_, rfl⟩
  have hP84_eq : MulFixed.windowPoint B.point 84 k84 = t84 • B.point := by
    rw [ht84_def]; rfl
  replace hpx84 : env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1) = (t84 • B.point).x := by
    rw [← hP84_eq]; exact hpx84
  replace hpy84 : env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1) = (t84 • B.point).y := by
    rw [← hP84_eq]; exact hpy84
  obtain ⟨S83, hS83_def⟩ : ∃ S : ℕ, S = MulFixed.partialSum ks 83 := ⟨_, rfl⟩
  have hS83_lt : S83 < 2 * 8 ^ (83 + 1) := by
    rw [hS83_def]; exact MulFixed.partialSum_lt ks 83 fun _ _ => hks_lt _
  have hS83_pos : 0 < S83 := by rw [hS83_def]; exact MulFixed.partialSum_pos ks 83
  have hS83_card := inv_lt_card hS83_lt (by omega)
  have hacc83 :
      ({ x := Expression.eval env
            (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10 + 4 + 2 + 2)).x,
         y := Expression.eval env
            (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10 + 4 + 2 + 2)).y }
        : Point Fp)
      = { x := (S83 • B.point).x, y := (S83 • B.point).y } := by
    rw [hS83_def]
    have := h_inv 83 (by omega)
    rw [accPt_succ] at this
    convert this using 4
  -- the complete addition produces `[V]B`
  have hValidP :
      ({ x := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1),
         y := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1) } :
        Point Fp).Valid := by
    rw [hpx84, hpy84]
    exact Point.valid_nsmul (.inl B.onCurve) t84
  have hValidAcc :
    ({ x := Expression.eval env
          (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10 + 4 + 2 + 2)).x,
        y := Expression.eval env
          (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10 + 4 + 2 + 2)).y }
        : Point Fp).Valid := by
    rw [hacc83]
    exact Point.valid_nsmul (.inl B.onCurve) S83
  have h_final := h_add ⟨hValidP, hValidAcc⟩
  have hresult :
      ({ x := Expression.eval env
            (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 4 + 2 + 2)).x,
         y := Expression.eval env
            (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 4 + 2 + 2)).y }
        : Point Fp).coords = ((V • B.point).x, (V • B.point).y) := by
    rw [h_final.2]
    show ShortWeierstrass.add pallasA
        (({ x := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1),
            y := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1) }
          : Point Fp)).coords
        (({ x := Expression.eval env
              (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10 + 4 + 2 + 2)).x,
            y := Expression.eval env
              (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10 + 4 + 2 + 2)).y }
          : Point Fp)).coords = _
    rw [show (({ x := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1),
                 y := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1) } : Point Fp)).coords
      = (env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1),
         env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1)) from rfl,
      hpx84, hpy84, hacc83]
    show ShortWeierstrass.add pallasA ((t84 • B.point).x, (t84 • B.point).y)
        ((S83 • B.point).x, (S83 • B.point).y) = ((V • B.point).x, (V • B.point).y)
    have hpt : t84 • B.point + S83 • B.point = V • B.point := by
      rw [Point.nsmul_add_nsmul B.onCurve, ht84_def, hS83_def, ← B.add_natCast_val_nsmul, ← hks84,
        windowScalar_partialSum ks, ← hV_def, natCast_val_nsmul]
    exact FixedBase.add_coords_eq hpt
  -- running-sum cells via the floor-division telescoping
  have hz85' : zf 85 = 0 := by rw [hzf85]; exact h_z85
  have hzdiv : ∀ w, w ≤ 83 →
      env.get (zCell i₀ w) = (((∑ j ∈ Finset.range 85, ks j * 8 ^ j) / 8 ^ (w + 1) : ℕ) : Fp) := by
    intro w hw
    rw [← hzf_succ w (by omega)]
    exact chain_div zf ks hks_lt hchain hz85' (85 - (w + 1)) (w + 1) (by omega)
  -- assemble
  refine ⟨ks, fun w _ => hks_lt w, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hαV, hV_def]
  · apply Point.ext_coords; rw [← hV_def]; exact hresult
  · rw [show env.get (i₀ + 1 + 4 + 41 * 10) = env.get (zCell i₀ 42) from rfl, hzdiv 42 (by omega),
      ← hV_def]
  · rw [show env.get (i₀ + 1 + 4 + 42 * 10) = env.get (zCell i₀ 43) from rfl, hzdiv 43 (by omega),
      ← hV_def]
  · rw [show env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10) = env.get (zCell i₀ 83) from rfl,
      hzdiv 83 (by omega), ← hV_def]

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
      MulFixed.interpolatedX, hwin, B.interpolate_eq w hw _ (windowVal_lt α w)]
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
-- (`extendsVector_toIRLiteral` etc.) keep matching through stuck `size`/`localLength`
-- indices (lean4#12179).
set_option backward.isDefEq.respectTransparency false in
theorem completeness (B : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main B) ProverAssumptions
      (ProverSpec B) := by
  -- TODO: the honest-prover argument mirrors `Short.completeness` (windows assigned by
  -- `windowVal`/`rowTailValue`, accumulator invariant `accPt = [partialSum]B`, final
  -- complete addition giving `[α.val]B`, with `windowScalar_partialSum (windowVal α)` +
  -- `sum_windowVal` bridging to `α.val • B.point`). The honest-prover helper lemmas above
  -- (`word_inRange`, `coordsRow_spec`, `zValue_step`, `zValue_zero`, `zValue_85_eq_zero`,
  -- `sum_windowVal`, `env_get_rowTail`, the `rowTailValue_*` `rfl`-bridges) are in place.
  -- Remaining blocker: unlike soundness, `circuit_proof_start`/`circuit_norm` does NOT
  -- expand the *second* `Circuit.foldl`'s `UsesLocalWitnessesCompleteness` obligation
  -- (windows 44..83); it survives as a raw `env.UsesLocalWitnessesCompleteness _
  -- (Circuit.foldl (Vector.finRange 40) ...)` because the `foldl.usesLocalWitnesses`
  -- `circuit_norm ↓` lemma fails to fire on the nested-after-window-43 second segment
  -- (its `const_out`/`constant` instance arguments do not synthesize against the
  -- non-canonical accumulated offset). Expanding it by hand, plus the kernel size cliff
  -- this 85-window two-foldl completeness sits on (see `doc/performance-problems.md`,
  -- "Kernel size cliffs in completeness proofs of large compositions"), is the open work.
  circuit_proof_start [main, rowProgram, ProverSpec, ProverAssumptions,
    Utilities.RunningSum.circuit, Utilities.RunningSum.Spec,
    MulFixed.RunningSumCoords.circuit, MulFixed.RunningSumCoords.Spec,
    AddIncomplete.circuit, AddIncomplete.Spec, AddIncomplete.Assumptions,
    Add.circuit, Add.Spec, Add.Assumptions]
  simp only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub] at h_env
  rw [show (42 * 10 + (i₀ + 1 + 4) + 4 + 6 : ℕ) = i₀ + 1 + 4 + 42 * 10 + 4 + 6 from by omega]
    at h_env
  rw [Circuit.foldl.usesLocalWitnesses] at h_env
  simp only [Vector.getElem_finRange, Fin.val_mk, Nat.reduceMul, circuit_norm] at h_env
  simp only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceSub] at h_env ⊢
  obtain ⟨h_z0w, h_t0, ⟨⟨h_t1, h_inc1⟩, h_seg1_loop⟩, h_t43, h_inc43,
    ⟨⟨h_t44, h_inc44⟩, h_seg2_loop⟩, h_t84, h_add⟩ := h_env
  simp only [h_input] at h_t44 h_seg2_loop
  simp only [AddIncomplete.Assumptions, AddIncomplete.Spec] at h_inc44 h_seg2_loop
  -- bridge the witness-IR row values to the honest `rowTailValue`s, at literal windows
  replace h_t0 := h_t0.trans (rowProgram_value B input 0)
  replace h_t1 := h_t1.trans (rowProgram_value B input 1)
  replace h_t43 := h_t43.trans (rowProgram_value B input 43)
  replace h_t44 := h_t44.trans (rowProgram_value B input 44)
  replace h_t84 := h_t84.trans (rowProgram_value B input 84)
  have hα := h_assumptions
  -- per-window witnessed row values (windows `1..83`, window `j + 1`), gluing both foldl
  -- segments and the explicit window 43
  have hrow : ∀ (j : ℕ), j < 83 →
      env.get (zCell i₀ (j + 1)) = (rowTailValue B input (j + 1)).zNext ∧
        env.get (i₀ + 1 + 4 + j * 10 + 1) = (rowTailValue B input (j + 1)).xP ∧
        env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) = (rowTailValue B input (j + 1)).yP ∧
        env.get (i₀ + 1 + 4 + j * 10 + 1 + 1 + 1) = (rowTailValue B input (j + 1)).u := by
    intro j hj
    rw [show zCell i₀ (j + 1) = i₀ + 1 + 4 + j * 10 from rfl]
    rcases Nat.lt_or_ge j 1 with hj0 | hj1
    · obtain rfl : j = 0 := by omega
      exact env_get_rowTail (n := i₀ + 1 + 4 + 0 * 10) (by simpa using h_t1)
    rcases Nat.lt_or_ge j 42 with hj42 | hj42'
    · have hb := ((h_seg1_loop (j - 1) (by omega)).1).trans
        (rowProgram_value B input (j - 1 + 1 + 1))
      rw [show (j - 1 + 1) * 10 = j * 10 from by omega] at hb
      simp only [show j - 1 + 1 + 1 = j + 1 from by omega] at hb
      exact env_get_rowTail hb
    rcases Nat.lt_or_ge j 43 with hj43 | hj43'
    · have hje : (43 : ℕ) = j + 1 := by omega
      have hb := h_t43
      rw [hje, show (420 : ℕ) + (i₀ + 1 + 4) = i₀ + 1 + 4 + j * 10 from by omega] at hb
      exact env_get_rowTail hb
    rcases Nat.lt_or_ge j 44 with hj44 | hj44'
    · have hje : (44 : ℕ) = j + 1 := by omega
      have hb := h_t44
      rw [hje, show i₀ + 1 + 4 + 420 + 4 + 6 = i₀ + 1 + 4 + j * 10 from by omega] at hb
      exact env_get_rowTail hb
    · have hb := ((h_seg2_loop (j - 44) (by omega)).1).trans
        (rowProgram_value B input (j - 44 + 1 + 44))
      rw [show i₀ + 1 + 4 + 420 + 4 + 6 + (j - 44 + 1) * 10 = i₀ + 1 + 4 + j * 10 from by omega] at hb
      simp only [show j - 44 + 1 + 44 = j + 1 from by omega] at hb
      exact env_get_rowTail hb
  -- per-window AddIncomplete implication (windows `1..83`), raw OnCurve form
  have h_step' : ∀ (j : ℕ), j < 83 →
      (({ x := env.get (i₀ + 1 + 4 + j * 10 + 1),
            y := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) } : Point Fp).OnCurve ∧
          (accPt env.toEnvironment i₀ j).OnCurve ∧
          ¬env.get (i₀ + 1 + 4 + j * 10 + 1) = (accPt env.toEnvironment i₀ j).x →
        (accPt env.toEnvironment i₀ (j + 1)).OnCurve ∧
          accPt env.toEnvironment i₀ (j + 1) =
            { x := env.get (i₀ + 1 + 4 + j * 10 + 1),
              y := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) } +
              accPt env.toEnvironment i₀ j) := by
    intro j hj
    rcases Nat.lt_or_ge j 1 with hj0 | hj1
    · obtain rfl : j = 0 := by omega
      exact h_inc1
    rcases Nat.lt_or_ge j 42 with hj42 | hj42'
    · have h := (h_seg1_loop (j - 1) (by omega)).2
      rw [show j - 1 + 1 = j from by omega] at h
      rw [accPt_pos env.toEnvironment i₀ (by omega)]
      exact h
    rcases Nat.lt_or_ge j 43 with hj43 | hj43'
    · obtain rfl : j = 42 := by omega
      exact h_inc43
    rcases Nat.lt_or_ge j 44 with hj44 | hj44'
    · obtain rfl : j = 43 := by omega
      exact h_inc44
    · have h := (h_seg2_loop (j - 44) (by omega)).2
      rw [show i₀ + 1 + 4 + 420 + 4 + 6 + (j - 44 + 1) * 10 = i₀ + 1 + 4 + j * 10 from by omega,
        show i₀ + 1 + 4 + 420 + 4 + 6 + (j - 44) * 10 = i₀ + 1 + 4 + (j - 1) * 10 from by omega] at h
      rw [accPt_pos env.toEnvironment i₀ (by omega), accPt_succ]
      exact h
  -- honest window-point coordinate cells
  have hrowX : ∀ (j : ℕ) (hj : j < 83), env.get (i₀ + 1 + 4 + j * 10 + 1)
      = (MulFixed.windowPoint B.point (j + 1) (windowVal input (j + 1))).x :=
    fun j hj => (hrow j hj).2.1.trans (rowTailValue_xP B input (j + 1))
  have hrowY : ∀ (j : ℕ) (hj : j < 83), env.get (i₀ + 1 + 4 + j * 10 + 1 + 1)
      = (MulFixed.windowPoint B.point (j + 1) (windowVal input (j + 1))).y :=
    fun j hj => (hrow j hj).2.2.1.trans (rowTailValue_yP B input (j + 1))
  -- the honest accumulator after windows `0..w` is `[partialSum]B`
  have h_inv : ∀ (w : ℕ), w ≤ 83 →
      accPt env.toEnvironment i₀ w
        = { x := (MulFixed.partialSum (windowVal input) w • B.point).x,
            y := (MulFixed.partialSum (windowVal input) w • B.point).y } := by
    intro w hw
    induction w with
    | zero =>
      have hval0 : (MulFixed.windowScalar 0 (windowVal input 0)).val
          = MulFixed.partialSum (windowVal input) 0 := by
        rw [MulFixed.windowScalar_val (by norm_num) (windowVal_lt input 0), MulFixed.partialSum]
        simp
      show ({ x := env.get (i₀ + 1 + 1), y := env.get (i₀ + 1 + 1 + 1) } : Point Fp) = _
      obtain ⟨h0z, h0x, h0y, h0u⟩ := env_get_rowTail h_t0
      rw [h0x, h0y, rowTailValue_xP, rowTailValue_yP]
      unfold MulFixed.windowPoint
      rw [hval0]
    | succ j ih =>
      have hj : j < 83 := by omega
      have hacc := ih (by omega)
      set t := (MulFixed.windowScalar (j + 1) (windowVal input (j + 1))).val with ht_def
      have hval : t = (windowVal input (j + 1) + 2) * 8 ^ (j + 1) :=
        MulFixed.windowScalar_val (by omega) (windowVal_lt input (j + 1))
      have hS_lt := MulFixed.partialSum_lt (windowVal input) j fun _ _ => windowVal_lt input _
      have hS_pos := MulFixed.partialSum_pos (windowVal input) j
      have hpow : 0 < (8 : ℕ) ^ (j + 1) := pow_pos (by norm_num) _
      have ht_lower : 2 * 8 ^ (j + 1) ≤ t := by
        rw [hval]; exact Nat.mul_le_mul_right _ (by omega)
      have ht_upper : t ≤ 9 * 8 ^ (j + 1) := by
        rw [hval]; exact Nat.mul_le_mul_right _ (by have := windowVal_lt input (j + 1); omega)
      have hS_card := inv_lt_card hS_lt (by omega)
      have hsum_card := step_sum_lt hS_lt ht_upper (by omega)
      have hpx : env.get (i₀ + 1 + 4 + j * 10 + 1) = (t • B.point).x := by
        rw [hrowX j hj]; rfl
      have hpy : env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) = (t • B.point).y := by
        rw [hrowY j hj]; rfl
      have h_spec := h_step' j hj ⟨by
          rw [hpx, hpy]
          exact B.nsmul_onCurve (by omega) (by omega),
        by
          rw [hacc]
          exact B.nsmul_onCurve hS_pos hS_card,
        by
          rw [hpx, hacc]
          show (t • B.point).x ≠ (MulFixed.partialSum (windowVal input) j • B.point).x
          exact B.nsmul_x_ne hS_pos (by omega) hsum_card⟩
      rw [h_spec.2, hpx, hpy, hacc]
      rw [Point.nsmul_add_nsmul B.onCurve]
      congr 1
      rw [MulFixed.partialSum, hval]
      omega
  -- honest running-sum cells
  obtain ⟨h0z, h0x, h0y, h0u⟩ := env_get_rowTail h_t0
  have hz0cell : env.get i₀ = zValue input 0 := by rw [h_z0w, zValue_zero]
  have hzCellSucc : ∀ (j : ℕ), j < 83 → env.get (zCell i₀ (j + 1)) = zValue input (j + 2) :=
    fun j hj => (hrow j hj).1.trans (rowTailValue_zNext B input (j + 1))
  have hz1cell : env.get (i₀ + 1) = zValue input 1 :=
    h0z.trans (rowTailValue_zNext B input 0)
  -- window-84 witness cells
  rw [show (400 : ℕ) + (i₀ + 1 + 4 + 420 + 4 + 6)
    = i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 from by omega] at h_t84
  have hrow84 := env_get_rowTail h_t84
  have hw84z : env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10) = zValue input 85 :=
    hrow84.1.trans (rowTailValue_zNext B input 84)
  have hw84x : env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1)
      = (MulFixed.windowPoint B.point 84 (windowVal input 84)).x :=
    hrow84.2.1.trans (rowTailValue_xP B input 84)
  have hw84y : env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1)
      = (MulFixed.windowPoint B.point 84 (windowVal input 84)).y :=
    hrow84.2.2.1.trans (rowTailValue_yP B input 84)
  -- the final accumulator after window 83
  obtain ⟨S83, hS83_def⟩ : ∃ S : ℕ, S = MulFixed.partialSum (windowVal input) 83 := ⟨_, rfl⟩
  have hS83_lt : S83 < 2 * 8 ^ (83 + 1) := by
    rw [hS83_def]; exact MulFixed.partialSum_lt (windowVal input) 83 fun _ _ => windowVal_lt input _
  have hS83_pos : 0 < S83 := by rw [hS83_def]; exact MulFixed.partialSum_pos (windowVal input) 83
  have hS83_card := inv_lt_card hS83_lt (by omega)
  have hacc83 :
      ({ x := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10 + 4 + 2 + 2)).x,
         y := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10 + 4 + 2 + 2)).y }
        : Point Fp)
      = { x := (S83 • B.point).x, y := (S83 • B.point).y } := by
    rw [hS83_def]
    have := h_inv 83 (by omega)
    rw [accPt_succ] at this
    convert this using 4
  -- window-84 point opaque
  obtain ⟨t84, ht84_def⟩ : ∃ t : ℕ, t = (MulFixed.windowScalar 84 (windowVal input 84)).val := ⟨_, rfl⟩
  have hpx84 : env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1) = (t84 • B.point).x := by
    rw [hw84x, ht84_def]; rfl
  have hpy84 : env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1) = (t84 • B.point).y := by
    rw [hw84y, ht84_def]; rfl
  have hValidP :
      ({ x := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1),
         y := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1) } :
        Point Fp).Valid := by
    rw [hpx84, hpy84]
    exact Point.valid_nsmul (.inl B.onCurve) t84
  have hValidAcc :
      ({ x := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10 + 4 + 2 + 2)).x,
          y := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10 + 4 + 2 + 2)).y }
        : Point Fp).Valid := by
    rw [hacc83]
    exact Point.valid_nsmul (.inl B.onCurve) S83
  -- per-window constraint obligations (windows `1..83`)
  have hB : ∀ (j : ℕ), j < 83 →
      Utilities.RunningSum.InRange (2 ^ 3) (Utilities.RunningSum.word 3
        { zCur := env.get (zCell i₀ j), zNext := env.get (zCell i₀ (j + 1)) }) ∧
      Coords.Spec (B.params (j + 1)) (MulFixed.RunningSumCoords.coordsRow
        { zCur := env.get (zCell i₀ j), zNext := env.get (zCell i₀ (j + 1)),
          xP := env.get (i₀ + 1 + 4 + j * 10 + 1),
          yP := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1),
          u := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1 + 1) }) ∧
      ({ x := env.get (i₀ + 1 + 4 + j * 10 + 1),
         y := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) } : Point Fp).OnCurve ∧
      (accPt env.toEnvironment i₀ j).OnCurve ∧
      ¬env.get (i₀ + 1 + 4 + j * 10 + 1) = (accPt env.toEnvironment i₀ j).x := by
    intro j hj
    have hzc : env.get (zCell i₀ j) = zValue input (j + 1) := by
      rcases Nat.eq_zero_or_pos j with rfl | hjp
      · exact hz1cell
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        exact hzCellSucc j' (by omega)
    have hzn : env.get (zCell i₀ (j + 1)) = zValue input (j + 1 + 1) := hzCellSucc j hj
    have hacc := h_inv j (by omega)
    have hS_lt := MulFixed.partialSum_lt (windowVal input) j fun _ _ => windowVal_lt input _
    have hS_pos := MulFixed.partialSum_pos (windowVal input) j
    have hS_card := inv_lt_card hS_lt (by omega)
    set t := (MulFixed.windowScalar (j + 1) (windowVal input (j + 1))).val with ht_def
    have hval : t = (windowVal input (j + 1) + 2) * 8 ^ (j + 1) :=
      MulFixed.windowScalar_val (by omega) (windowVal_lt input (j + 1))
    have ht_lower : 2 * 8 ^ (j + 1) ≤ t := by rw [hval]; exact Nat.mul_le_mul_right _ (by omega)
    have ht_upper : t ≤ 9 * 8 ^ (j + 1) := by
      rw [hval]; exact Nat.mul_le_mul_right _ (by have := windowVal_lt input (j + 1); omega)
    have hpow : 0 < (8 : ℕ) ^ (j + 1) := pow_pos (by norm_num) _
    have hsum_card := step_sum_lt hS_lt ht_upper (by omega)
    have hpx : env.get (i₀ + 1 + 4 + j * 10 + 1) = (t • B.point).x := by rw [hrowX j hj]; rfl
    have hpy : env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) = (t • B.point).y := by rw [hrowY j hj]; rfl
    refine ⟨word_inRange input (j + 1) hzc hzn, ?_, ?_, ?_, ?_⟩
    · refine coordsRow_spec B input (by omega) hzc hzn ?_ ?_ ?_
      · rw [hrowX j hj]
      · rw [hrowY j hj]
      · exact (hrow j hj).2.2.2.trans (rowTailValue_u B input (j + 1))
    · rw [hpx, hpy]
      exact B.nsmul_onCurve (by omega) (by omega)
    · rw [hacc]
      exact B.nsmul_onCurve hS_pos hS_card
    · rw [hpx, hacc]
      show (t • B.point).x ≠ (MulFixed.partialSum (windowVal input) j • B.point).x
      exact B.nsmul_x_ne hS_pos (by omega) hsum_card
  -- the complete addition produces `[input.val]B`
  have h_final := h_add ⟨hValidP, hValidAcc⟩
  have hresult :
      ({ x := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 4 + 2 + 2)).x,
         y := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 4 + 2 + 2)).y }
        : Point Fp).coords
        = (((show Fp from input).val • B.point).x, ((show Fp from input).val • B.point).y) := by
    rw [h_final.2]
    show ShortWeierstrass.add pallasA
        (({ x := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1),
            y := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1) }
          : Point Fp)).coords
        (({ x := Expression.eval env.toEnvironment
              (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10 + 4 + 2 + 2)).x,
            y := Expression.eval env.toEnvironment
              (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10 + 4 + 2 + 2)).y }
          : Point Fp)).coords = _
    rw [show (({ x := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1),
                 y := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1) } :
            Point Fp)).coords
      = (env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1),
         env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1)) from rfl,
      hpx84, hpy84, hacc83]
    show ShortWeierstrass.add pallasA ((t84 • B.point).x, (t84 • B.point).y)
        ((S83 • B.point).x, (S83 • B.point).y)
      = (((show Fp from input).val • B.point).x, ((show Fp from input).val • B.point).y)
    have hpt : t84 • B.point + S83 • B.point = (show Fp from input).val • B.point := by
      rw [Point.nsmul_add_nsmul B.onCurve, ht84_def, hS83_def, ← B.add_natCast_val_nsmul,
        windowScalar_partialSum (windowVal input),
        sum_windowVal (α := (show Fp from input)) hα, natCast_val_nsmul]
    exact FixedBase.add_coords_eq hpt
  -- the running-sum cells, honest values
  have hz43 : env.get (i₀ + 1 + 4 + 41 * 10) = zValue input 43 := hzCellSucc 41 (by omega)
  have hz44 : env.get (i₀ + 1 + 4 + 42 * 10) = zValue input 44 := hzCellSucc 42 (by omega)
  have hz84 : env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10) = zValue input 84 := by
    have := hzCellSucc 82 (by omega)
    rw [show zCell i₀ (82 + 1) = i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10 from rfl] at this
    exact this
  -- window-0 constraints
  have hz0InRange : Utilities.RunningSum.InRange (2 ^ 3) (Utilities.RunningSum.word 3
      { zCur := env.get i₀, zNext := env.get (i₀ + 1) }) :=
    word_inRange input 0 hz0cell hz1cell
  have hz0Coords : Coords.Spec (B.params 0) (MulFixed.RunningSumCoords.coordsRow
      { zCur := env.get i₀, zNext := env.get (i₀ + 1), xP := env.get (i₀ + 1 + 1),
        yP := env.get (i₀ + 1 + 1 + 1), u := env.get (i₀ + 1 + 1 + 1 + 1) }) :=
    coordsRow_spec B input (by norm_num) hz0cell hz1cell
      (h0x.trans (rowTailValue_xP B input 0)) (h0y.trans (rowTailValue_yP B input 0))
      (h0u.trans (rowTailValue_u B input 0))
  -- window-84 constraints
  have hw84z' : env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10) = zValue input 85 := hw84z
  have hzc84 : env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10) = zValue input 84 := hz84
  have hw84u : env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1 + 1)
      = B.u 84 (windowVal input 84) :=
    hrow84.2.2.2.trans (rowTailValue_u B input 84)
  have hw84InRange : Utilities.RunningSum.InRange (2 ^ 3) (Utilities.RunningSum.word 3
      { zCur := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10),
        zNext := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10) }) :=
    word_inRange input 84 hzc84 hw84z'
  have hw84Coords : Coords.Spec (B.params 84) (MulFixed.RunningSumCoords.coordsRow
      { zCur := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 39 * 10),
        zNext := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10),
        xP := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1),
        yP := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1),
        u := env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10 + 1 + 1 + 1) }) :=
    coordsRow_spec B input (by norm_num) hzc84 hw84z' hw84x hw84y hw84u
  -- the strict running sum terminates at zero
  have hz85zero : env.get (i₀ + 1 + 4 + 42 * 10 + 4 + 6 + 40 * 10) = 0 := by
    rw [hw84z']; exact zValue_85_eq_zero hα
  -- assemble: window 0, the two foldl segments (via `hB`), windows 43/44/84, the strict
  -- check, the final addition, and the prover spec
  -- converted (raw-offset) window-43 and window-44 obligations
  have hB42 := hB 42 (by omega)
  rw [show zCell i₀ 42 = i₀ + 1 + 4 + 41 * 10 from rfl,
    show zCell i₀ (42 + 1) = i₀ + 1 + 4 + 42 * 10 from rfl,
    show accPt env.toEnvironment i₀ 42
      = { x := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 41 * 10 + 4 + 2 + 2)).x,
          y := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 41 * 10 + 4 + 2 + 2)).y } from
      accPt_succ env.toEnvironment i₀ 41] at hB42
  have hB43 := hB 43 (by omega)
  rw [show zCell i₀ 43 = i₀ + 1 + 4 + 42 * 10 from rfl,
    show zCell i₀ (43 + 1) = i₀ + 1 + 4 + 42 * 10 + 4 + 6 from rfl,
    show accPt env.toEnvironment i₀ 43
      = { x := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 2 + 2)).x,
          y := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 42 * 10 + 4 + 2 + 2)).y } from
      accPt_succ env.toEnvironment i₀ 42] at hB43
  refine ⟨?_, ?_, hz43, hz44, hz84⟩
  swap
  · apply Point.ext_coords
    rw [B.smul_coords, RunningSumMul.natCast_val_nsmul]
    simp only [Point.coords] at hresult ⊢
    exact hresult
  refine ⟨h_z0w, hz0InRange, hz0Coords, ⟨hB 0 (by omega), ?_⟩, hB42.1, hB42.2.1, hB42.2.2,
    ⟨hB43, ?_⟩, hw84InRange, hw84Coords, hz85zero, hValidP, hValidAcc⟩
  -- foldl1 (windows 2..42)
  · intro i hi
    have h := hB (i + 1) (by omega)
    rw [zCell_pos i₀ (by omega), zCell_succ, accPt_pos env.toEnvironment i₀ (by omega)] at h
    convert h using 6
  -- foldl2 (windows 45..83)
  · intro i hi
    have h := hB (i + 44) (by omega)
    rw [zCell_pos i₀ (by omega), zCell_succ, accPt_pos env.toEnvironment i₀ (by omega)] at h
    simpa +arith using h

/-- The decomposition + windowed-multiplication regions of
`base_field_elem.rs::Config::assign`. -/
def circuit (B : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint Fp field Output where
  main := main B
  elaborated := elaborated B
  Spec := Spec B
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec B
  soundness := soundness B
  completeness := completeness B
  requirementsChannelsLawful input offset := by
    and_intros
    · dsimp only [main, Utilities.RunningSum.circuit, MulFixed.RunningSumCoords.circuit,
        AddIncomplete.circuit, Add.circuit]
      simp only [circuit_norm]
    · -- TODO this proof is super ugly to avoid kernel recursion
      intro channel h_mem
      dsimp only [main, CircuitType.var_of_provableType, Circuit.pure_def,
        Circuit.bind_def, assertion.eq_1, List.cons_append, List.nil_append,
        List.map_cons, List.map_nil, subcircuit.eq_1,
        Operations.localLength.eq_6, FormalAssertion.toSubcircuit_localLength,
        Circuit.operations,
        Operations.shallowChannels_witness, Operations.shallowChannels_subcircuit] at h_mem
      simp only [Operations.shallowChannels_append,
        ↓Circuit.foldl.shallowChannels, Circuit.operations,
        Operations.shallowChannels_subcircuit, Operations.shallowChannels_nil] at h_mem
      nomatch h_mem
    · intro env _
      simp only [main, circuit_norm]

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

def main (B : MulFixed.FixedBase) (alpha : Var field Fp) :
    Circuit Fp (Var Point Fp) := do
  -- region 1+2: strict running-sum decomposition, windowed mul, complete addition
  let m ← RunningSumMul.circuit B alpha
  -- region 3: canonicity of the base-field element.
  -- α_0 = α - z_84 · 2^252, the low 252 bits.
  -- α_0_prime = α_0 + 2^130 - t_p; 13 ten-bit lookups give z_13_alpha_0_prime.
  let alpha0Prime ← witness <|
    (Witgen.FExpr.expr alpha - Witgen.FExpr.expr m.z84 * Witgen.FExpr.const (2 ^ 252 : Fp))
      + Witgen.FExpr.const (2 ^ 130 : Fp) - Witgen.FExpr.const (tPNat : Fp)
  let zsDecomp ← Utilities.LookupRangeCheck.CopyCheck.circuit 13 alpha0Prime
  let z13Alpha0Prime := zsDecomp[13]
  -- the 2-bit / 1-bit pieces of the top window, and the canonicity gate
  let alpha1 ← witness (m.z84.val % (4 : ℕ)).toField
  let alpha2 ← witness (m.z84.val / (4 : ℕ)).toField
  let z84Alpha <== m.z84
  let z44Alpha <== m.z44
  let z43Alpha <== m.z43
  Gate.circuit {
    alpha := alpha, z84Alpha := z84Alpha, alpha1 := alpha1, alpha2 := alpha2,
    alpha0Prime := alpha0Prime, z13Alpha0Prime := z13Alpha0Prime,
    z44Alpha := z44Alpha, z43Alpha := z43Alpha }
  return m.result

instance elaborated (B : MulFixed.FixedBase) :
    ElaboratedCircuit Fp field Point (main B) := by
  elaborate_circuit

/-- Preconditions: `α` is a canonical base-field element (always true for an actual
`Fp` cell — `α.val < p` by definition). -/
def Assumptions (_ : Fp) : Prop := True

/-- The circuit computes `[α]·B`, the fixed-base multiplication of `B` by the base-field
element `α` (reinterpreted as the scalar `α.val`, which is `< p < q`). -/
def Spec (B : MulFixed.FixedBase) (alpha : Fp) (output : Point Fp) : Prop :=
  output = (alpha.val : Fq) • B

/-- `p = 2^254 + t_p` for the Pallas base field. -/
private theorem base_card_eq : PALLAS_BASE_CARD = 2 ^ 254 + tPNat := by
  norm_num [PALLAS_BASE_CARD, tPNat]

/-- From the lookup digit sum `S < 2^130` and the field equation `S = α0 + 2^130 - t_p`
(with `α0 < 2^132` ruling out wraparound), conclude `α0 < t_p`. Factored so the heavy
`ZMod.val` reasoning is kernel-checked in isolation. -/
private theorem alpha0_lt_tp {S α0 : ℕ} (hSlt : S < 2 ^ 130) (hα0lt : α0 < 2 ^ 132)
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
private theorem honest_canon_spec {row : Input Fp} {α : Fp}
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

theorem soundness (B : MulFixed.FixedBase) :
    Soundness Fp (main B) Assumptions (Spec B) := by
  circuit_proof_start [main, Spec, RunningSumMul.circuit, Gate.circuit,
    Gate.Spec, Utilities.LookupRangeCheck.CopyCheck.circuit]
  obtain ⟨hRSM, hCopy, hz84eq, hz44eq, hz43eq, hGate⟩ := h_holds
  -- the windowed-mul spec: the decomposed value `V`, with `α = (V : Fp)`
  obtain ⟨ks, hks_lt, hαV, hresPt, hz43V, hz44V, hz84V⟩ := hRSM
  set V := ∑ j ∈ Finset.range 85, ks j * 8 ^ j with hV
  -- the canonicity gate facts
  simp only [Gate.IsAlpha1, Gate.DecomposesBaseFieldElem,
    Gate.CanonicalHighBit, Gate.alpha0, Gate.alpha0Hi120,
    Gate.a43, IsBool] at hGate
  obtain ⟨hAlpha1, hAlpha2, ⟨hz84dec, hα0prime⟩, hCanon⟩ := hGate
  -- bound on the decomposed value: it fits in 85 windows
  have hVlt : V < 8 ^ 85 := RunningSumMul.sum_lt_of_windows fun j hj => hks_lt j hj
  -- the top window value `A0 = V / 8^84 = ks 84 < 8`, with `V = α0 + A0·2^252`
  set A0 : ℕ := V / 8 ^ 84 with hA0
  have hA0lt : A0 < 8 := by
    rw [hA0]; rw [show (8 : ℕ) ^ 85 = 8 ^ 84 * 8 from by ring] at hVlt
    exact Nat.div_lt_of_lt_mul (by omega)
  set α0 : ℕ := V % 8 ^ 84 with hα0def
  have hα0lt : α0 < 2 ^ 252 := by
    rw [hα0def]; exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by norm_num)
  have hVsplit : V = α0 + A0 * 8 ^ 84 := by
    rw [hα0def, hA0]; omega
  -- gate cells, via the copy equalities, in terms of `V`
  have e84 : env.get _ = ((V / 8 ^ 84 : ℕ) : Fp) := hz84eq.trans hz84V
  have e44 : env.get _ = ((V / 8 ^ 44 : ℕ) : Fp) := hz44eq.trans hz44V
  have e43 : env.get _ = ((V / 8 ^ 43 : ℕ) : Fp) := hz43eq.trans hz43V
  -- `α2` and `α1` as naturals: `A0 = a1 + 4·a2`
  rw [e84, ← hA0] at hz84dec
  -- the crux: the decomposed value is the canonical representative `α.val`
  have h884 : (8 : ℕ) ^ 84 = 2 ^ 252 := by norm_num
  have hVltp : V < PALLAS_BASE_CARD := by
    rw [base_card_eq]
    rcases hAlpha2 with ha2 | ha2
    · -- α2 = 0: the top window is ≤ 3, so V < 2^254
      rw [ha2, zero_mul, _root_.add_zero] at hz84dec
      have hA0le : A0 ≤ 3 := by
        rcases hAlpha1 with h | h | h | h <;> rw [h] at hz84dec
        · have : A0 = 0 :=
            RunningSumMul.natCast_inj_of_lt_8 hA0lt (by norm_num) (by rw [hz84dec]; norm_num)
          omega
        · have : A0 = 1 :=
            RunningSumMul.natCast_inj_of_lt_8 hA0lt (by norm_num) (by rw [hz84dec]; norm_num)
          omega
        · have : A0 = 2 :=
            RunningSumMul.natCast_inj_of_lt_8 hA0lt (by norm_num) (by rw [hz84dec]; norm_num)
          omega
        · have : A0 = 3 :=
            RunningSumMul.natCast_inj_of_lt_8 hA0lt (by norm_num) (by rw [hz84dec]; norm_num)
          omega
      have hmul : A0 * 8 ^ 84 ≤ 3 * 2 ^ 252 := by
        rw [h884]; exact Nat.mul_le_mul_right _ hA0le
      rw [hVsplit]
      norm_num [tPNat] at hα0lt ⊢
      omega
    · -- α2 = 1: canonicity forces α0 < t_p
      obtain ⟨hα1z, hhi120, _, hz13⟩ := hCanon ha2
      -- the top window is `4` (α1 = 0, α2 = 1)
      rw [hα1z, ha2] at hz84dec
      have hA04 : A0 = 4 :=
        RunningSumMul.natCast_inj_of_lt_8 hA0lt (by norm_num) (by rw [hz84dec]; norm_num)
      have hV254 : V = α0 + 2 ^ 254 := by rw [hVsplit, hA04, h884]; norm_num
      have hz84val : V / 8 ^ 84 = 4 := hA04
      -- `alpha0_hi_120 = 0` forces `α0 < 2^132`
      have h844 : (8 : ℕ) ^ 44 = 2 ^ 132 := by norm_num
      have hdiv44 : V / 8 ^ 44 = α0 / 2 ^ 132 + 2 ^ 122 := by
        rw [hV254, h844, show (2 : ℕ) ^ 254 = 2 ^ 122 * 2 ^ 132 from by ring,
          Nat.add_mul_div_right _ _ (by positivity)]
      rw [e44, e84, hz84val, hdiv44,
        show (OfNat.ofNat (2 ^ 120) : Fp) = (2 : Fp) ^ 120 from by norm_num] at hhi120
      have hq0 : α0 / 2 ^ 132 = 0 := by
        have hcast : ((α0 / 2 ^ 132 : ℕ) : Fp) = 0 := by
          push_cast at hhi120 ⊢; linear_combination hhi120
        have hlt : α0 / 2 ^ 132 < PALLAS_BASE_CARD := by
          have : α0 / 2 ^ 132 < 2 ^ 120 :=
            Nat.div_lt_of_lt_mul (by rw [show 2 ^ 132 * 2 ^ 120 = 2 ^ 252 from by ring]; omega)
          rw [base_card_eq]; omega
        exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ _).mp hcast) hlt
      have hα0lt132 : α0 < 2 ^ 132 := by
        rcases Nat.div_eq_zero_iff.mp hq0 with h | h
        · norm_num at h
        · exact h
      -- The 13-window lookup on `α_0_prime` forces `α0 < t_p`.
      --
      -- `hα0prime : α_0_prime = α0 + 2^130 - t_p` (after the rewrites below), and the
      -- lookup (`hCopy`) telescopes (via `CopyCheck.spec_telescope`, which is stated over
      -- an abstract `ℕ → Fp` function and so sidesteps the kernel/whnf cliff on the
      -- concrete getElem chain, see `doc/performance-problems.md`) from `z_0 = α_0_prime`
      -- to `z_13 = 0` (`hz13`), giving `α_0_prime = ↑lo` for some `lo < 2^130` (the
      -- 130-bit digit sum). Since `α0 < 2^132` (`hα0lt132`), the value
      -- `α0 + 2^130 - t_p < p` does not wrap, so `lo = α0 + 2^130 - t_p < 2^130`,
      -- i.e. `α0 < t_p`.
      rw [hαV, e84, hz84val,
        show (V : Fp) = (α0 : Fp) + (4 : ℕ) * OfNat.ofNat (2 ^ 252) from by
          rw [hV254]; push_cast; ring] at hα0prime
      obtain ⟨lo, hlo, htel⟩ := Utilities.LookupRangeCheck.CopyCheck.spec_telescope hCopy 13 le_rfl
      rw [hCopy.1] at htel
      simp only [Vector.getElem_map, Vector.getElem_cast] at htel
      rw [hz13, mul_zero, _root_.add_zero] at htel
      have hK13 : Orchard.Specs.K * 13 = 130 := by norm_num [Orchard.Specs.K]
      rw [hK13] at hlo
      have hfield : (lo : Fp) = (α0 : Fp) + (2 : Fp) ^ 130 - (tPNat : Fp) := by
        rw [← htel, hα0prime]
        push_cast [tP, tPNat]
        ring
      have hα0tp : α0 < tPNat := alpha0_lt_tp hlo hα0lt132 hfield
      rw [hV254]; omega
  have hVcanon : V = ZMod.val (show Fp from input) := by
    rw [hαV, ZMod.val_natCast, Nat.mod_eq_of_lt hVltp]
  -- hence the output is `[α.val]·B`
  refine hresPt.trans ?_
  apply Point.ext_coords
  rw [B.smul_coords, RunningSumMul.natCast_val_nsmul, hVcanon]
  rfl

theorem completeness (B : MulFixed.FixedBase) :
    Completeness Fp (main B) Assumptions := by
  circuit_proof_start [main, Assumptions, RunningSumMul.circuit,
    RunningSumMul.ProverSpec, Utilities.LookupRangeCheck.CopyCheck.circuit,
    Utilities.LookupRangeCheck.CopyCheck.ProverSpec, Gate.circuit,
    Gate.Spec]
  obtain ⟨hRSM, hap0, hCC, ha1, ha2, hz84c, hz44c, hz43c⟩ := h_env
  have hpa : RunningSumMul.ProverAssumptions input env.data env.hint := by
    unfold RunningSumMul.ProverAssumptions; exact ZMod.val_lt (show Fp from input)
  obtain ⟨-, -, hz43v, hz44v, hz84v⟩ := hRSM hpa
  -- the honest running-sum cells `m.z84 = ↑(α.val / 8^84)`, etc.
  simp only [RunningSumMul.zValue] at hz84v hz44v hz43v
  have hp8 : 8 < PALLAS_BASE_CARD := by norm_num [PALLAS_BASE_CARD]
  have hvlt : (show Fp from input).val < 8 ^ 85 :=
    lt_of_lt_of_le (ZMod.val_lt _) (by norm_num [PALLAS_BASE_CARD])
  have hd8 : (show Fp from input).val / 8 ^ 84 < 8 :=
    Nat.div_lt_of_lt_mul (by rw [show (8 : ℕ) ^ 84 * 8 = 8 ^ 85 from by ring]; exact hvlt)
  -- the honest top window `d = α.val / 8^84 < 8`, used in `α1`, `α2`, `α0'`
  rw [hz84v] at ha1 ha2 hap0
  rw [ZMod.val_natCast_of_lt (lt_trans hd8 hp8)] at ha1 ha2
  refine ⟨hpa, hz84c, hz44c, hz43c, ?_, ?_, ?_⟩
  · -- IsAlpha1 α1
    rw [ha1]
    have : (show Fp from input).val / 8 ^ 84 % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases h : (show Fp from input).val / 8 ^ 84 % 4 <;>
      simp [Gate.IsAlpha1]
  · -- IsBool α2
    rw [ha2]
    have hd4 : (show Fp from input).val / 8 ^ 84 / 4 < 2 := by omega
    interval_cases h : (show Fp from input).val / 8 ^ 84 / 4 <;> simp [IsBool]
  · -- DecomposesBaseFieldElem ∧ CanonicalHighBit, via the abstract-row lemma (keeps the
    -- giant `m.z84` foldl out of the def-unfolding whnf).
    refine honest_canon_spec (α := input) hpa rfl (hz84c.trans hz84v) ha1 ha2 hap0
      (hz44c.trans hz44v) (hz43c.trans hz43v) ?_
    -- z13 = ↑(α0'.val / 2¹³⁰), from the 13-window lookup running sum. Bind first so the
    -- lookup spec elaborates at its own (small) type, then close by defeq against the row.
    have h13 := hCC.2 13
    -- rewrite the `Fin 14` index to the `ℕ` literal `13` syntactically, so the match with
    -- the row's `z13Alpha0Prime := …[13]` is by projection rather than a costly defeq that
    -- reduces the running-sum vector index.
    dsimp only [] at h13 ⊢
    exact h13

/-- `base_field_elem.rs::Config::assign` (`FixedPointBaseField::mul`): base-field-element
fixed-base scalar multiplication `[α]B`. -/
def circuit (B : MulFixed.FixedBase) : FormalCircuit Fp field Point where
  main := main B
  elaborated := elaborated B
  Assumptions := Assumptions
  Spec := Spec B
  soundness := soundness B
  completeness := completeness B

end Orchard.Ecc.MulFixed.BaseFieldElem
