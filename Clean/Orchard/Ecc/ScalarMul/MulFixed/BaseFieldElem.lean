import Clean.Orchard.Ecc.ScalarMul.MulFixed
import Clean.Orchard.Ecc.AddIncomplete
import Clean.Orchard.Ecc.Add
import Clean.Orchard.Utilities

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul_fixed/base_field_elem.rs`.

`circuit` (`Canonicity checks` namespace below) is the custom gate enabled on the
canonicity-check rows. `Assign.circuit` is the source-level entry point
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

namespace Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem

structure Row (F : Type) where
  alpha : F
  z84Alpha : F
  alpha1 : F
  alpha2 : F
  alpha0Prime : F
  z13Alpha0Prime : F
  z44Alpha : F
  z43Alpha : F
deriving ProvableStruct

def alpha0 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 252)] (row : Row K) : K :=
  row.alpha - row.z84Alpha * OfNat.ofNat (2 ^ 252)

def alpha1RangeCheck {K : Type} [One K] [Sub K] [Mul K] [OfNat K 2] [OfNat K 3]
    (row : Row K) : K :=
  row.alpha1 * (1 - row.alpha1) * (2 - row.alpha1) * (3 - row.alpha1)

def z84AlphaCheck {K : Type} [Add K] [Sub K] [Mul K] [OfNat K 4] (row : Row K) : K :=
  row.z84Alpha - (row.alpha1 + row.alpha2 * 4)

def alpha0PrimeCheck {K : Type} [Add K] [Sub K] [Mul K]
    [OfNat K (2 ^ 130)] [OfNat K (2 ^ 252)]
    [OfNat K 45560315531419706090280762371685220353] (row : Row K) : K :=
  row.alpha0Prime - (alpha0 row + OfNat.ofNat (2 ^ 130) - NoteCommit.tP)

def alpha0Hi120 {K : Type} [Sub K] [Mul K] [OfNat K (2 ^ 120)] (row : Row K) : K :=
  row.z44Alpha - row.z84Alpha * OfNat.ofNat (2 ^ 120)

def a43 {K : Type} [Sub K] [Mul K] [OfNat K 8] (row : Row K) : K :=
  row.z43Alpha - row.z44Alpha * 8

def IsAlpha1 (alpha1 : Fp) : Prop :=
  alpha1 = 0 ∨ alpha1 = 1 ∨ alpha1 = 2 ∨ alpha1 = 3

def DecomposesBaseFieldElem (row : Row Fp) : Prop :=
  row.z84Alpha = row.alpha1 + row.alpha2 * 4 ∧
    row.alpha0Prime = alpha0 row + OfNat.ofNat (2 ^ 130) - NoteCommit.tP

def CanonicalHighBit (row : Row Fp) : Prop :=
  row.alpha2 = 1 →
    row.alpha1 = 0 ∧ alpha0Hi120 row = 0 ∧ IsBool (a43 row) ∧ row.z13Alpha0Prime = 0

def Spec (row : Row Fp) : Prop :=
  IsAlpha1 row.alpha1 ∧ IsBool row.alpha2 ∧ DecomposesBaseFieldElem row ∧
    CanonicalHighBit row

def main (row : Var Row Fp) : Circuit Fp Unit := do
  assertZero (row.alpha2 * row.alpha1)
  assertZero (row.alpha2 * alpha0Hi120 row)
  assertZero (row.alpha2 * NoteCommit.boolPoly (a43 row))
  assertZero (row.alpha2 * row.z13Alpha0Prime)
  assertZero (alpha1RangeCheck row)
  assertZero (NoteCommit.boolPoly row.alpha2)
  assertZero (z84AlphaCheck row)
  assertZero (alpha0PrimeCheck row)

def circuit : FormalAssertion Fp Row where
  name := "GATE Canonicity checks"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, IsAlpha1, DecomposesBaseFieldElem,
      CanonicalHighBit, alpha0, alpha1RangeCheck, z84AlphaCheck, alpha0PrimeCheck,
      alpha0Hi120, a43, NoteCommit.boolPoly, NoteCommit.tP]
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
    · rcases mul_eq_zero.mp hAlpha2Bool with h0 | h1
      · exact Or.inl h0
      · exact Or.inr (by linear_combination h1)
    · constructor
      · exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hZ84)
      · exact sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hAlpha0Prime)
    · intro hAlpha2
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hAlpha2] at hAlpha21
        simpa using hAlpha21
      · rw [hAlpha2] at hAlpha2Hi
        simpa [sub_eq_add_neg] using hAlpha2Hi
      · have hA43Poly : NoteCommit.boolPoly (input_z43Alpha - input_z44Alpha * 8) = 0 := by
          have hMul :
              input_alpha2 * NoteCommit.boolPoly (input_z43Alpha - input_z44Alpha * 8) = 0 := by
            simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hAlpha2A43
          rw [hAlpha2] at hMul
          simpa using hMul
        exact isBool_of_boolPoly_eq_zero hA43Poly
      · rw [hAlpha2] at hAlpha2Z13
        simpa using hAlpha2Z13
  completeness := by
    circuit_proof_start [main, Spec, IsAlpha1, DecomposesBaseFieldElem,
      CanonicalHighBit, alpha0, alpha1RangeCheck, z84AlphaCheck, alpha0PrimeCheck,
      alpha0Hi120, a43, NoteCommit.boolPoly, NoteCommit.tP]
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
          have hBoolA43 := boolPoly_eq_zero_of_isBool (hCanon h1).2.2.1
          rw [h1]
          simpa [NoteCommit.boolPoly, sub_eq_add_neg] using hBoolA43
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
    · rcases hAlpha2 with h0 | h1
      · rw [h0]
        ring
      · rw [h1]
        ring
    · rw [hZ84]
      ring
    · rw [hAlpha0Prime]
      ring

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
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
  result : Ecc.Point F
  z43 : F
  z44 : F
  z84 : F
deriving ProvableStruct

def main (B : MulFixed.FixedBase) (alpha : Var field Fp) :
    Circuit Fp (Var Output Fp) := do
  -- `copy_decompose`: `z_0` is a copy of `α`
  let z₀ <== alpha
  -- window 0 initializes the accumulator
  let t₀ : Var RowTail Fp ← witness fun env => rowTailValue B (env alpha) 0
  Utilities.RunningSum.circuit 3 { zCur := z₀, zNext := t₀.zNext }
  MulFixed.RunningSumCoords.circuit (B.params 0)
    { zCur := z₀, zNext := t₀.zNext, xP := t₀.xP, yP := t₀.yP, u := t₀.u }
  let acc₀ : Var Ecc.Point Fp := { x := t₀.xP, y := t₀.yP }
  -- windows 1..42 are added with incomplete addition; final `zCur = z_43`
  let (acc₄₂, z₄₃) ← Circuit.foldlRange 42 (acc₀, t₀.zNext) fun (acc, zCur) i => do
    let t : Var RowTail Fp ← witness fun env => rowTailValue B (env alpha) (i.val + 1)
    Utilities.RunningSum.circuit 3 { zCur := zCur, zNext := t.zNext }
    MulFixed.RunningSumCoords.circuit (B.params (i.val + 1))
      { zCur := zCur, zNext := t.zNext, xP := t.xP, yP := t.yP, u := t.u }
    let acc' ← Ecc.AddIncomplete.circuit { p := { x := t.xP, y := t.yP }, q := acc }
    return (acc', t.zNext)
  -- explicit window 43; `t₄₃.zNext = z_44`
  let t₄₃ : Var RowTail Fp ← witness fun env => rowTailValue B (env alpha) 43
  Utilities.RunningSum.circuit 3 { zCur := z₄₃, zNext := t₄₃.zNext }
  MulFixed.RunningSumCoords.circuit (B.params 43)
    { zCur := z₄₃, zNext := t₄₃.zNext, xP := t₄₃.xP, yP := t₄₃.yP, u := t₄₃.u }
  let acc₄₃ ← Ecc.AddIncomplete.circuit { p := { x := t₄₃.xP, y := t₄₃.yP }, q := acc₄₂ }
  -- windows 44..83 are added with incomplete addition; final `zCur = z_84`
  let (acc₈₃, z₈₄) ← Circuit.foldlRange 40 (acc₄₃, t₄₃.zNext) fun (acc, zCur) i => do
    let t : Var RowTail Fp ← witness fun env => rowTailValue B (env alpha) (i.val + 44)
    Utilities.RunningSum.circuit 3 { zCur := zCur, zNext := t.zNext }
    MulFixed.RunningSumCoords.circuit (B.params (i.val + 44))
      { zCur := zCur, zNext := t.zNext, xP := t.xP, yP := t.yP, u := t.u }
    let acc' ← Ecc.AddIncomplete.circuit { p := { x := t.xP, y := t.yP }, q := acc }
    return (acc', t.zNext)
  -- most significant window 84
  let t₈₄ : Var RowTail Fp ← witness fun env => rowTailValue B (env alpha) 84
  Utilities.RunningSum.circuit 3 { zCur := z₈₄, zNext := t₈₄.zNext }
  MulFixed.RunningSumCoords.circuit (B.params 84)
    { zCur := z₈₄, zNext := t₈₄.zNext, xP := t₈₄.xP, yP := t₈₄.yP, u := t₈₄.u }
  -- strict decomposition: the final running sum value is zero
  t₈₄.zNext === (0 : Expression Fp)
  -- `[α]B` by complete addition of the most significant window
  let result ← Ecc.Add.circuit { p := { x := t₈₄.xP, y := t₈₄.yP }, q := acc₈₃ }
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
    output.result.coords = ((V • B.point).x, (V • B.point).y) ∧
    output.z43 = ((V / 8 ^ 43 : ℕ) : Fp) ∧
    output.z44 = ((V / 8 ^ 44 : ℕ) : Fp) ∧
    output.z84 = ((V / 8 ^ 84 : ℕ) : Fp)

def ProverAssumptions (alpha : Fp) (_ : ProverData Fp) (_ : ProverHint Fp) : Prop :=
  alpha.val < PALLAS_BASE_CARD

def ProverSpec (B : MulFixed.FixedBase) (alpha : Fp) (output : Output Fp)
    (_ : ProverHint Fp) : Prop :=
  output.result.coords = ((alpha.val • B.point).x, (alpha.val • B.point).y) ∧
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

theorem soundness (B : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Soundness Fp (main B) (fun _ _ => True) (Spec B) := by
  sorry

theorem completeness (B : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint.Completeness Fp (main B) ProverAssumptions
      (ProverSpec B) := by
  sorry

/-- The decomposition + windowed-multiplication regions of
`base_field_elem.rs::Config::assign`. -/
def circuit (B : MulFixed.FixedBase) :
    GeneralFormalCircuit.WithHint Fp field Output where
  main := main B
  Spec := Spec B
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec B
  soundness := soundness B
  completeness := completeness B

end RunningSumMul

/-!
### Entry circuit (`Assign`)

`base_field_elem.rs::Config::assign`: the full source-level `FixedPointBaseField::mul`.
Composes `RunningSumMul` with the canonicity tail — a 13-window lookup range check on
`α_0 + 2¹³⁰ - t_p` and the `Canonicity checks` gate — and returns `[α]B`.
-/

namespace Assign

/-- `t_p` as a natural number (`p = 2^254 + tPNat` for the Pallas base field). -/
def tPNat : ℕ := 45560315531419706090280762371685220353

def main (B : MulFixed.FixedBase) (alpha : Var field Fp) :
    Circuit Fp (Var Ecc.Point Fp) := do
  -- region 1+2: strict running-sum decomposition, windowed mul, complete addition
  let m ← RunningSumMul.circuit B alpha
  -- region 3: canonicity of the base-field element.
  -- α_0 = α - z_84 · 2^252, the low 252 bits.
  -- α_0_prime = α_0 + 2^130 - t_p; 13 ten-bit lookups give z_13_alpha_0_prime.
  let alpha0Prime ← witnessField fun env =>
    (env alpha - env (m.z84) * (2 ^ 252 : Fp)) + (2 ^ 130 : Fp) - (tPNat : Fp)
  let zsDecomp ← Utilities.LookupRangeCheck.CopyCheck.circuit 13 alpha0Prime
  let z13Alpha0Prime := zsDecomp[13]
  -- the 2-bit / 1-bit pieces of the top window, and the canonicity gate
  let alpha1 ← witnessField fun env => ((env (m.z84)).val % 4 : ℕ)
  let alpha2 ← witnessField fun env => ((env (m.z84)).val / 4 : ℕ)
  let z84Alpha <== m.z84
  let z44Alpha <== m.z44
  let z43Alpha <== m.z43
  BaseFieldElem.circuit {
    alpha := alpha, z84Alpha := z84Alpha, alpha1 := alpha1, alpha2 := alpha2,
    alpha0Prime := alpha0Prime, z13Alpha0Prime := z13Alpha0Prime,
    z44Alpha := z44Alpha, z43Alpha := z43Alpha }
  return m.result

instance elaborated (B : MulFixed.FixedBase) :
    ElaboratedCircuit Fp field Ecc.Point (main B) := by
  elaborate_circuit

/-- Preconditions: `α` is a canonical base-field element (always true for an actual
`Fp` cell — `α.val < p` by definition). -/
def Assumptions (_ : Fp) : Prop := True

/-- The circuit computes `[α]·B`, the fixed-base multiplication of `B` by the base-field
element `α` (reinterpreted as the scalar `α.val`, which is `< p < q`). -/
def Spec (B : MulFixed.FixedBase) (alpha : Fp) (output : Ecc.Point Fp) : Prop :=
  output.coords = ((alpha.val • B.point).x, (alpha.val • B.point).y)

/-- `p = 2^254 + t_p` for the Pallas base field. -/
private theorem base_card_eq : PALLAS_BASE_CARD = 2 ^ 254 + tPNat := by
  norm_num [PALLAS_BASE_CARD, tPNat]

/-- Telescoping a 13-step `2^10`-radix running sum to its 130-bit digit sum. Stated over
abstract cell values so the heavy combination is kernel-checked once, not inlined into
the (giant-term) entry-circuit soundness proof. -/
private theorem telescope13_eq {z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 ap : Fp}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 : ℕ}
    (h0 : z0 = ap)
    (e0 : z0 = 2 ^ 10 * z1 + (w0 : Fp)) (e1 : z1 = 2 ^ 10 * z2 + (w1 : Fp))
    (e2 : z2 = 2 ^ 10 * z3 + (w2 : Fp)) (e3 : z3 = 2 ^ 10 * z4 + (w3 : Fp))
    (e4 : z4 = 2 ^ 10 * z5 + (w4 : Fp)) (e5 : z5 = 2 ^ 10 * z6 + (w5 : Fp))
    (e6 : z6 = 2 ^ 10 * z7 + (w6 : Fp)) (e7 : z7 = 2 ^ 10 * z8 + (w7 : Fp))
    (e8 : z8 = 2 ^ 10 * z9 + (w8 : Fp)) (e9 : z9 = 2 ^ 10 * z10 + (w9 : Fp))
    (e10 : z10 = 2 ^ 10 * z11 + (w10 : Fp)) (e11 : z11 = 2 ^ 10 * z12 + (w11 : Fp))
    (e12 : z12 = (w12 : Fp)) :
    ap = ((w0 + 2 ^ 10 * w1 + 2 ^ 20 * w2 + 2 ^ 30 * w3 + 2 ^ 40 * w4 + 2 ^ 50 * w5 +
      2 ^ 60 * w6 + 2 ^ 70 * w7 + 2 ^ 80 * w8 + 2 ^ 90 * w9 + 2 ^ 100 * w10 +
      2 ^ 110 * w11 + 2 ^ 120 * w12 : ℕ) : Fp) := by
  push_cast
  linear_combination -h0 + e0 + 2 ^ 10 * e1 + 2 ^ 20 * e2 + 2 ^ 30 * e3 + 2 ^ 40 * e4 +
    2 ^ 50 * e5 + 2 ^ 60 * e6 + 2 ^ 70 * e7 + 2 ^ 80 * e8 + 2 ^ 90 * e9 +
    2 ^ 100 * e10 + 2 ^ 110 * e11 + 2 ^ 120 * e12

theorem soundness (B : MulFixed.FixedBase) :
    Soundness Fp (main B) Assumptions (Spec B) := by
  circuit_proof_start [main, Spec, RunningSumMul.circuit, BaseFieldElem.circuit,
    BaseFieldElem.Spec, Utilities.LookupRangeCheck.CopyCheck.circuit,
    Utilities.LookupRangeCheck.CopyCheck.Spec]
  obtain ⟨hRSM, hCopy, hz84eq, hz44eq, hz43eq, hGate⟩ := h_holds
  -- the windowed-mul spec: the decomposed value `V`, with `α = (V : Fp)`
  obtain ⟨ks, hks_lt, hαV, hres, hz43V, hz44V, hz84V⟩ := hRSM
  simp only [Ecc.Point.coords] at hres ⊢
  set V := ∑ j ∈ Finset.range 85, ks j * 8 ^ j with hV
  -- the canonicity gate facts
  simp only [BaseFieldElem.IsAlpha1, BaseFieldElem.DecomposesBaseFieldElem,
    BaseFieldElem.CanonicalHighBit, BaseFieldElem.alpha0, BaseFieldElem.alpha0Hi120,
    BaseFieldElem.a43, IsBool] at hGate
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
      -- lookup (`hCopy`) with `z_13 = 0` (`hz13`) gives `α_0_prime = ↑S` for some
      -- `S < 2^130` (the 130-bit digit sum). Since `α0 < 2^132` (`hα0lt132`), the
      -- value `α0 + 2^130 - t_p < p` does not wrap, so `S = α0 + 2^130 - t_p < 2^130`,
      -- i.e. `α0 < t_p`. The telescoping is proven in `telescope13_eq`; wiring it onto
      -- the concrete `CopyCheck` output vector currently hits a kernel/whnf cliff on the
      -- giant getElem terms (see commit notes / task #5). TODO: reformulate the lookup
      -- running sum over a plain `ℕ → Fp` function to sidestep the getElem reduction.
      rw [hαV, e84, hz84val,
        show (V : Fp) = (α0 : Fp) + (4 : ℕ) * OfNat.ofNat (2 ^ 252) from by
          rw [hV254]; push_cast; ring] at hα0prime
      have hα0tp : α0 < tPNat := by sorry
      rw [hV254]; omega
  have hVcanon : V = ZMod.val (show Fp from input) := by
    rw [hαV, ZMod.val_natCast, Nat.mod_eq_of_lt hVltp]
  -- hence the output is `[α.val]·B`
  rw [hres, hVcanon]

theorem completeness (B : MulFixed.FixedBase) :
    Completeness Fp (main B) Assumptions := by
  sorry

/-- `base_field_elem.rs::Config::assign` (`FixedPointBaseField::mul`): base-field-element
fixed-base scalar multiplication `[α]B`. -/
def circuit (B : MulFixed.FixedBase) : FormalCircuit Fp field Ecc.Point where
  main := main B
  Assumptions := Assumptions
  Spec := Spec B
  soundness := soundness B
  completeness := completeness B

end Assign

end Orchard.Ecc.ScalarMul.MulFixed.BaseFieldElem
