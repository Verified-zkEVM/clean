import Clean.Orchard.Ecc.MulFixed
import Clean.Orchard.Ecc.AddIncomplete
import Clean.Orchard.Ecc.Add
import Clean.Orchard.Utilities

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul_fixed/short.rs`.

`Gate.circuit` is the custom gate enabled on the final row (`q_mul_fixed_short`): the
boolean check of the last decomposition window, the `±1` check of the sign, and the
conditional negation of the `y`-coordinate.

`circuit` is the source-level entry point `short.rs::Config::assign`
(`EccInstructions::mul_fixed_short`, gadget API `FixedPointShort::mul`): it decomposes
the 64-bit magnitude into 22 three-bit windows with a strict running sum, processes the
windows like full-width fixed-base mul (window-table coordinates checks, incomplete
additions, offset-corrected most significant window, complete addition), and finally
conditionally negates the result according to the sign.
-/

namespace Orchard.Ecc.MulFixed.Short

open CompElliptic.Curves.Pasta CompElliptic.CurveForms
open ShortWeierstrass (SWPoint)
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

namespace Gate

structure Input (F : Type) where
  yP : F
  yA : F
  lastWindow : F
  sign : F
deriving ProvableStruct

def signCheck {K : Type} [One K] [Sub K] [Mul K] (row : Input K) : K :=
  row.sign * row.sign - 1

def yCheck {K : Type} [Add K] [Sub K] [Mul K] (row : Input K) : K :=
  (row.yP - row.yA) * (row.yP + row.yA)

def negationCheck {K : Type} [Sub K] [Mul K] (row : Input K) : K :=
  row.sign * row.yP - row.yA

def IsSign (sign : Fp) : Prop :=
  sign = 1 ∨ sign = 0 - 1

def SignedPointSelection (row : Input Fp) : Prop :=
  ∀ x : Fp,
    (row.sign = 1 → (x, row.yP) = (x, row.yA)) ∧
      (row.sign = 0 - 1 →
        (x, row.yP) = ShortWeierstrass.neg (x, row.yA))

def Spec (row : Input Fp) : Prop :=
  IsBool row.lastWindow ∧ IsSign row.sign ∧ SignedPointSelection row

def main (row : Var Input Fp) : Circuit Fp Unit := do
  assertBool row.lastWindow
  assertZero (signCheck row)
  assertZero (yCheck row)
  assertZero (negationCheck row)

def circuit : FormalAssertion Fp Input where
  name := "GATE Short fixed-base mul gate"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec, IsSign, SignedPointSelection,
      ShortWeierstrass.neg, signCheck, yCheck, negationCheck]
    rcases h_holds with ⟨hLastWindow, hSign, _hY, hNegation⟩
    have hSignedY : input_yA = input_sign * input_yP :=
      (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hNegation)).symm
    refine ⟨?_, ?_, ?_⟩
    · exact hLastWindow
    · have hmul : (input_sign - 1) * (input_sign + 1) = 0 := by
        linear_combination hSign
      rcases mul_eq_zero.mp hmul with hPos | hNeg
      · exact Or.inl (sub_eq_zero.mp hPos)
      · exact Or.inr (by linear_combination hNeg)
    · intro x
      constructor
      · intro hPos
        apply Prod.ext
        · rfl
        · rw [hSignedY, hPos]
          simp
      · intro hNeg
        apply Prod.ext
        · rfl
        · rw [hSignedY, hNeg]
          simp
  completeness := by
    circuit_proof_start [main, Spec, IsSign, SignedPointSelection,
      ShortWeierstrass.neg, signCheck, yCheck, negationCheck]
    rcases h_spec with ⟨hLastWindow, hSign, hPoint⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact hLastWindow
    · rcases hSign with hSign | hSign <;> rw [hSign] <;> ring
    · rcases hSign with hSign | hSign
      · have hY := congrArg Prod.snd ((hPoint 0).1 hSign)
        simp at hY
        rw [hY]
        ring
      · have hY := congrArg Prod.snd ((hPoint 0).2 hSign)
        simp at hY
        rw [hY]
        ring
    · rcases hSign with hSign | hSign
      · have hY := congrArg Prod.snd ((hPoint 0).1 hSign)
        simp at hY
        rw [hSign, hY]
        ring
      · have hY := congrArg Prod.snd ((hPoint 0).2 hSign)
        simp at hY
        rw [hSign, hY]
        ring

end Gate

/-!
### Short fixed-base value model

Same window arithmetic as full-width fixed-base mul, with `NUM_WINDOWS_SHORT = 22`
windows for the 64-bit magnitude: the most significant window is window `21` and the
initialization offset accumulates over the lower `21` windows.
-/

/-- `offset_acc` for short fixed-base mul: `∑_{j=0}^{20} 2^{3j+1}`
(`mul_fixed.rs::process_msb` with `NUM_WINDOWS_SHORT`). -/
def offsetAcc : ℕ := ∑ j ∈ Finset.range 21, 2 ^ (3 * j + 1)

theorem offsetAcc_eq : offsetAcc = ∑ j ∈ Finset.range 21, 2 * 8 ^ j := by
  unfold offsetAcc
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add, pow_mul]
  norm_num [mul_comm]

/-- The scalar multiple contributed by window `w` holding value `k`:
`(k + 2)·8^w` for the lower 21 windows, `k·8^21 - offset_acc` for the most
significant window. -/
def windowScalar (w k : ℕ) : Fq :=
  if w = 21 then (k : Fq) * 8 ^ 21 - (offsetAcc : Fq) else ((k : Fq) + 2) * 8 ^ w

/-- The window-table point for window `w` and window value `k`. -/
def windowPoint (point : Point Fp) (w k : ℕ) : Point Fp :=
  (windowScalar w k).val • point

theorem windowScalar_ne_zero {w k : ℕ} (hk : k < 8) :
    windowScalar w k ≠ 0 := by
  unfold windowScalar
  by_cases h21 : w = 21
  · rw [if_pos h21]
    interval_cases k <;> native_decide
  · rw [if_neg h21]
    apply mul_ne_zero
    · rw [show (k : Fq) + 2 = ((k + 2 : ℕ) : Fq) by push_cast; ring,
        Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have hle := Nat.le_of_dvd (by omega) hdvd
      have : PALLAS_SCALAR_CARD ≤ 9 := by omega
      norm_num [PALLAS_SCALAR_CARD] at this
    · exact pow_ne_zero _ (by decide)

theorem windowScalar_val {w k : ℕ} (hw : w < 21) (hk : k < 8) :
    (windowScalar w k).val = (k + 2) * 8 ^ w := by
  have hbound : (k + 2) * 8 ^ w < PALLAS_SCALAR_CARD := by
    calc (k + 2) * 8 ^ w ≤ 9 * 8 ^ 20 :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ < PALLAS_SCALAR_CARD := by norm_num [PALLAS_SCALAR_CARD]
  unfold windowScalar
  rw [if_neg (by omega),
    show ((k : Fq) + 2) * 8 ^ w = (((k + 2) * 8 ^ w : ℕ) : Fq) by push_cast; ring,
    ZMod.val_natCast_of_lt hbound]

/-- The window decomposition recombines to the decomposed word: the `+2` offsets of the
lower 21 windows cancel against `offset_acc` in the most significant window. -/
theorem windowScalar_partialSum (ks : ℕ → ℕ) :
    windowScalar 21 (ks 21) + (partialSum ks 20 : Fq)
      = ((∑ j ∈ Finset.range 22, ks j * 8 ^ j : ℕ) : Fq) := by
  have hsplit : partialSum ks 20
      = (∑ j ∈ Finset.range 21, ks j * 8 ^ j) + offsetAcc := by
    rw [partialSum_eq_sum, offsetAcc_eq, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, show (∑ j ∈ Finset.range 22, ks j * 8 ^ j)
      = (∑ j ∈ Finset.range 21, ks j * 8 ^ j) + ks 21 * 8 ^ 21 from
    Finset.sum_range_succ _ _]
  unfold windowScalar
  rw [if_pos rfl]
  push_cast
  ring

/--
A fixed base for short signed fixed-base scalar multiplication: a generator of the
Pallas prime-order group together with its precomputed window tables for the 22 short
windows (halo2 `FixedPoint<pallas::Affine>` with `FixedScalarKind = ShortScalar`).

The fields and invariants mirror `MulFixed.FixedBase`, with the short window count and
the short most-significant-window scalar.
-/
structure FixedBase where
  point : Point Fp
  onCurve : point.OnCurve
  params : ℕ → CoordsParams Fp
  u : ℕ → ℕ → Fp
  interpolate_eq : ∀ (w : ℕ), w < 22 → ∀ (k : ℕ), k < 8 →
    interpolate (params w) (k : Fp) = (windowPoint point w k).x
  u_mul_u : ∀ (w : ℕ), w < 22 → ∀ (k : ℕ), k < 8 →
    u w k * u w k = (windowPoint point w k).y + (params w).z
  z_sub_y_not_square : ∀ (w : ℕ), w < 22 → ∀ (k : ℕ), k < 8 →
    ¬ IsSquare ((params w).z - (windowPoint point w k).y)

namespace FixedBase
variable (B : FixedBase)

theorem nsmul_eq_zero_iff (n : ℕ) : n • B.point = 0 ↔ PALLAS_SCALAR_CARD ∣ n := by
  exact Point.nsmul_eq_zero_iff B.onCurve n

theorem windowPoint_ne_zero {w k : ℕ} (hk : k < 8) :
    windowPoint B.point w k ≠ 0 := by
  unfold windowPoint
  rw [Ne, B.nsmul_eq_zero_iff]
  intro hdvd
  have hval : (windowScalar w k).val < PALLAS_SCALAR_CARD := ZMod.val_lt _
  have h0 : (windowScalar w k).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hval
  exact windowScalar_ne_zero hk ((ZMod.val_eq_zero _).mp h0)

theorem windowPoint_onCurve {w k : ℕ} (hk : k < 8) :
    (windowPoint B.point w k).OnCurve := by
  unfold windowPoint
  apply Point.nsmul_onCurve B.onCurve
  · exact Nat.pos_of_ne_zero fun h0 =>
      windowScalar_ne_zero hk ((ZMod.val_eq_zero _).mp h0)
  · exact ZMod.val_lt _

theorem nsmul_ne_zero {n : ℕ} (hn : 0 < n) (hlt : n < PALLAS_SCALAR_CARD) :
    n • B.point ≠ 0 :=
  Point.nsmul_ne_zero B.onCurve hn hlt

theorem nsmul_onCurve {n : ℕ} (hn : 0 < n) (hlt : n < PALLAS_SCALAR_CARD) :
    (n • B.point).OnCurve :=
  Point.nsmul_onCurve B.onCurve hn hlt

theorem nsmul_x_ne {s t : ℕ} (hs : 0 < s) (hst : s < t)
    (hsum : s + t < PALLAS_SCALAR_CARD) :
    (t • B.point).x ≠ (s • B.point).x :=
  Point.nsmul_x_ne B.onCurve hs hst hsum

/-- Congruent scalars produce the same multiple of the generator. -/
theorem nsmul_congr {m n : ℕ} (h : m ≡ n [MOD PALLAS_SCALAR_CARD]) :
    m • B.point = n • B.point :=
  Point.nsmul_congr B.onCurve h

/-- Adding a cast natural to a scalar acts as expected on multiples of the generator. -/
theorem add_natCast_val_nsmul (a : Fq) (S : ℕ) :
    (a + (S : Fq)).val • B.point = (a.val + S) • B.point := by
  apply B.nsmul_congr
  rw [ZMod.val_add, ZMod.val_natCast]
  exact (Nat.mod_modEq _ _).trans (Nat.ModEq.add_left _ (Nat.mod_modEq _ _))

/-- The value-level result of multiplying the fixed base by a scalar. -/
def scalarMul (s : Fq) : Point Fp :=
  { x := (s.val • B.point).x, y := (s.val • B.point).y }

instance : HSMul Fq FixedBase (Point Fp) where
  hSMul s B := B.scalarMul s

theorem smul_valid (s : Fq) : (s • B).Valid :=
  Point.valid_nsmul (.inl B.onCurve) s.val

theorem smul_coords (s : Fq) :
    (s • B).coords = ((s.val • B.point).x, (s.val • B.point).y) := rfl

/-- Coordinate form of adding two scalar multiples of the fixed base. -/
theorem nsmul_add_coords {a b c : ℕ} (h : a + b = c) :
    ShortWeierstrass.add pallasA ((a • B.point).x, (a • B.point).y)
        ((b • B.point).x, (b • B.point).y) = (c • B.point).coords := by
  exact Point.nsmul_add_coords B.onCurve h

/-- Coordinate form of a known point-addition equality. -/
theorem add_coords_eq {P Q R : Point Fp} (h : P + Q = R) :
    ShortWeierstrass.add pallasA (P.x, P.y) (Q.x, Q.y) = R.coords := by
  exact Point.add_coords_eq h

/-- Negating the scalar negates the `y`-coordinate of the result. -/
theorem smul_neg (s : Fq) :
    (((-s) : Fq) • B : Point Fp) = { x := (s • B).x, y := -((s • B).y) } := by
  suffices h : (-s).val • B.point = -(s.val • B.point) by
    show ({ x := ((-s).val • B.point).x, y := ((-s).val • B.point).y } : Point Fp) = _
    rw [h]
    rfl
  have hp_valid : B.point.Valid := .inl B.onCurve
  apply (Point.ext_toSW_iff
    (Point.valid_nsmul hp_valid (-s).val)
    (Point.valid_neg (Point.valid_nsmul hp_valid s.val))).mpr
  rw [Point.toSW_nsmul hp_valid (-s).val,
    Point.toSW_neg (Point.valid_nsmul hp_valid s.val),
    Point.toSW_nsmul hp_valid s.val]
  by_cases hs : s = 0
  · subst hs
    simp
  · have hnonzero : B.point.toSW hp_valid ≠ 0 := by
      intro hzero
      rw [← Point.toSW_zero, ← Point.ext_toSW_iff] at hzero
      have hcurve := B.onCurve
      rw [hzero] at hcurve
      exact Point.not_onCurve_zero hcurve
    have horderSW : PALLAS_SCALAR_CARD • B.point.toSW hp_valid = 0 := by
      rw [← Point.addOrderOf_eq hnonzero]
      exact addOrderOf_nsmul_eq_zero _
    have : NeZero s := ⟨hs⟩
    rw [ZMod.val_neg_of_ne_zero s, sub_nsmul _ (le_of_lt (ZMod.val_lt s)), horderSW]
    simp

/-- Soundness of one window row (same argument as `MulFixed.FixedBase`'s): if the
coordinates gate holds on a row whose window value is `k < 8`, the row's point is the
window-table point. -/
theorem coords_eq_windowPoint {w k : ℕ} (hw : w < 22) (hk : k < 8)
    {row : CoordsRow Fp} (hwindow : row.window = (k : Fp))
    (hspec : Coords.Spec (B.params w) row) :
    row.xP = (windowPoint B.point w k).x ∧ row.yP = (windowPoint B.point w k).y := by
  obtain ⟨hx, hu, hcurve⟩ := hspec
  have hxP : row.xP = (windowPoint B.point w k).x := by
    rw [hx, interpolatedX, hwindow, B.interpolate_eq w hw k hk]
  refine ⟨hxP, ?_⟩
  have hrowCurve : ({ x := (windowPoint B.point w k).x, y := row.yP } : Point Fp).OnCurve := by
    rw [← hxP]
    dsimp [Point.OnCurve]
    linear_combination hcurve
  rcases ShortWeierstrass.y_eq_or_y_eq_neg_of_onCurve
      ((Point.onCurve_iff
        ({ x := (windowPoint B.point w k).x, y := row.yP } : Point Fp)).mp hrowCurve)
      ((Point.onCurve_iff
        ({ x := (windowPoint B.point w k).x, y := (windowPoint B.point w k).y } :
          Point Fp)).mp (B.windowPoint_onCurve hk)) with hy | hy
  · exact hy
  · simp only at hy
    exact absurd ⟨row.u, by rw [hy] at hu; linear_combination -hu⟩
      (B.z_sub_y_not_square w hw k hk)

end FixedBase

/-!
### Entry circuit

Value model: `windowVal m w` is window `w` of the base-`8` decomposition of the
magnitude, `zValue m w` is the running-sum value `z_w = ⌊m / 8^w⌋`, and `rowTailValue`
is the honest-prover assignment of the witnessed cells of one window row.
-/

/-- The magnitude-sign input pair (`ecc/chip.rs::MagnitudeSign`): two already-assigned
cells holding an unsigned (at most 64-bit) integer and a sign in `{1, -1}`. -/
structure MagnitudeSign (F : Type) where
  magnitude : F
  sign : F
deriving ProvableStruct

def windowVal (m : Fp) (w : ℕ) : ℕ := m.val / 8 ^ w % 8

theorem windowVal_lt (m : Fp) (w : ℕ) : windowVal m w < 8 :=
  Nat.mod_lt _ (by norm_num)

/-- The honest-prover running sum value `z_w = ⌊magnitude / 8^w⌋`. -/
def zValue (m : Fp) (w : ℕ) : Fp := ((m.val / 8 ^ w : ℕ) : Fp)

/-- The honest-prover witnessed cells of window row `w`: the next running sum value,
the coordinates of the window-table point, and the table square root `u`. -/
structure RowTail (F : Type) where
  zNext : F
  xP : F
  yP : F
  u : F
deriving ProvableStruct

def rowTailValue (B : FixedBase) (m : Fp) (w : ℕ) : RowTail Fp where
  zNext := zValue m (w + 1)
  xP := (windowPoint B.point w (windowVal m w)).x
  yP := (windowPoint B.point w (windowVal m w)).y
  u := B.u w (windowVal m w)

private theorem rowTailValue_zNext (B : FixedBase) (m : Fp) (w : ℕ) :
    (rowTailValue B m w).zNext = zValue m (w + 1) := rfl

private theorem rowTailValue_xP (B : FixedBase) (m : Fp) (w : ℕ) :
    (rowTailValue B m w).xP = (windowPoint B.point w (windowVal m w)).x := rfl

private theorem rowTailValue_yP (B : FixedBase) (m : Fp) (w : ℕ) :
    (rowTailValue B m w).yP = (windowPoint B.point w (windowVal m w)).y := rfl

private theorem rowTailValue_u (B : FixedBase) (m : Fp) (w : ℕ) :
    (rowTailValue B m w).u = B.u w (windowVal m w) := rfl

/-- The witness program of one window row: take window `w` of the base-8 decomposition
of the committed magnitude (`k = m.val / 8^w % 8`, matching `windowVal` definitionally),
witness the next running-sum value, and read the three window-table columns at `k`. -/
def rowProgram (B : FixedBase) (magnitude : Expression Fp) (w : ℕ) :
    Witgen.M Fp (RowTail (Witgen.FExpr Fp)) := do
  let xs := Vector.ofFn fun k : Fin 8 => (windowPoint B.point w k.val).x
  let ys := Vector.ofFn fun k : Fin 8 => (windowPoint B.point w k.val).y
  let us := Vector.ofFn fun k : Fin 8 => B.u w k.val
  let s := magnitude.val
  let k := s / (8 ^ w : ℕ) % 8
  return RowTail.mk (s / (8 ^ (w + 1) : ℕ)).toField xs[k] ys[k] us[k]

def main (B : FixedBase) (input : Var MagnitudeSign Fp) :
    Circuit Fp (Var Point Fp) := do
  -- `copy_decompose`: `z_0` is a copy of the magnitude
  let z₀ <== input.magnitude
  -- window 0 initializes the accumulator
  let t₀ : Var RowTail Fp ← witnessProgram (rowProgram B input.magnitude 0)
  Utilities.RunningSum.circuit 3 { zCur := z₀, zNext := t₀.zNext }
  RunningSumCoords.circuit (B.params 0)
    { zCur := z₀, zNext := t₀.zNext, xP := t₀.xP, yP := t₀.yP, u := t₀.u }
  let acc₀ : Var Point Fp := { x := t₀.xP, y := t₀.yP }
  -- windows 1..20 are added with incomplete addition
  let (acc, z₂₁) ← Circuit.foldl (.finRange 20) (acc₀, t₀.zNext) fun (acc, zCur) i => do
    let t : Var RowTail Fp ← witnessProgram (rowProgram B input.magnitude (i.val + 1))
    Utilities.RunningSum.circuit 3 { zCur := zCur, zNext := t.zNext }
    RunningSumCoords.circuit (B.params (i.val + 1))
      { zCur := zCur, zNext := t.zNext, xP := t.xP, yP := t.yP, u := t.u }
    let acc' ← AddIncomplete.circuit { p := { x := t.xP, y := t.yP }, q := acc }
    return (acc', t.zNext)
  -- most significant window 21
  let t₂₁ : Var RowTail Fp ← witnessProgram (rowProgram B input.magnitude 21)
  Utilities.RunningSum.circuit 3 { zCur := z₂₁, zNext := t₂₁.zNext }
  RunningSumCoords.circuit (B.params 21)
    { zCur := z₂₁, zNext := t₂₁.zNext, xP := t₂₁.xP, yP := t₂₁.yP, u := t₂₁.u }
  -- strict decomposition: the final running sum value is zero
  t₂₁.zNext === (0 : Expression Fp)
  -- `[magnitude]B` by complete addition
  let magnitudeMul ← Add.circuit { p := { x := t₂₁.xP, y := t₂₁.yP }, q := acc }
  -- final row: copy sign and last window, conditionally negate the `y`-coordinate
  let sign <== input.sign
  let lastWindow <== z₂₁
  let yP ← witness <| input.sign * magnitudeMul.y
  Gate.circuit { yP := yP, yA := magnitudeMul.y, lastWindow := lastWindow, sign := sign }
  return { x := magnitudeMul.x, y := yP }

instance elaborated (B : FixedBase) :
    ElaboratedCircuit Fp MagnitudeSign Point (main B) := by
  elaborate_circuit

def Spec (B : FixedBase) (input : MagnitudeSign Fp) (output : Point Fp)
    (_ : ProverData Fp) : Prop :=
  ∃ m : ℕ, m < 2 ^ 64 ∧ input.magnitude = (m : Fp) ∧
    ((input.sign = 1 ∧ output = (m : Fq) • B) ∨
      (input.sign = -1 ∧ output = ((-(m : Fq)) : Fq) • B))

def ProverAssumptions (input : MagnitudeSign Fp) (_ : ProverData Fp)
    (_ : ProverHint Fp) : Prop :=
  input.magnitude.val < 2 ^ 64 ∧ (input.sign = 1 ∨ input.sign = -1)

def ProverSpec (B : FixedBase) (input : MagnitudeSign Fp) (output : Point Fp)
    (_ : ProverHint Fp) : Prop :=
  (input.sign = 1 → output = (input.magnitude.val : Fq) • B) ∧
    (input.sign = -1 → output = ((-(input.magnitude.val : Fq)) : Fq) • B)

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
  have hcard : (8 : ℕ) < CompElliptic.Fields.Pasta.PALLAS_BASE_CARD := by
    norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at this

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

private theorem inv_lt_card {S j : ℕ} (hS : S < 2 * 8 ^ (j + 1)) (hj : j ≤ 20) :
    S < PALLAS_SCALAR_CARD := by
  have hpow : (8 : ℕ) ^ (j + 1) ≤ 8 ^ 21 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard : 2 * 8 ^ 21 < PALLAS_SCALAR_CARD := by norm_num [PALLAS_SCALAR_CARD]
  omega

private theorem step_sum_lt {S t j : ℕ} (hS : S < 2 * 8 ^ (j + 1))
    (ht : t ≤ 9 * 8 ^ (j + 1)) (hj : j ≤ 19) : S + t < PALLAS_SCALAR_CARD := by
  have hpow : (8 : ℕ) ^ (j + 1) ≤ 8 ^ 20 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard : 11 * 8 ^ 20 < PALLAS_SCALAR_CARD := by norm_num [PALLAS_SCALAR_CARD]
  omega

private theorem partialSum_step_eq {ks : ℕ → ℕ} {j t : ℕ}
    (hval : t = (ks (j + 1) + 2) * 8 ^ (j + 1)) :
    t + partialSum ks j = partialSum ks (j + 1) := by
  rw [partialSum, hval]
  omega

private theorem short_magnitude_lt {ks : ℕ → ℕ} {m : ℕ}
    (hm : m = ∑ j ∈ Finset.range 22, ks j * 8 ^ j)
    (hks_lt : ∀ w, ks w < 8) (hks21_le : ks 21 ≤ 1) :
    m < 2 ^ 64 := by
  have hsum21 : ∑ j ∈ Finset.range 21, ks j * 8 ^ j < 8 ^ 21 :=
    sum_lt_of_windows fun j _ => hks_lt j
  have hsplit : m = (∑ j ∈ Finset.range 21, ks j * 8 ^ j) + ks 21 * 8 ^ 21 := by
    rw [hm, Finset.sum_range_succ]
  have hpow : (8 : ℕ) ^ 21 = 2 ^ 63 := by norm_num
  have h64 : (2 : ℕ) ^ 64 = 2 * 2 ^ 63 := by norm_num
  have : ks 21 * 8 ^ 21 ≤ 8 ^ 21 := by
    calc ks 21 * 8 ^ 21 ≤ 1 * 8 ^ 21 := Nat.mul_le_mul_right _ hks21_le
      _ = 8 ^ 21 := by ring
  omega

/-- The telescoped running sum: if every step satisfies the decomposition relation and
the final value is zero, the initial value is the weighted digit sum. -/
private theorem chain_eq_sum (z : ℕ → Fp) (ks : ℕ → ℕ)
    (hword : ∀ w < 22, z w = (ks w : Fp) + 8 * z (w + 1))
    (hz22 : z 22 = 0) :
    z 0 = ((∑ j ∈ Finset.range 22, ks j * 8 ^ j : ℕ) : Fp) := by
  have key : ∀ w ≤ 22,
      z 0 = ((∑ j ∈ Finset.range w, ks j * 8 ^ j : ℕ) : Fp) + z w * ((8 ^ w : ℕ) : Fp) := by
    intro w hw
    induction w with
    | zero => simp
    | succ v ih =>
      rw [ih (by omega), hword v (by omega), Finset.sum_range_succ]
      push_cast
      ring
  have h22 := key 22 (by omega)
  rw [hz22, zero_mul, _root_.add_zero] at h22
  exact h22

/-- The evaluated accumulator entering loop iteration `j` (after windows `0..j`,
relative to a circuit starting at offset `i₀`). -/
private def accPt (env : Environment Fp) (i₀ : ℕ) : ℕ → Point Fp
  | 0 => { x := env.get (i₀ + 1 + 1), y := env.get (i₀ + 1 + 1 + 1) }
  | j + 1 =>
    { x := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + j * 10 + 4 + 2 + 2)).x,
      y := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + j * 10 + 4 + 2 + 2)).y }

/-- The index of the cell holding the running sum value `z_{j+1}`, for `j ≤ 20`
(relative to a circuit starting at offset `i₀`). -/
private def zCell (i₀ : ℕ) : ℕ → ℕ
  | 0 => i₀ + 1
  | j + 1 => i₀ + 1 + 4 + j * 10

/-- Convert the range-check word equation into the running sum step relation. -/
private theorem step_of_word {a b : Fp} {k : ℕ}
    (h : Utilities.RunningSum.word 3 { zCur := a, zNext := b } = (k : Fp)) :
    a = (k : Fp) + 8 * b := by
  simp only [Utilities.RunningSum.word, Utilities.RunningSum.twoPowWindow] at h
  have h8 : (((2 : ℕ) ^ 3 : ℕ) : Fp) = 8 := by norm_num
  rw [h8] at h
  linear_combination h

private theorem acc_eq_partialSum_nsmul (B : FixedBase) (acc : ℕ → Point Fp)
    (ks : ℕ → ℕ) (hks_lt : ∀ w, ks w < 8)
    (h0 : acc 0 = windowPoint B.point 0 (ks 0))
    (hstep : ∀ (j : ℕ), j < 20 →
      acc j = partialSum ks j • B.point →
      acc (j + 1) = windowPoint B.point (j + 1) (ks (j + 1)) + acc j) :
    ∀ (w : ℕ), w ≤ 20 →
      acc w = partialSum ks w • B.point := by
  intro w hw
  induction w with
  | zero =>
      rw [h0]
      unfold windowPoint
      rw [windowScalar_val (by norm_num) (hks_lt 0), partialSum]
      simp
  | succ j ih =>
      have hj : j < 20 := by omega
      have hval : (windowScalar (j + 1) (ks (j + 1))).val =
          (ks (j + 1) + 2) * 8 ^ (j + 1) :=
        windowScalar_val (by omega) (hks_lt (j + 1))
      rw [hstep j hj (ih (by omega)), ih (by omega)]
      unfold windowPoint
      rw [Point.nsmul_add_nsmul B.onCurve, partialSum_step_eq hval]

private theorem add_step_of_scalar_meaning (B : FixedBase) {A P Acc : Point Fp} {t S : ℕ}
    (hP : P = t • B.point) (hAcc : Acc = S • B.point)
    (ht_pos : 0 < t) (ht_card : t < PALLAS_SCALAR_CARD)
    (hS_pos : 0 < S) (hS_card : S < PALLAS_SCALAR_CARD)
    (hS_lt_t : S < t) (hsum_card : S + t < PALLAS_SCALAR_CARD)
    (hinc : P.OnCurve ∧ Acc.OnCurve ∧ P.x ≠ Acc.x → A.OnCurve ∧ A = P + Acc) :
    A = P + Acc := by
  exact (hinc ⟨by
      rw [hP]
      exact B.nsmul_onCurve ht_pos ht_card,
    by
      rw [hAcc]
      exact B.nsmul_onCurve hS_pos hS_card,
    by
      rw [hP, hAcc]
      exact B.nsmul_x_ne hS_pos hS_lt_t hsum_card⟩).2

private theorem acc_step_of_coords (B : FixedBase) (ks : ℕ → ℕ)
    (hks_lt : ∀ w, ks w < 8)
    {j k : ℕ} (hj : j < 20) (hk : k < 8) (hks : ks (j + 1) = k)
    {row : RunningSumCoords.Input Fp} {A Acc : Point Fp}
    (hcoords : Coords.Spec (B.params (j + 1)) (RunningSumCoords.coordsRow row))
    (hwindow : (RunningSumCoords.coordsRow row).window = (k : Fp))
    (hacc : Acc = partialSum ks j • B.point)
    (hinc : (Point.mk row.xP row.yP).OnCurve ∧ Acc.OnCurve ∧ row.xP ≠ Acc.x →
      A.OnCurve ∧ A = Point.mk row.xP row.yP + Acc) :
    A = windowPoint B.point (j + 1) (ks (j + 1)) + Acc := by
  obtain ⟨hpx, hpy⟩ :=
    B.coords_eq_windowPoint (by omega) hk hwindow hcoords
  rw [← hks] at hpx hpy
  set t := (windowScalar (j + 1) (ks (j + 1))).val with ht_def
  have hval : t = (ks (j + 1) + 2) * 8 ^ (j + 1) :=
    windowScalar_val (by omega) (by rw [hks]; exact hk)
  have hS_lt := partialSum_lt ks j fun _ _ => hks_lt _
  have hS_pos := partialSum_pos ks j
  have ht_lower : 2 * 8 ^ (j + 1) ≤ t := by
    rw [hval]
    exact Nat.mul_le_mul_right _ (by omega)
  have ht_upper : t ≤ 9 * 8 ^ (j + 1) := by
    rw [hval]
    exact Nat.mul_le_mul_right _ (by rw [hks]; omega)
  have hS_card := inv_lt_card hS_lt (by omega)
  have hsum_card := step_sum_lt hS_lt ht_upper (by omega)
  have hwp : windowPoint B.point (j + 1) (ks (j + 1)) = t • B.point := by
    rw [ht_def]
    rfl
  have hP : Point.mk row.xP row.yP = windowPoint B.point (j + 1) (ks (j + 1)) := by
    apply Point.ext_coords
    exact Prod.ext hpx hpy
  have hP_t : Point.mk row.xP row.yP = t • B.point := by
    rw [hP, hwp]
  have hstep := add_step_of_scalar_meaning (B := B) (A := A)
    (P := Point.mk row.xP row.yP) (Acc := Acc)
    (t := t) (S := partialSum ks j) hP_t hacc
    (Nat.lt_of_lt_of_le
      (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _)) ht_lower) (by omega)
    hS_pos hS_card (Nat.lt_of_lt_of_le hS_lt ht_lower) hsum_card hinc
  rw [← hP]
  exact hstep

private theorem window21_add_partialSum_eq_nsmul (B : FixedBase) (ks : ℕ → ℕ)
    {m t S k : ℕ}
    (ht : t = (windowScalar 21 k).val) (hS : S = partialSum ks 20)
    (hk : ks 21 = k) (hm : m = ∑ j ∈ Finset.range 22, ks j * 8 ^ j) :
    t • B.point + S • B.point = ((m : Fq).val) • B.point := by
  rw [Point.nsmul_add_nsmul B.onCurve, ht, hS, ← B.add_natCast_val_nsmul, ← hk,
    windowScalar_partialSum ks, ← hm]

theorem soundness (B : FixedBase) :
    GeneralFormalCircuit.Soundness Fp (main B) (fun _ _ => True) (Spec B) := by
  circuit_proof_start [Gate.circuit, Gate.Spec, Gate.IsSign,
    Gate.SignedPointSelection, Utilities.RunningSum.circuit, Utilities.RunningSum.Spec,
    RunningSumCoords.circuit, RunningSumCoords.Spec, AddIncomplete.circuit,
    AddIncomplete.Spec, AddIncomplete.Assumptions, Add.circuit, Add.Spec,
    Add.Assumptions, List.sum_cons, List.sum_nil]
  simp +instances only [Nat.reduceMul, Nat.reduceSub, circuit_norm,
    ] at h_holds ⊢
  obtain ⟨h_z0, h_rs0, h_coords0, h_loop, h_rs21, h_coords21, h_z22, h_add,
    h_signCopy, h_lastwCopy, h_isBool, h_isSign, h_signSel⟩ := h_holds
  -- clean up the per-iteration loop hypothesis
  replace h_loop : ∀ (j : ℕ) (hj : j < 20),
      Utilities.RunningSum.InRange (2 ^ 3) (Utilities.RunningSum.word 3
        { zCur := env.get (zCell i₀ j), zNext := env.get (zCell i₀ (j + 1)) }) ∧
      Coords.Spec (B.params (j + 1)) (RunningSumCoords.coordsRow
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
    rcases j with _ | j'
    · simpa only [zCell, accPt, Nat.zero_mul, Nat.add_zero, Nat.reduceAdd, circuit_norm]
        using h_loop.1
    · simpa only [zCell, accPt, Nat.reduceAdd, circuit_norm]
        using h_loop.2 j' (by omega)
  clear h_input
  -- window values from the range checks
  obtain ⟨k0, hk0_lt, hw0⟩ := exists_lt_of_inRange h_rs0
  obtain ⟨k21, hk21_lt, hw21⟩ := exists_lt_of_inRange h_rs21
  have hkE : ∀ j : Fin 20, ∃ k : ℕ, k < 8 ∧
      Utilities.RunningSum.word 3
          { zCur := env.get (zCell i₀ j.val), zNext := env.get (zCell i₀ (j.val + 1)) }
        = (k : Fp) :=
    fun j => exists_lt_of_inRange (h_loop j.1 j.2).1
  choose kf hkf_lt hkf using hkE
  -- The combined window function and running sum function are kept opaque (introduced
  -- through an existential) so kernel defeq checks get stuck on them instead of
  -- unfolding the case analysis, see `doc/performance-problems.md`.
  obtain ⟨ks, hks_def⟩ : ∃ ks' : ℕ → ℕ, ks' = fun w =>
      if w = 0 then k0 else if h : w - 1 < 20 then kf ⟨w - 1, h⟩ else k21 := ⟨_, rfl⟩
  have hks0 : ks 0 = k0 := by simp [hks_def]
  have hksj : ∀ (j : ℕ) (hj : j < 20), ks (j + 1) = kf ⟨j, hj⟩ := by
    intro j hj
    simp [hks_def, hj]
  have hks21 : ks 21 = k21 := by norm_num [hks_def]
  have hks_lt : ∀ w, ks w < 8 := by
    intro w
    simp only [hks_def]
    split_ifs
    · exact hk0_lt
    · exact hkf_lt _
    · exact hk21_lt
  -- the running sum values as a function
  obtain ⟨zf, hzf_def⟩ : ∃ zf' : ℕ → Fp, zf' = fun w =>
      if w = 0 then env.get i₀
      else if h : w ≤ 21 then env.get (zCell i₀ (w - 1))
      else env.get (i₀ + 1 + 4 + 200) := ⟨_, rfl⟩
  have hzf0 : zf 0 = env.get i₀ := by simp [hzf_def]
  have hzf_succ : ∀ j, j < 21 → zf (j + 1) = env.get (zCell i₀ j) := by
    intro j hj
    simp only [hzf_def]
    rw [if_neg (Nat.succ_ne_zero j), dif_pos (Nat.succ_le_iff.mpr hj), Nat.add_sub_cancel]
  have hzf22 : zf 22 = env.get (i₀ + 1 + 4 + 200) := by
    simp only [hzf_def]
    rw [if_neg (by omega), dif_neg (by omega)]
  -- telescope the running sum into the magnitude
  have hchain : ∀ w < 22, zf w = (ks w : Fp) + 8 * zf (w + 1) := by
    intro w hw
    rcases w with _ | w
    · rw [hzf0, hzf_succ 0 (by omega), hks0]
      exact step_of_word hw0
    · rcases Nat.lt_or_ge w 20 with hj | hj
      · rw [hzf_succ w (by omega), hzf_succ (w + 1) (by omega), hksj w hj]
        exact step_of_word (hkf ⟨w, hj⟩)
      · have hw20 : w = 20 := by omega
        subst hw20
        rw [hzf_succ 20 (by omega), hzf22, hks21]
        exact step_of_word hw21
  obtain ⟨m, hm_def⟩ : ∃ m' : ℕ, m' = ∑ j ∈ Finset.range 22, ks j * 8 ^ j := ⟨_, rfl⟩
  have hmag : input_magnitude = (m : Fp) := by
    rw [← h_z0, ← hzf0, chain_eq_sum zf ks hchain (by rw [hzf22]; exact h_z22), hm_def]
  -- the most significant window is a bit, so the magnitude fits in 64 bits
  have hz21_eq : env.get (zCell i₀ 20) = (k21 : Fp) := by
    have h := step_of_word hw21
    rw [h_z22] at h
    rw [show env.get (zCell i₀ 20) = env.get (i₀ + 1 + 4 + 190) from rfl]
    linear_combination h
  have hk21_bool : k21 = 0 ∨ k21 = 1 := by
    rw [h_lastwCopy] at h_isBool
    rcases h_isBool with h | h
    · exact Or.inl (natCast_inj_of_lt_8 hk21_lt (by norm_num)
        (by rw [← hz21_eq,
          show env.get (zCell i₀ 20) = env.get (i₀ + 1 + 4 + 190) from rfl, h]; norm_num))
    · exact Or.inr (natCast_inj_of_lt_8 hk21_lt (by norm_num)
        (by rw [← hz21_eq,
          show env.get (zCell i₀ 20) = env.get (i₀ + 1 + 4 + 190) from rfl, h]; norm_num))
  have hm_lt : m < 2 ^ 64 := by
    have hks21_le : ks 21 ≤ 1 := by
      rw [hks21]
      rcases hk21_bool with h | h <;> omega
    exact short_magnitude_lt hm_def hks_lt hks21_le
  have h_acc0 : accPt env i₀ 0 = windowPoint B.point 0 (ks 0) := by
    have hwindow : (RunningSumCoords.coordsRow
        { zCur := env.get i₀, zNext := env.get (i₀ + 1), xP := env.get (i₀ + 1 + 1),
          yP := env.get (i₀ + 1 + 1 + 1),
          u := env.get (i₀ + 1 + 1 + 1 + 1) } : CoordsRow Fp).window = (k0 : Fp) := by
      show env.get i₀ - env.get (i₀ + 1) * 8 = (k0 : Fp)
      linear_combination step_of_word hw0
    obtain ⟨hpx, hpy⟩ := B.coords_eq_windowPoint (by omega) hk0_lt hwindow h_coords0
    rw [show (RunningSumCoords.coordsRow
        { zCur := env.get i₀, zNext := env.get (i₀ + 1), xP := env.get (i₀ + 1 + 1),
          yP := env.get (i₀ + 1 + 1 + 1),
          u := env.get (i₀ + 1 + 1 + 1 + 1) } : CoordsRow Fp).xP
        = env.get (i₀ + 1 + 1) from rfl] at hpx
    rw [show (RunningSumCoords.coordsRow
        { zCur := env.get i₀, zNext := env.get (i₀ + 1), xP := env.get (i₀ + 1 + 1),
          yP := env.get (i₀ + 1 + 1 + 1),
          u := env.get (i₀ + 1 + 1 + 1 + 1) } : CoordsRow Fp).yP
        = env.get (i₀ + 1 + 1 + 1) from rfl] at hpy
    rw [hks0]
    simp only [accPt, hpx, hpy]
  have h_acc_step : ∀ (j : ℕ), j < 20 →
      accPt env i₀ j = partialSum ks j • B.point →
      accPt env i₀ (j + 1) = windowPoint B.point (j + 1) (ks (j + 1)) +
        accPt env i₀ j := by
    intro j hj hacc
    obtain ⟨_, h_coordsRow, h_inc⟩ := h_loop j hj
    have hwindow : (RunningSumCoords.coordsRow
        { zCur := env.get (zCell i₀ j), zNext := env.get (zCell i₀ (j + 1)),
          xP := env.get (i₀ + 1 + 4 + j * 10 + 1),
          yP := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1),
          u := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1 + 1) } : CoordsRow Fp).window
        = (kf ⟨j, hj⟩ : Fp) := by
      show env.get (zCell i₀ j) - env.get (zCell i₀ (j + 1)) * 8 = (kf ⟨j, hj⟩ : Fp)
      linear_combination step_of_word (hkf ⟨j, hj⟩)
    exact acc_step_of_coords B ks hks_lt hj (hkf_lt ⟨j, hj⟩) (hksj j hj)
      h_coordsRow hwindow hacc h_inc
  have h_inv : ∀ (w : ℕ), w ≤ 20 →
      accPt env i₀ w = partialSum ks w • B.point :=
    acc_eq_partialSum_nsmul B (accPt env i₀) ks hks_lt h_acc0 h_acc_step
  clear h_loop
  -- the window-21 point
  have hwindow21 : (RunningSumCoords.coordsRow
      { zCur := env.get (i₀ + 1 + 4 + 190), zNext := env.get (i₀ + 1 + 4 + 200),
        xP := env.get (i₀ + 1 + 4 + 200 + 1), yP := env.get (i₀ + 1 + 4 + 200 + 1 + 1),
        u := env.get (i₀ + 1 + 4 + 200 + 1 + 1 + 1) } : CoordsRow Fp).window = (k21 : Fp) := by
    show env.get (i₀ + 1 + 4 + 190) - env.get (i₀ + 1 + 4 + 200) * 8 = (k21 : Fp)
    linear_combination step_of_word hw21
  obtain ⟨hpx21, hpy21⟩ :=
    B.coords_eq_windowPoint (show (21 : ℕ) < 22 by norm_num) hk21_lt hwindow21 h_coords21
  -- Window-21 values are kept opaque from here on: kernel defeq checks must get stuck
  -- on them instead of unfolding `windowScalar 21` into `offsetAcc` values, and on the
  -- accumulated scalar instead of unfolding the `partialSum` recursion
  -- (see `doc/performance-problems.md`).
  obtain ⟨t21, ht21_def⟩ : ∃ t : ℕ, t = (windowScalar 21 k21).val := ⟨_, rfl⟩
  have hP21_eq : windowPoint B.point 21 k21 = t21 • B.point := by
    rw [ht21_def]
    rfl
  replace hpx21 : env.get (i₀ + 1 + 4 + 200 + 1) = (t21 • B.point).x := by
    rw [← hP21_eq]
    exact hpx21
  replace hpy21 : env.get (i₀ + 1 + 4 + 200 + 1 + 1) = (t21 • B.point).y := by
    rw [← hP21_eq]
    exact hpy21
  obtain ⟨S20, hS20_def⟩ : ∃ S : ℕ, S = partialSum ks 20 := ⟨_, rfl⟩
  have hS_lt : S20 < 2 * 8 ^ (20 + 1) := by
    rw [hS20_def]
    exact partialSum_lt ks 20 fun _ _ => hks_lt _
  have hS_pos : 0 < S20 := by
    rw [hS20_def]
    exact partialSum_pos ks 20
  have hS_card := inv_lt_card hS_lt le_rfl
  have hacc20 :
        ({ x := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + 190 + 4 + 2 + 2)).x,
           y := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + 190 + 4 + 2 + 2)).y }
          : Point Fp)
        = S20 • B.point := by
    rw [hS20_def]
    exact h_inv 20 le_rfl
  -- the complete addition produces `[magnitude]B`
  have hValidP :
      ({ x := env.get (i₀ + 1 + 4 + 200 + 1),
         y := env.get (i₀ + 1 + 4 + 200 + 1 + 1) } : Point Fp).Valid := by
    rw [hpx21, hpy21]
    exact Point.valid_nsmul (.inl B.onCurve) t21
  have hValidAcc :
      ({ x := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + 190 + 4 + 2 + 2)).x,
         y := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + 190 + 4 + 2 + 2)).y }
        : Point Fp).Valid := by
    rw [hacc20]
    exact Point.valid_nsmul (.inl B.onCurve) S20
  have h_final := h_add ⟨hValidP, hValidAcc⟩
  have hmulEq :
      ({ x := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + 200 + 4 + 2 + 2)).x,
         y := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + 200 + 4 + 2 + 2)).y }
        : Point Fp)
      = (m : Fq) • B := by
    apply Point.ext_coords
    rw [h_final.2]
    show ShortWeierstrass.add pallasA
        (({ x := env.get (i₀ + 1 + 4 + 200 + 1), y := env.get (i₀ + 1 + 4 + 200 + 1 + 1) }
          : Point Fp)).coords
        (({ x := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + 190 + 4 + 2 + 2)).x,
            y := Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + 190 + 4 + 2 + 2)).y }
          : Point Fp)).coords = _
    rw [show (({ x := env.get (i₀ + 1 + 4 + 200 + 1),
                 y := env.get (i₀ + 1 + 4 + 200 + 1 + 1) } : Point Fp)).coords
      = (env.get (i₀ + 1 + 4 + 200 + 1), env.get (i₀ + 1 + 4 + 200 + 1 + 1)) from rfl,
      hpx21, hpy21, hacc20]
    show ShortWeierstrass.add pallasA ((t21 • B.point).x, (t21 • B.point).y)
        ((S20 • B.point).x, (S20 • B.point).y)
      = ((m : Fq) • B).coords
    have hpt : t21 • B.point + S20 • B.point = (m : Fq).val • B.point :=
      window21_add_partialSum_eq_nsmul B ks ht21_def hS20_def hks21 hm_def
    exact FixedBase.add_coords_eq hpt
  -- sign analysis
  simp only [h_signCopy] at h_isSign h_signSel
  refine ⟨m, hm_lt, hmag, ?_⟩
  rcases h_isSign with hsign | hsign
  · left
    refine ⟨hsign, ?_⟩
    have hyP : env.get (i₀ + 1 + 4 + 200 + 4 + 11 + 1 + 1)
        = Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + 200 + 4 + 2 + 2)).y :=
      congrArg Prod.snd ((h_signSel (0 : Fp)).1 hsign)
    rw [← hmulEq, hyP]
  · right
    refine ⟨?_, ?_⟩
    · rw [hsign]
      ring
    have hyP : env.get (i₀ + 1 + 4 + 200 + 4 + 11 + 1 + 1)
        = -(Expression.eval env (varFromOffset Point (i₀ + 1 + 4 + 200 + 4 + 2 + 2)).y) := by
      have h2 := congrArg Prod.snd ((h_signSel (0 : Fp)).2 hsign)
      simpa [ShortWeierstrass.neg] using h2
    rw [B.smul_neg, ← hmulEq, hyP]

/-- Extract the four field equations from a witnessed `RowTail`, keeping the row opaque
(see `env_get_row` in `FullWidth.lean` and `doc/performance-problems.md`). -/
private theorem env_get_rowTail {env : ProverEnvironment Fp} {n : ℕ} {r : RowTail Fp}
    (h : ({ zNext := env.get n, xP := env.get (n + 1), yP := env.get (n + 1 + 1),
            u := env.get (n + 1 + 1 + 1) } : RowTail Fp) = r) :
    env.get n = r.zNext ∧ env.get (n + 1) = r.xP ∧
      env.get (n + 1 + 1) = r.yP ∧ env.get (n + 1 + 1 + 1) = r.u :=
  ⟨congrArg RowTail.zNext h, congrArg RowTail.xP h,
    congrArg RowTail.yP h, congrArg RowTail.u h⟩

/-- The evaluated row program is the honest `rowTailValue`, stated at symbolic `w` and
an opaque magnitude `m`, where every reduction is cheap. The LHS is the `circuit_norm`
normal form of the witness-IR completeness hypothesis: `FiniteField.fromNat`/
`FiniteField.val` from `NExpr.toField`/`Expression.val`, and one range-guarded
window-table read per column from the `.listGet` evaluation (see `rowProgram_value` in
`FullWidth.lean`). -/
private theorem rowProgram_value (B : FixedBase) (m : Fp) (w : ℕ) :
    RowTail.mk (F := Fp) (FiniteField.fromNat (FiniteField.val m / 8 ^ (w + 1)))
      (if _ : FiniteField.val m / 8 ^ w % 8 < 8 then
        (windowPoint B.point w (FiniteField.val m / 8 ^ w % 8)).x else 0)
      (if _ : FiniteField.val m / 8 ^ w % 8 < 8 then
        (windowPoint B.point w (FiniteField.val m / 8 ^ w % 8)).y else 0)
      (if _ : FiniteField.val m / 8 ^ w % 8 < 8 then
        B.u w (FiniteField.val m / 8 ^ w % 8) else 0)
    = rowTailValue B m w := by
  have h8 : FiniteField.val m / 8 ^ w % 8 < 8 := Nat.mod_lt _ (by norm_num)
  simp only [dif_pos h8]
  rfl

/-- The running sum step relation on honest values. -/
private theorem zValue_step (m : Fp) (w : ℕ) :
    zValue m w = (windowVal m w : Fp) + 8 * zValue m (w + 1) := by
  unfold zValue windowVal
  rw [show m.val / 8 ^ (w + 1) = m.val / 8 ^ w / 8 by
    rw [Nat.div_div_eq_div_mul, pow_succ]]
  conv_lhs => rw [show m.val / 8 ^ w
    = m.val / 8 ^ w % 8 + 8 * (m.val / 8 ^ w / 8) by omega]
  push_cast
  ring

/-- Membership of small casts in the range-check set. -/
private theorem inRange_of_lt {k : ℕ} (hk : k < 8) :
    Utilities.RunningSum.InRange (2 ^ 3) ((k : Fp)) := by
  simp [Utilities.RunningSum.InRange, Utilities.RunningSum.rangeCheckValues,
    show (2 : ℕ) ^ 3 = 8 from rfl, List.range_succ, List.range_zero]
  interval_cases k <;> norm_num

/-- The honest running sum values satisfy the range check. -/
private theorem word_inRange (m : Fp) (w : ℕ) {a b : Fp}
    (ha : a = zValue m w) (hb : b = zValue m (w + 1)) :
    Utilities.RunningSum.InRange (2 ^ 3)
      (Utilities.RunningSum.word 3 { zCur := a, zNext := b }) := by
  have hword : Utilities.RunningSum.word 3 { zCur := a, zNext := b }
      = (windowVal m w : Fp) := by
    show a - Utilities.RunningSum.twoPowWindow 3 * b = _
    have h8 : (Utilities.RunningSum.twoPowWindow 3 : Fp) = 8 := by
      norm_num [Utilities.RunningSum.twoPowWindow]
    rw [ha, hb, h8]
    linear_combination zValue_step m w
  rw [hword]
  exact inRange_of_lt (windowVal_lt m w)

/-- The honest row values satisfy the coordinates check. -/
private theorem coordsRow_spec (B : FixedBase) (m : Fp) {w : ℕ} (hw : w < 22)
    {row : RunningSumCoords.Input Fp}
    (hzc : row.zCur = zValue m w) (hzn : row.zNext = zValue m (w + 1))
    (hx : row.xP = (windowPoint B.point w (windowVal m w)).x)
    (hy : row.yP = (windowPoint B.point w (windowVal m w)).y)
    (hu : row.u = B.u w (windowVal m w)) :
    Coords.Spec (B.params w) (RunningSumCoords.coordsRow row) := by
  have hwin : (RunningSumCoords.coordsRow row).window = (windowVal m w : Fp) := by
    show row.zCur - row.zNext * 8 = _
    rw [hzc, hzn]
    linear_combination zValue_step m w
  refine ⟨?_, ?_, ?_⟩
  · rw [show (RunningSumCoords.coordsRow row).xP = row.xP from rfl, hx,
      interpolatedX, hwin, B.interpolate_eq w hw _ (windowVal_lt m w)]
  · rw [show (RunningSumCoords.coordsRow row).u = row.u from rfl,
      show (RunningSumCoords.coordsRow row).yP = row.yP from rfl, hu, hy]
    exact B.u_mul_u w hw _ (windowVal_lt m w)
  · rw [show (RunningSumCoords.coordsRow row).yP = row.yP from rfl,
      show (RunningSumCoords.coordsRow row).xP = row.xP from rfl, hx, hy]
    have h := B.windowPoint_onCurve (w := w) (k := windowVal m w) (windowVal_lt m w)
    dsimp [Point.OnCurve] at h
    linear_combination h

private theorem honest_acc_step (B : FixedBase) (env : ProverEnvironment Fp)
    (i₀ : ℕ) (m : Fp)
    (hx : ∀ (j : ℕ), j < 20 →
      env.get (i₀ + 1 + 4 + j * 10 + 1) = (rowTailValue B m (j + 1)).xP)
    (hy : ∀ (j : ℕ), j < 20 →
      env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) = (rowTailValue B m (j + 1)).yP)
    (h_step : ∀ (j : ℕ) (_ : j < 20),
      ({ x := env.get (i₀ + 1 + 4 + j * 10 + 1),
         y := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) } : Point Fp).OnCurve ∧
        (accPt env.toEnvironment i₀ j).OnCurve ∧
        ¬env.get (i₀ + 1 + 4 + j * 10 + 1) = (accPt env.toEnvironment i₀ j).x →
      (accPt env.toEnvironment i₀ (j + 1)).OnCurve ∧
        accPt env.toEnvironment i₀ (j + 1) =
          { x := env.get (i₀ + 1 + 4 + j * 10 + 1),
            y := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) } +
            accPt env.toEnvironment i₀ j) :
    ∀ (j : ℕ), j < 20 →
      accPt env.toEnvironment i₀ j = partialSum (windowVal m) j • B.point →
      accPt env.toEnvironment i₀ (j + 1) =
        windowPoint B.point (j + 1) (windowVal m (j + 1)) +
          accPt env.toEnvironment i₀ j := by
  intro j hj hacc
  set t := (windowScalar (j + 1) (windowVal m (j + 1))).val with ht_def
  have hval : t = (windowVal m (j + 1) + 2) * 8 ^ (j + 1) :=
    windowScalar_val (by omega) (windowVal_lt m (j + 1))
  have hS_lt := partialSum_lt (windowVal m) j
    fun _ _ => windowVal_lt m _
  have hS_pos := partialSum_pos (windowVal m) j
  have ht_lower : 2 * 8 ^ (j + 1) ≤ t := by
    rw [hval]
    exact Nat.mul_le_mul_right _ (by omega)
  have ht_upper : t ≤ 9 * 8 ^ (j + 1) := by
    rw [hval]
    exact Nat.mul_le_mul_right _ (by
      have := windowVal_lt m (j + 1)
      omega)
  have hS_card := inv_lt_card hS_lt (by omega)
  have hsum_card := step_sum_lt hS_lt ht_upper (by omega)
  have hpx : env.get (i₀ + 1 + 4 + j * 10 + 1) = (t • B.point).x := by
    rw [hx j hj]
    rfl
  have hpy : env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) = (t • B.point).y := by
    rw [hy j hj]
    rfl
  have h_spec := h_step j hj ⟨by
      rw [hpx, hpy]
      exact B.nsmul_onCurve
        (Nat.lt_of_lt_of_le
          (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _)) ht_lower)
        (by omega),
    by
      rw [hacc]
      exact B.nsmul_onCurve hS_pos hS_card,
    by
      rw [hpx, hacc]
      show (t • B.point).x ≠ (partialSum (windowVal m) j • B.point).x
      exact B.nsmul_x_ne hS_pos (Nat.lt_of_lt_of_le hS_lt ht_lower) hsum_card⟩
  rw [h_spec.2, hpx, hpy, hacc]
  unfold windowPoint
  rw [ht_def]

private theorem honest_loop_constraints (B : FixedBase) (env : ProverEnvironment Fp)
    (i₀ : ℕ) (m : Fp)
    (hx : ∀ (j : ℕ), j < 20 →
      env.get (i₀ + 1 + 4 + j * 10 + 1) = (rowTailValue B m (j + 1)).xP)
    (hy : ∀ (j : ℕ), j < 20 →
      env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) = (rowTailValue B m (j + 1)).yP)
    (hu : ∀ (j : ℕ), j < 20 →
      env.get (i₀ + 1 + 4 + j * 10 + 1 + 1 + 1) = (rowTailValue B m (j + 1)).u)
    (hzCell : ∀ (j : ℕ), j ≤ 20 →
      env.get (zCell i₀ j) = zValue m (j + 1))
    (h_inv : ∀ (w : ℕ), w ≤ 20 →
      accPt env.toEnvironment i₀ w = partialSum (windowVal m) w • B.point) :
    ∀ (j : ℕ) (_ : j < 20),
      Utilities.RunningSum.InRange (2 ^ 3) (Utilities.RunningSum.word 3
        { zCur := env.get (zCell i₀ j), zNext := env.get (i₀ + 1 + 4 + j * 10) }) ∧
      Coords.Spec (B.params (j + 1)) (RunningSumCoords.coordsRow
        { zCur := env.get (zCell i₀ j), zNext := env.get (i₀ + 1 + 4 + j * 10),
          xP := env.get (i₀ + 1 + 4 + j * 10 + 1),
          yP := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1),
          u := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1 + 1) }) ∧
      ({ x := env.get (i₀ + 1 + 4 + j * 10 + 1),
         y := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) } : Point Fp).OnCurve ∧
      (accPt env.toEnvironment i₀ j).OnCurve ∧
      ¬env.get (i₀ + 1 + 4 + j * 10 + 1) = (accPt env.toEnvironment i₀ j).x := by
  intro j hj
  have hzc : env.get (zCell i₀ j) = zValue m (j + 1) := hzCell j (by omega)
  have hzn : env.get (i₀ + 1 + 4 + j * 10) = zValue m (j + 1 + 1) := by
    show env.get (zCell i₀ (j + 1)) = _
    exact hzCell (j + 1) (by omega)
  have hacc := h_inv j (by omega)
  have hS_lt := partialSum_lt (windowVal m) j
    fun _ _ => windowVal_lt m _
  have hS_pos := partialSum_pos (windowVal m) j
  have hS_card := inv_lt_card hS_lt (by omega)
  set t := (windowScalar (j + 1) (windowVal m (j + 1))).val with ht_def
  have hval : t = (windowVal m (j + 1) + 2) * 8 ^ (j + 1) :=
    windowScalar_val (by omega) (windowVal_lt m (j + 1))
  have ht_lower : 2 * 8 ^ (j + 1) ≤ t := by
    rw [hval]
    exact Nat.mul_le_mul_right _ (by omega)
  have ht_upper : t ≤ 9 * 8 ^ (j + 1) := by
    rw [hval]
    exact Nat.mul_le_mul_right _ (by
      have := windowVal_lt m (j + 1)
      omega)
  have hsum_card := step_sum_lt hS_lt ht_upper (by omega)
  have hpx : env.get (i₀ + 1 + 4 + j * 10 + 1) = (t • B.point).x := by
    rw [hx j hj]
    rfl
  have hpy : env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) = (t • B.point).y := by
    rw [hy j hj]
    rfl
  refine ⟨word_inRange m (j + 1) hzc hzn, ?_, ?_, ?_, ?_⟩
  · exact coordsRow_spec B m (by omega) hzc hzn
      (by exact hx j hj)
      (by exact hy j hj)
      (by exact hu j hj)
  · rw [hpx, hpy]
    exact B.nsmul_onCurve
      (Nat.lt_of_lt_of_le
        (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _)) ht_lower)
      (by omega)
  · rw [hacc]
    exact B.nsmul_onCurve hS_pos hS_card
  · rw [hpx, hacc]
    show (t • B.point).x ≠ (partialSum (windowVal m) j • B.point).x
    exact B.nsmul_x_ne hS_pos
      (Nat.lt_of_lt_of_le hS_lt ht_lower) hsum_card

private theorem signed_y_eq_of_gate
    {sign yA yP : Fp} (hyP : yP = sign * yA) :
    (sign = 1 → yP = yA) ∧ (sign = -1 → yP = -yA) := by
  constructor
  · intro hs
    rw [hyP, hs, one_mul]
  · intro hs
    rw [hyP, hs]
    ring

private theorem signed_output_spec (B : FixedBase) {m : ℕ}
    {sign x y ySigned : Fp}
    (hmulEq : ({ x := x, y := y } : Point Fp) = ((m : Fq) • B))
    (hySigned_pos : sign = 1 → ySigned = y)
    (hySigned_neg : sign = -1 → ySigned = -y) :
    (sign = 1 → ({ x := x, y := ySigned } : Point Fp) = (m : Fq) • B) ∧
      (sign = -1 → ({ x := x, y := ySigned } : Point Fp) = ((-(m : Fq)) : Fq) • B) := by
  constructor
  · intro hs
    rw [hySigned_pos hs]
    exact hmulEq
  · intro hs
    rw [B.smul_neg, ← hmulEq, hySigned_neg hs]

/-- The running sum starts at the magnitude itself. -/
private theorem zValue_zero (m : Fp) : zValue m 0 = m := by
  unfold zValue
  rw [pow_zero, Nat.div_one, ZMod.natCast_zmod_val]

/-- The strict running sum terminates at zero for a 64-bit magnitude. -/
private theorem zValue_22_eq_zero {m : Fp} (hm : m.val < 2 ^ 64) : zValue m 22 = 0 := by
  unfold zValue
  rw [Nat.div_eq_of_lt (by norm_num; omega)]
  exact Nat.cast_zero

/-- The last window of a 64-bit magnitude is a bit. -/
private theorem zValue_21_isBool {m : Fp} (hm : m.val < 2 ^ 64) : IsBool (zValue m 21) := by
  have hdiv : m.val / 8 ^ 21 = 0 ∨ m.val / 8 ^ 21 = 1 := by
    have h8 : (8 : ℕ) ^ 21 = 2 ^ 63 := by norm_num
    have : m.val / 8 ^ 21 < 2 := by omega
    omega
  unfold zValue
  rcases hdiv with h | h <;> rw [h]
  · exact Or.inl Nat.cast_zero
  · exact Or.inr Nat.cast_one

/-- Base-8 digit recombination of the magnitude. -/
private theorem sum_windowVal {m : Fp} (hm : m.val < 2 ^ 64) :
    ∑ j ∈ Finset.range 22, windowVal m j * 8 ^ j = m.val := by
  unfold windowVal
  have h := sum_base8 m.val 22
  rwa [Nat.mod_eq_of_lt (by norm_num; omega)] at h

-- TODO(4.30 bump): legacy defeq so `circuit_norm`'s witness-IR completeness lemmas
-- (`extendsVector_toIRLiteral` etc.) keep matching through stuck `size`/`localLength`
-- indices (lean4#12179).
set_option backward.isDefEq.respectTransparency false in
theorem completeness (B : FixedBase) :
    GeneralFormalCircuit.Completeness Fp (main B) ProverAssumptions (ProverSpec B) := by
  circuit_proof_start [rowProgram, Gate.circuit, Gate.Spec,
    Gate.IsSign, Gate.SignedPointSelection,
    Utilities.RunningSum.circuit, Utilities.RunningSum.Spec,
    RunningSumCoords.circuit, RunningSumCoords.Spec,
    AddIncomplete.circuit, AddIncomplete.Spec, AddIncomplete.Assumptions,
    Add.circuit, Add.Spec, Add.Assumptions]
  obtain ⟨hm_lt, h_sign⟩ := h_assumptions
  obtain ⟨h_z0w, h_t0, h_loop_env, h_t21, h_add_env, h_signw, h_lastww, h_yPw⟩ := h_env
  simp +instances only [List.sum_cons, List.sum_nil, Nat.reduceAdd, Nat.reduceMul,
    circuit_norm]
    at h_add_env h_signw h_lastww h_yPw ⊢
  rw [Nat.add_comm 200 (i₀ + 1 + 4)] at h_signw h_lastww h_yPw
  -- witnessed row values
  obtain ⟨h0z, h0x, h0y, h0u⟩ :=
    env_get_rowTail (h_t0.trans (rowProgram_value B input_magnitude 0))
  have hrow : ∀ (j : ℕ) (hj : j < 20),
      env.get (i₀ + 1 + 4 + j * 10) = (rowTailValue B input_magnitude (j + 1)).zNext ∧
        env.get (i₀ + 1 + 4 + j * 10 + 1) = (rowTailValue B input_magnitude (j + 1)).xP ∧
        env.get (i₀ + 1 + 4 + j * 10 + 1 + 1)
          = (rowTailValue B input_magnitude (j + 1)).yP ∧
        env.get (i₀ + 1 + 4 + j * 10 + 1 + 1 + 1)
          = (rowTailValue B input_magnitude (j + 1)).u :=
    fun j hj => by
      rcases j with _ | j'
      · exact env_get_rowTail
          (h_loop_env.1.1.trans (rowProgram_value B input_magnitude 1))
      · exact env_get_rowTail
          ((h_loop_env.2 j' (by omega)).1.trans
            (rowProgram_value B input_magnitude (j' + 1 + 1)))
  have h21 : env.get (200 + (i₀ + 1 + 4)) = (rowTailValue B input_magnitude 21).zNext ∧
      env.get (200 + (i₀ + 1 + 4) + 1) = (rowTailValue B input_magnitude 21).xP ∧
        env.get (200 + (i₀ + 1 + 4) + 1 + 1) = (rowTailValue B input_magnitude 21).yP ∧
        env.get (200 + (i₀ + 1 + 4) + 1 + 1 + 1) = (rowTailValue B input_magnitude 21).u :=
    env_get_rowTail (h_t21.trans (rowProgram_value B input_magnitude 21))
  rw [Nat.add_comm 200 (i₀ + 1 + 4)] at h21
  obtain ⟨h21z, h21x, h21y, h21u⟩ := h21
  -- the z-chain cells in honest form
  have hzCell : ∀ (j : ℕ), j ≤ 20 →
      env.get (zCell i₀ j) = zValue input_magnitude (j + 1) := by
    intro j hj
    rcases j with _ | j'
    · exact h0z.trans (rowTailValue_zNext B input_magnitude 0)
    · exact ((hrow j' (by omega)).1).trans (rowTailValue_zNext B input_magnitude (j' + 1))
  have hz22cell : env.get (i₀ + 1 + 4 + 200) = zValue input_magnitude 22 :=
    h21z.trans (rowTailValue_zNext B input_magnitude 21)
  -- per-iteration incomplete addition implication, cleaned up
  have h_step' : ∀ (j : ℕ) (hj : j < 20),
      ({ x := env.get (i₀ + 1 + 4 + j * 10 + 1),
         y := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) } : Point Fp).OnCurve ∧
        (accPt env.toEnvironment i₀ j).OnCurve ∧
        ¬env.get (i₀ + 1 + 4 + j * 10 + 1) = (accPt env.toEnvironment i₀ j).x →
      (accPt env.toEnvironment i₀ (j + 1)).OnCurve ∧
        accPt env.toEnvironment i₀ (j + 1) =
          { x := env.get (i₀ + 1 + 4 + j * 10 + 1),
            y := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) } +
            accPt env.toEnvironment i₀ j := by
    intro j hj
    rcases j with _ | j'
    · simpa only [accPt, Nat.zero_mul, Nat.add_zero, Nat.reduceAdd, circuit_norm]
        using h_loop_env.1.2
    · simpa only [accPt, Nat.reduceAdd, circuit_norm]
        using (h_loop_env.2 j' (by omega)).2
  clear h_loop_env
  have h_acc0 :
      accPt env.toEnvironment i₀ 0 = windowPoint B.point 0 (windowVal input_magnitude 0) := by
    show ({ x := env.get (i₀ + 1 + 1), y := env.get (i₀ + 1 + 1 + 1) } : Point Fp) = _
    rw [h0x, h0y, rowTailValue_xP, rowTailValue_yP]
  have h_acc_step : ∀ (j : ℕ), j < 20 →
      accPt env.toEnvironment i₀ j =
        partialSum (windowVal input_magnitude) j • B.point →
      accPt env.toEnvironment i₀ (j + 1) =
        windowPoint B.point (j + 1) (windowVal input_magnitude (j + 1)) +
          accPt env.toEnvironment i₀ j :=
    honest_acc_step B env i₀ input_magnitude
      (fun j hj => (hrow j hj).2.1)
      (fun j hj => (hrow j hj).2.2.1)
      h_step'
  have h_inv : ∀ (w : ℕ), w ≤ 20 →
      accPt env.toEnvironment i₀ w =
        partialSum (windowVal input_magnitude) w • B.point :=
    acc_eq_partialSum_nsmul B (accPt env.toEnvironment i₀) (windowVal input_magnitude)
      (fun w => windowVal_lt input_magnitude w) h_acc0 h_acc_step
  clear h_acc0 h_acc_step
  clear h_step'
  -- per-iteration constraint obligations
  have hB : ∀ (j : ℕ) (hj : j < 20),
      Utilities.RunningSum.InRange (2 ^ 3) (Utilities.RunningSum.word 3
        { zCur := env.get (zCell i₀ j), zNext := env.get (i₀ + 1 + 4 + j * 10) }) ∧
      Coords.Spec (B.params (j + 1)) (RunningSumCoords.coordsRow
        { zCur := env.get (zCell i₀ j), zNext := env.get (i₀ + 1 + 4 + j * 10),
          xP := env.get (i₀ + 1 + 4 + j * 10 + 1),
          yP := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1),
          u := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1 + 1) }) ∧
      ({ x := env.get (i₀ + 1 + 4 + j * 10 + 1),
         y := env.get (i₀ + 1 + 4 + j * 10 + 1 + 1) } : Point Fp).OnCurve ∧
      (accPt env.toEnvironment i₀ j).OnCurve ∧
      ¬env.get (i₀ + 1 + 4 + j * 10 + 1) = (accPt env.toEnvironment i₀ j).x :=
    honest_loop_constraints B env i₀ input_magnitude
      (fun j hj => (hrow j hj).2.1)
      (fun j hj => (hrow j hj).2.2.1)
      (fun j hj => (hrow j hj).2.2.2)
      hzCell h_inv
  clear hrow h_t0 h_t21 h_input
  -- window 21 values, kept opaque for kernel-cheap defeq (`doc/performance-problems.md`)
  obtain ⟨t21, ht21_def⟩ : ∃ t : ℕ,
      t = (windowScalar 21 (windowVal input_magnitude 21)).val := ⟨_, rfl⟩
  have hP21_eq : windowPoint B.point 21 (windowVal input_magnitude 21) = t21 • B.point := by
    rw [ht21_def]
    rfl
  have hpx21 : env.get (i₀ + 1 + 4 + 200 + 1) = (t21 • B.point).x := by
    rw [h21x, rowTailValue_xP, hP21_eq]
  have hpy21 : env.get (i₀ + 1 + 4 + 200 + 1 + 1) = (t21 • B.point).y := by
    rw [h21y, rowTailValue_yP, hP21_eq]
  obtain ⟨S20, hS20_def⟩ : ∃ S : ℕ, S = partialSum (windowVal input_magnitude) 20 :=
    ⟨_, rfl⟩
  have hS_lt : S20 < 2 * 8 ^ (20 + 1) := by
    rw [hS20_def]
    exact partialSum_lt (windowVal input_magnitude) 20
      fun _ _ => windowVal_lt input_magnitude _
  have hS_pos : 0 < S20 := by
    rw [hS20_def]
    exact partialSum_pos (windowVal input_magnitude) 20
  have hS_card := inv_lt_card hS_lt (by omega)
  have hacc20 :
        ({ x := Expression.eval env.toEnvironment
              (varFromOffset Point (i₀ + 1 + 4 + 190 + 4 + 2 + 2)).x,
           y := Expression.eval env.toEnvironment
              (varFromOffset Point (i₀ + 1 + 4 + 190 + 4 + 2 + 2)).y } : Point Fp)
        = S20 • B.point := by
    change accPt env.toEnvironment i₀ 20 = S20 • B.point
    rw [hS20_def]
    exact h_inv 20 (by omega)
  have hValidP :
      ({ x := env.get (i₀ + 1 + 4 + 200 + 1),
         y := env.get (i₀ + 1 + 4 + 200 + 1 + 1) } : Point Fp).Valid := by
    rw [hpx21, hpy21]
    exact Point.valid_nsmul (.inl B.onCurve) t21
  have hValidAcc :
      ({ x := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 190 + 4 + 2 + 2)).x,
          y := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 190 + 4 + 2 + 2)).y } : Point Fp).Valid := by
    rw [hacc20]
    exact Point.valid_nsmul (.inl B.onCurve) S20
  have h_final := h_add_env ⟨hValidP, hValidAcc⟩
  have hmulEq :
      ({ x := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 200 + 4 + 2 + 2)).x,
         y := Expression.eval env.toEnvironment
            (varFromOffset Point (i₀ + 1 + 4 + 200 + 4 + 2 + 2)).y } : Point Fp)
      = ((input_magnitude.val : ℕ) : Fq) • B := by
    apply Point.ext_coords
    rw [h_final.2]
    show ShortWeierstrass.add pallasA
        (({ x := env.get (i₀ + 1 + 4 + 200 + 1), y := env.get (i₀ + 1 + 4 + 200 + 1 + 1) }
          : Point Fp)).coords
        (({ x := Expression.eval env.toEnvironment
              (varFromOffset Point (i₀ + 1 + 4 + 190 + 4 + 2 + 2)).x,
            y := Expression.eval env.toEnvironment
              (varFromOffset Point (i₀ + 1 + 4 + 190 + 4 + 2 + 2)).y } : Point Fp)).coords = _
    rw [show (({ x := env.get (i₀ + 1 + 4 + 200 + 1),
                 y := env.get (i₀ + 1 + 4 + 200 + 1 + 1) } : Point Fp)).coords
      = (env.get (i₀ + 1 + 4 + 200 + 1), env.get (i₀ + 1 + 4 + 200 + 1 + 1)) from rfl,
      hpx21, hpy21, hacc20]
    show ShortWeierstrass.add pallasA ((t21 • B.point).x, (t21 • B.point).y)
        ((S20 • B.point).x, (S20 • B.point).y)
      = (((input_magnitude.val : ℕ) : Fq) • B).coords
    have hpt : t21 • B.point + S20 • B.point
        = ((input_magnitude.val : ℕ) : Fq).val • B.point :=
      window21_add_partialSum_eq_nsmul B (windowVal input_magnitude) ht21_def hS20_def rfl
        (sum_windowVal hm_lt).symm
    exact FixedBase.add_coords_eq hpt
  have hSignedOutput := signed_output_spec B (m := input_magnitude.val)
    (sign := input_sign)
    (x := Expression.eval env.toEnvironment
      (varFromOffset Point (i₀ + 1 + 4 + 200 + 4 + 2 + 2)).x)
    (y := Expression.eval env.toEnvironment
      (varFromOffset Point (i₀ + 1 + 4 + 200 + 4 + 2 + 2)).y)
    (ySigned := env.get (i₀ + 1 + 4 + 200 + 4 + 11 + 1 + 1))
    (hmulEq := hmulEq)
    (hySigned_pos := by
      intro hs
      rw [h_yPw, hs, one_mul])
    (hySigned_neg := by
      intro hs
      rw [h_yPw, hs]
      ring)
  -- assemble the constraints and the prover spec
  refine ⟨⟨h_z0w, ?_, ?_, ?_, ?_, ?_, ?_, ⟨hValidP, hValidAcc⟩, h_signw, h_lastww,
    ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact word_inRange input_magnitude 0
      (by rw [h_z0w]; exact (zValue_zero input_magnitude).symm)
      (hzCell 0 (Nat.zero_le _))
  · exact coordsRow_spec B input_magnitude (by norm_num)
      (by rw [h_z0w]; exact (zValue_zero input_magnitude).symm)
      (hzCell 0 (Nat.zero_le _))
      (h0x.trans (rowTailValue_xP B input_magnitude 0))
      (h0y.trans (rowTailValue_yP B input_magnitude 0))
      (h0u.trans (rowTailValue_u B input_magnitude 0))
  · constructor
    · simpa only [zCell, accPt, Nat.zero_mul, Nat.add_zero, Nat.reduceAdd, circuit_norm]
        using hB 0 (by omega)
    · intro i hi
      simpa only [zCell, accPt, Nat.reduceAdd, circuit_norm]
        using hB (i + 1) (by omega)
  · exact word_inRange input_magnitude 21
      (show env.get (zCell i₀ 20) = _ from hzCell 20 le_rfl) hz22cell
  · exact coordsRow_spec B input_magnitude (by norm_num)
      (show env.get (zCell i₀ 20) = _ from hzCell 20 le_rfl) hz22cell
      (h21x.trans (rowTailValue_xP B input_magnitude 21))
      (h21y.trans (rowTailValue_yP B input_magnitude 21))
      (h21u.trans (rowTailValue_u B input_magnitude 21))
  · rw [hz22cell]
    exact zValue_22_eq_zero hm_lt
  · rw [h_lastww, show env.get (i₀ + 1 + 4 + 190) = env.get (zCell i₀ 20) from rfl,
      hzCell 20 le_rfl]
    exact zValue_21_isBool hm_lt
  · rw [h_signw]
    rcases h_sign with h | h
    · exact Or.inl h
    · right
      change input_sign = 0 - 1
      rw [h]
      ring
  · exact fun x => by
      constructor
      · intro hs
        rw [h_signw] at hs
        have hyP : env.get (i₀ + 1 + 4 + 200 + 4 + 11 + 1 + 1)
            = Expression.eval env.toEnvironment
              (varFromOffset Point (i₀ + 1 + 4 + 200 + 4 + 2 + 2)).y := by
          rw [h_yPw, hs, one_mul]
        rw [hyP]
      · intro hs
        rw [h_signw] at hs
        have hyP : env.get (i₀ + 1 + 4 + 200 + 4 + 11 + 1 + 1)
            = -(Expression.eval env.toEnvironment
              (varFromOffset Point (i₀ + 1 + 4 + 200 + 4 + 2 + 2)).y) := by
          rw [h_yPw, hs]
          ring
        rw [hyP]
        rfl
  · exact hSignedOutput.1
  · exact hSignedOutput.2

def circuit (B : FixedBase) : GeneralFormalCircuit Fp MagnitudeSign Point where
  main := main B
  Spec := Spec B
  ProverAssumptions := ProverAssumptions
  ProverSpec := ProverSpec B
  soundness := soundness B
  completeness := completeness B

end Orchard.Ecc.MulFixed.Short
