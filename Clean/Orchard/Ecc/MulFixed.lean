import Clean.Orchard.Ecc.Defs

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul_fixed.rs`.
-/

namespace Orchard.Ecc.MulFixed

structure CoordsParams (F : Type) where
  z : F
  lagrange0 : F
  lagrange1 : F
  lagrange2 : F
  lagrange3 : F
  lagrange4 : F
  lagrange5 : F
  lagrange6 : F
  lagrange7 : F

def CoordsParams.toExpr (params : CoordsParams Fp) :
    CoordsParams (Expression Fp) where
  z := params.z
  lagrange0 := params.lagrange0
  lagrange1 := params.lagrange1
  lagrange2 := params.lagrange2
  lagrange3 := params.lagrange3
  lagrange4 := params.lagrange4
  lagrange5 := params.lagrange5
  lagrange6 := params.lagrange6
  lagrange7 := params.lagrange7

structure CoordsRow (F : Type) where
  window : F
  xP : F
  yP : F
  u : F
deriving ProvableStruct

def interpolate {K : Type} [Add K] [Mul K] (params : CoordsParams K) (window : K) : K :=
  params.lagrange0 +
    window * params.lagrange1 +
    window * window * params.lagrange2 +
    window * window * window * params.lagrange3 +
    window * window * window * window * params.lagrange4 +
    window * window * window * window * window * params.lagrange5 +
    window * window * window * window * window * window * params.lagrange6 +
    window * window * window * window * window * window * window *
      params.lagrange7

def interpolatedX {K : Type} [Add K] [Mul K] (params : CoordsParams K) (row : CoordsRow K) : K :=
  interpolate params row.window

def xCheck {K : Type} [Add K] [Sub K] [Mul K] (params : CoordsParams K) (row : CoordsRow K) :
    K :=
  interpolatedX params row - row.xP

def yCheck {K : Type} [Sub K] [Mul K] (params : CoordsParams K) (row : CoordsRow K) : K :=
  row.u * row.u - row.yP - params.z

def onCurve {K : Type} [Sub K] [Mul K] [OfNat K 5] (row : CoordsRow K) : K :=
  row.yP * row.yP - row.xP * row.xP * row.xP - 5

namespace Coords

def Spec (params : CoordsParams Fp) (row : CoordsRow Fp) :
    Prop :=
  row.xP = interpolatedX params row ∧
    row.u * row.u = row.yP + params.z ∧
    row.yP * row.yP = row.xP * row.xP * row.xP + 5

def main (params : CoordsParams Fp) (row : Var CoordsRow Fp) :
    Circuit Fp Unit := do
  assertZero (xCheck params.toExpr row)
  assertZero (yCheck params.toExpr row)
  assertZero (onCurve row)

def circuit (params : CoordsParams Fp) :
    FormalAssertion Fp CoordsRow where
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [main, Spec, xCheck, yCheck, onCurve, interpolatedX, interpolate]
    rcases h_holds with ⟨hx, hy, hCurve⟩
    simp [CoordsParams.toExpr, circuit_norm] at hx hy
    exact ⟨(sub_eq_zero.mp (by simpa [sub_eq_add_neg] using hx)).symm,
      by linear_combination hy,
      by linear_combination hCurve⟩
  completeness := by
    circuit_proof_start [main, Spec, xCheck, yCheck, onCurve, interpolatedX, interpolate]
    rcases h_spec with ⟨hx, hy, hCurve⟩
    simp [CoordsParams.toExpr, circuit_norm]
    exact ⟨by simpa [sub_eq_add_neg] using sub_eq_zero.mpr hx.symm,
      by linear_combination hy,
      by linear_combination hCurve⟩

end Coords

namespace RunningSumCoords

/-- The advice cells queried by the gate: the running sum `z` values in the `window`
column at the current and next row, and the window-table point cells of the current
row. The window value itself is not a cell; it is derived as `z_cur - z_next · 8`. -/
structure Input (F : Type) where
  zCur : F
  zNext : F
  xP : F
  yP : F
  u : F
deriving ProvableStruct

def word {K : Type} [Sub K] [Mul K] [OfNat K 8] (row : Input K) : K :=
  row.zCur - row.zNext * 8

def coordsRow {K : Type} [Sub K] [Mul K] [OfNat K 8] (row : Input K) : CoordsRow K :=
  { window := word row, xP := row.xP, yP := row.yP, u := row.u }

def Spec (params : CoordsParams Fp) (row : Input Fp) : Prop :=
  Coords.Spec params (coordsRow row)

def main (params : CoordsParams Fp) (row : Var Input Fp) :
    Circuit Fp Unit := do
  Coords.circuit params { window := word row, xP := row.xP, yP := row.yP, u := row.u }

def circuit (params : CoordsParams Fp) : FormalAssertion Fp Input where
  name := "GATE Running sum coordinates check"
  main := main params
  Spec := Spec params
  soundness := by
    circuit_proof_start [main, Spec, coordsRow, Coords.circuit, Coords.Spec, word]
    simpa [sub_eq_add_neg] using h_holds
  completeness := by
    circuit_proof_start [main, Spec, coordsRow, Coords.circuit, Coords.Spec, word]
    simpa [sub_eq_add_neg] using h_spec

end RunningSumCoords

/-!
### Fixed bases

A `FixedBase` models a halo2 `FixedPoint<pallas::Affine>` impl for a full-width scalar
(`ecc/chip.rs`, `FixedScalarKind = FullScalar`): the generator together with its
precomputed per-window constants (`lagrange_coeffs()`, `z()`, `u()` from
`ecc/chip/constants.rs`) and the correctness properties of those constants that halo2
enforces out-of-circuit via `test_lagrange_coeffs` / `test_zs_and_us`.
-/

open CompElliptic.Curves.Pasta CompElliptic.CurveForms
open ShortWeierstrass (SWPoint)
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

/-- `offset_acc`: the accumulated initialization offset
`∑_{j=0}^{83} 2^{3j+1}` subtracted in the most significant window
(`mul_fixed.rs::process_msb`). -/
def offsetAcc : ℕ := ∑ j ∈ Finset.range 84, 2 ^ (3 * j + 1)

/-- The scalar multiple contributed by window `w` holding value `k`:
`(k + 2)·8^w` for the lower 84 windows, `k·8^84 - offset_acc` for the most
significant window (`compute_window_table` in `ecc/chip/constants.rs`). -/
def windowScalar (w k : ℕ) : Fq :=
  if w = 84 then (k : Fq) * 8 ^ 84 - (offsetAcc : Fq) else ((k : Fq) + 2) * 8 ^ w

/-- The window-table point for window `w` and window value `k`. -/
def windowPoint (point : Point Fp) (w k : ℕ) : Point Fp :=
  (windowScalar w k).val • point

theorem windowScalar_ne_zero {w k : ℕ} (hk : k < 8) :
    windowScalar w k ≠ 0 := by
  have hcard : 9 < PALLAS_SCALAR_CARD := by norm_num [PALLAS_SCALAR_CARD]
  unfold windowScalar
  by_cases h84 : w = 84
  · rw [if_pos h84]
    interval_cases k <;> native_decide
  · rw [if_neg h84]
    apply mul_ne_zero
    · rw [show (k : Fq) + 2 = ((k + 2 : ℕ) : Fq) by push_cast; ring,
        Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      have := Nat.le_of_dvd (by omega) hdvd
      omega
    · exact pow_ne_zero _ (by decide)

theorem windowScalar_val {w k : ℕ} (hw : w < 84) (hk : k < 8) :
    (windowScalar w k).val = (k + 2) * 8 ^ w := by
  have hbound : (k + 2) * 8 ^ w < PALLAS_SCALAR_CARD := by
    calc (k + 2) * 8 ^ w ≤ 9 * 8 ^ 83 :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) (by omega))
      _ < PALLAS_SCALAR_CARD := by norm_num [PALLAS_SCALAR_CARD]
  unfold windowScalar
  rw [if_neg (by omega),
    show ((k : Fq) + 2) * 8 ^ w = (((k + 2) * 8 ^ w : ℕ) : Fq) by push_cast; ring,
    ZMod.val_natCast_of_lt hbound]

/-- `∑_{j ≤ w} (ks j + 2)·8^j`: the scalar accumulated after windows `0..w`, where each
window `j` contributes `(ks j + 2)·8^j` (`mul_fixed.rs::process_lower_bits`). -/
def partialSum (ks : ℕ → ℕ) : ℕ → ℕ
  | 0 => ks 0 + 2
  | w + 1 => partialSum ks w + (ks (w + 1) + 2) * 8 ^ (w + 1)

theorem partialSum_pos (ks : ℕ → ℕ) (w : ℕ) : 0 < partialSum ks w := by
  cases w with
  | zero => simp [partialSum]
  | succ w => simp [partialSum]

theorem partialSum_lt (ks : ℕ → ℕ) :
    ∀ w, (∀ j ≤ w, ks j < 8) → partialSum ks w < 2 * 8 ^ (w + 1)
  | 0, h => by
    have := h 0 (by omega)
    simp only [partialSum]
    omega
  | w + 1, h => by
    have ih := partialSum_lt ks w fun j hj => h j (by omega)
    have hk := h (w + 1) (by omega)
    have hmul : (ks (w + 1) + 2) * 8 ^ (w + 1) ≤ 10 * 8 ^ (w + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have h16 : 2 * 8 ^ (w + 1 + 1) = 16 * 8 ^ (w + 1) := by ring
    simp only [partialSum]
    omega

theorem partialSum_eq_sum (ks : ℕ → ℕ) :
    ∀ w, partialSum ks w = ∑ j ∈ Finset.range (w + 1), (ks j + 2) * 8 ^ j
  | 0 => by simp [partialSum]
  | w + 1 => by rw [partialSum, partialSum_eq_sum ks w, ← Finset.sum_range_succ]

theorem sum_base8 (n : ℕ) :
    ∀ m, ∑ j ∈ Finset.range m, n / 8 ^ j % 8 * 8 ^ j = n % 8 ^ m
  | 0 => by simp [Nat.mod_one]
  | m + 1 => by
    rw [Finset.sum_range_succ, sum_base8 n m, Nat.mod_pow_succ]
    ring

/--
A fixed base for full-width fixed-base scalar multiplication: a generator of the Pallas
prime-order group together with its precomputed window tables.

- `params w` holds the fixed columns of window `w`: the eight Lagrange interpolation
  coefficients of the window's `x`-coordinates and the y-sign-fixing constant `z`.
- `u w k` is the witnessed square root with `u² = y + z` for the window-table point.

The correctness properties are exactly the halo2 fixed-base invariants
(`test_lagrange_coeffs`, `test_zs_and_us`), plus the fact that the generator has the
full prime order `q` of the Pallas group.
-/
structure FixedBase where
  point : Point Fp
  onCurve : point.OnCurve
  params : ℕ → CoordsParams Fp
  u : ℕ → ℕ → Fp
  interpolate_eq : ∀ (w : ℕ), w < 85 → ∀ (k : ℕ), k < 8 →
    interpolate (params w) (k : Fp) = (windowPoint point w k).x
  u_mul_u : ∀ (w : ℕ), w < 85 → ∀ (k : ℕ), k < 8 →
    u w k * u w k = (windowPoint point w k).y + (params w).z
  z_sub_y_not_square : ∀ (w : ℕ), w < 85 → ∀ (k : ℕ), k < 8 →
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

/--
The collision-freedom fact behind the incomplete additions of fixed-base scalar
multiplication: distinct small positive multiples of the generator have distinct
`x`-coordinates, since equal `x` would force equal-or-opposite points and hence a
relation `t ∓ s ≡ 0` modulo the (large) group order.
-/
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

/-- The value-level result of multiplying the fixed base by a full-width scalar. -/
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

/--
Soundness of one window row: if the coordinates gate holds on a row whose window value
is `k < 8`, then the row's point is exactly the window-table point. The interpolation
property pins `x`, the curve equation restricts `y` to a sign, and the square-root
check `u² = y + z` excludes the wrong sign since `z - y` is a non-square.
-/
theorem coords_eq_windowPoint {w k : ℕ} (hw : w < 85) (hk : k < 8)
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

end Orchard.Ecc.MulFixed
