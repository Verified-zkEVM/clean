import Clean.Orchard.Ecc.ScalarMul.Defs

/-!
Reference: `halo2_gadgets/src/ecc/chip/mul_fixed.rs`.
-/

namespace Orchard.Ecc.ScalarMul.MulFixed

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

structure Row (F : Type) extends CoordsRow F where
  zCur : F
  zNext : F
deriving ProvableStruct

def word {K : Type} [Sub K] [Mul K] [OfNat K 8] (row : Row K) : K :=
  row.zCur - row.zNext * 8

def coordsRow {K : Type} [Sub K] [Mul K] [OfNat K 8] (row : Row K) : CoordsRow K :=
  { row.toCoordsRow with window := word row }

def Spec (params : CoordsParams Fp) (row : Row Fp) : Prop :=
  Coords.Spec params (coordsRow row)

def main (params : CoordsParams Fp) (row : Var Row Fp) :
    Circuit Fp Unit := do
  Coords.circuit params { row.toCoordsRow with window := word row }

def circuit (params : CoordsParams Fp) : FormalAssertion Fp Row where
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

open CompElliptic.Curves.Pasta CompElliptic.CurveForms.ShortWeierstrass
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
def windowPoint (point : SWPoint Pallas.curve) (w k : ℕ) : SWPoint Pallas.curve :=
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
  point : SWPoint Pallas.curve
  order_eq : addOrderOf point = PALLAS_SCALAR_CARD
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
  rw [← B.order_eq, addOrderOf_dvd_iff_nsmul_eq_zero]

theorem windowPoint_ne_zero {w k : ℕ} (hk : k < 8) :
    windowPoint B.point w k ≠ 0 := by
  unfold windowPoint
  rw [Ne, B.nsmul_eq_zero_iff]
  intro hdvd
  have hval : (windowScalar w k).val < PALLAS_SCALAR_CARD := ZMod.val_lt _
  have h0 : (windowScalar w k).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hval
  exact windowScalar_ne_zero hk ((ZMod.val_eq_zero _).mp h0)

theorem windowPoint_onCurve {w k : ℕ} (hk : k < 8) :
    Pallas.OnCurve ((windowPoint B.point w k).x, (windowPoint B.point w k).y) :=
  SWPoint.onCurve_of_ne_zero (B.windowPoint_ne_zero hk)

theorem nsmul_ne_zero {n : ℕ} (hn : 0 < n) (hlt : n < PALLAS_SCALAR_CARD) :
    n • B.point ≠ 0 := by
  rw [Ne, B.nsmul_eq_zero_iff]
  intro hdvd
  have := Nat.le_of_dvd hn hdvd
  omega

theorem nsmul_onCurve {n : ℕ} (hn : 0 < n) (hlt : n < PALLAS_SCALAR_CARD) :
    Pallas.OnCurve ((n • B.point).x, (n • B.point).y) :=
  SWPoint.onCurve_of_ne_zero (B.nsmul_ne_zero hn hlt)

/--
The collision-freedom fact behind the incomplete additions of fixed-base scalar
multiplication: distinct small positive multiples of the generator have distinct
`x`-coordinates, since equal `x` would force equal-or-opposite points and hence a
relation `t ∓ s ≡ 0` modulo the (large) group order.
-/
theorem nsmul_x_ne {s t : ℕ} (hs : 0 < s) (hst : s < t)
    (hsum : s + t < PALLAS_SCALAR_CARD) :
    (t • B.point).x ≠ (s • B.point).x := by
  have hs_ne : s • B.point ≠ 0 := B.nsmul_ne_zero hs (by omega)
  have ht_ne : t • B.point ≠ 0 := B.nsmul_ne_zero (by omega) (by omega)
  intro hx
  rcases SWPoint.eq_or_eq_neg_of_x_eq ht_ne hs_ne hx with heq | hneg
  · rw [nsmul_eq_nsmul_iff_modEq, B.order_eq, Nat.ModEq,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
    omega
  · have hzero : (t + s) • B.point = 0 := by
      rw [add_nsmul, hneg, neg_add_cancel]
    rw [B.nsmul_eq_zero_iff] at hzero
    have := Nat.le_of_dvd (by omega) hzero
    omega

/-- Congruent scalars produce the same multiple of the generator. -/
theorem nsmul_congr {m n : ℕ} (h : m ≡ n [MOD PALLAS_SCALAR_CARD]) :
    m • B.point = n • B.point := by
  rw [nsmul_eq_nsmul_iff_modEq, B.order_eq]
  exact h

/-- Adding a cast natural to a scalar acts as expected on multiples of the generator. -/
theorem add_natCast_val_nsmul (a : Fq) (S : ℕ) :
    (a + (S : Fq)).val • B.point = (a.val + S) • B.point := by
  apply B.nsmul_congr
  rw [ZMod.val_add, ZMod.val_natCast]
  exact (Nat.mod_modEq _ _).trans (Nat.ModEq.add_left _ (Nat.mod_modEq _ _))

/-- The value-level result of multiplying the fixed base by a full-width scalar. -/
def mulValue (s : Fq) : Point Fp :=
  { x := (s.val • B.point).x, y := (s.val • B.point).y }

theorem mulValue_valid (s : Fq) : Pallas.Valid (B.mulValue s).coords :=
  (s.val • B.point).onCurve

theorem mulValue_coords (s : Fq) :
    (B.mulValue s).coords = ((s.val • B.point).x, (s.val • B.point).y) := rfl

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
  have hrowCurve : Pallas.OnCurve ((windowPoint B.point w k).x, row.yP) := by
    rw [← hxP]
    show row.yP ^ 2 = row.xP ^ 3 + Pallas.a * row.xP + Pallas.b
    simp only [Pallas.a, Pallas.b]
    linear_combination hcurve
  rcases y_eq_or_y_eq_neg_of_onCurve hrowCurve (B.windowPoint_onCurve hk) with hy | hy
  · exact hy
  · exact absurd ⟨row.u, by rw [hy] at hu; linear_combination -hu⟩
      (B.z_sub_y_not_square w hw k hk)

end FixedBase

end Orchard.Ecc.ScalarMul.MulFixed
