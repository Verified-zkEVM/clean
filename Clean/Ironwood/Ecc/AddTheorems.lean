import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.Defs
import Clean.Utils.Tactics
import Mathlib.Tactic

namespace Halo2.Ironwood.Ecc

open CompElliptic.CurveForms

/-!
Reference:
`halo2_gadgets/src/ecc/chip/add.rs`
- `complete addition`

This ports the complete-addition custom gate over the Halo2 advice columns `x_p`, `y_p`,
rotated `x_qr`/`y_qr`, and auxiliary advice values `lambda`, `alpha`, `beta`, `gamma`,
and `delta`. The entry circuit copies input points into the current row, witnesses the
next-row result and auxiliaries, and calls the gate assertion.
-/

namespace Add
namespace Gate

structure Input (F : Type) where
  x_p : F
  y_p : F
  x_qr : CurrentNext F
  y_qr : CurrentNext F
  lambda : F
  alpha : F
  beta : F
  gamma : F
  delta : F
deriving ProvableStruct

namespace Input

@[simp]
def p {K : Type} (row : Input K) : Point K where
  x := row.x_p
  y := row.y_p

@[simp]
def q {K : Type} (row : Input K) : Point K where
  x := row.x_qr.curr
  y := row.y_qr.curr

@[simp]
def r {K : Type} (row : Input K) : Point K where
  x := row.x_qr.next
  y := row.y_qr.next

end Input

def Spec (row : Input Fp) : Prop :=
  (row.q.x - row.p.x ≠ 0 → (row.q.x - row.p.x) * row.lambda = row.q.y - row.p.y) ∧
    ((row.q.x - row.p.x) * row.alpha ≠ 1 →
      2 * row.p.y * row.lambda = 3 * row.p.x * row.p.x) ∧
    (row.p.x * row.q.x * (row.q.x - row.p.x) ≠ 0 →
      row.r.x = row.lambda * row.lambda - row.p.x - row.q.x ∧
      row.r.y = row.lambda * (row.p.x - row.r.x) - row.p.y) ∧
    (row.p.x * row.q.x * (row.q.y + row.p.y) ≠ 0 →
      row.r.x = row.lambda * row.lambda - row.p.x - row.q.x ∧
      row.r.y = row.lambda * (row.p.x - row.r.x) - row.p.y) ∧
    (row.p.x * row.beta ≠ 1 → row.r = row.q) ∧
    (row.q.x * row.gamma ≠ 1 → row.r = row.p) ∧
    ((row.q.x - row.p.x) * row.alpha + (row.q.y + row.p.y) * row.delta ≠ 1 →
      row.r.x = 0 ∧ row.r.y = 0)

end Gate

structure Input (F : Type) where
  p : Point F
  q : Point F
deriving ProvableStruct

def lambdaValue (input : Input Fp) : Fp :=
  if input.q.x = input.p.x then
    if input.p.y ≠ 0 then
      (3 * input.p.x * input.p.x) * (2 * input.p.y)⁻¹
    else
      0
  else
    (input.q.y - input.p.y) * (input.q.x - input.p.x)⁻¹

def rowValue (input : Input Fp) : Gate.Input Fp where
  x_p := input.p.x
  y_p := input.p.y
  x_qr := { curr := input.q.x, next := (input.p + input.q).x }
  y_qr := { curr := input.q.y, next := (input.p + input.q).y }
  lambda := lambdaValue input
  alpha := (input.q.x - input.p.x)⁻¹
  beta := input.p.x⁻¹
  gamma := input.q.x⁻¹
  delta := if input.q.x = input.p.x then (input.q.y + input.p.y)⁻¹ else 0

open Gate

theorem rowValue_spec {input : Input Fp}
    (hp : input.p.Valid) (hq : input.q.Valid) :
    Gate.Spec (rowValue input) := by
  constructor
  · intro hxdiff
    unfold rowValue lambdaValue
    simp at hxdiff ⊢
    rw [if_neg]
    · have hden : input.q.x - input.p.x ≠ 0 := hxdiff
      field_simp [hden]
    · intro hx
      exact hxdiff (sub_eq_zero.mpr hx)
  constructor
  · intro hflag
    dsimp [rowValue, lambdaValue] at hflag ⊢
    simp at hflag ⊢
    by_cases hx : input.q.x = input.p.x
    · by_cases hpy : input.p.y = 0
      · have hpx : input.p.x = 0 := by
          by_contra hpx
          exact Point.y_ne_zero_of_valid_of_x_ne_zero hp hpx hpy
        simp [hx, hpy, hpx]
      · simp [hx, hpy]
        have hden : (2 : Fp) * input.p.y ≠ 0 :=
          mul_ne_zero two_ne_zero hpy
        field_simp [hden, two_ne_zero]
    · have hcontra : (input.q.x - input.p.x) * (input.q.x - input.p.x)⁻¹ = 1 := by
        field_simp [sub_ne_zero.mpr hx]
      exact False.elim (hflag hcontra)
  constructor
  · intro hprod
    dsimp [rowValue, lambdaValue] at hprod ⊢
    simp at hprod ⊢
    have hpx : input.p.x ≠ 0 := hprod.1.1
    have hqx : input.q.x ≠ 0 := hprod.1.2
    have hxdiff : input.q.x - input.p.x ≠ 0 := hprod.2
    have hx : input.q.x ≠ input.p.x := fun h => hxdiff (sub_eq_zero.mpr h)
    have hxpq : input.p.x ≠ input.q.x := Ne.symm hx
    simp [Point.add_def, ShortWeierstrass.add, Point.ofCoords, Point.coords,
      hpx, hqx, hx, hxpq, pow_two, div_eq_mul_inv]
  constructor
  · intro hprod
    dsimp [rowValue, lambdaValue] at hprod ⊢
    simp at hprod ⊢
    have hpx : input.p.x ≠ 0 := hprod.1.1
    have hqx : input.q.x ≠ 0 := hprod.1.2
    have hysum : input.q.y + input.p.y ≠ 0 := hprod.2
    by_cases hx : input.q.x = input.p.x
    · have hsame := Point.y_eq_or_neg_of_same_x hp hq hpx hqx hx
      rcases hsame with hy | hy
      · have hnotInv : ¬(input.q.x = input.p.x ∧ input.q.y = -input.p.y) := by
          intro hinv
          apply hysum
          rw [hinv.2]
          ring
        have hpy : input.p.y ≠ 0 :=
          Point.y_ne_zero_of_valid_of_x_ne_zero hp hpx
        have hnotY : input.q.y ≠ -input.p.y := fun h => hnotInv ⟨hx, h⟩
        have hysum' : input.p.y + input.q.y ≠ 0 := by
          rw [hy]
          exact add_self_ne_zero hpy
        simp [Point.add_def, ShortWeierstrass.add, Point.ofCoords, Point.coords,
          hpx, hx, hpy, hysum', pallasA, pow_two, div_eq_mul_inv]
        constructor
        · ring
        · exact Or.inl (Or.inl (by ring))
      · exact False.elim (hysum (by rw [hy]; ring))
    · have hnotInv : ¬(input.q.x = input.p.x ∧ input.q.y = -input.p.y) := by
        exact fun h => hx h.1
      have hxpq : input.p.x ≠ input.q.x := Ne.symm hx
      simp [Point.add_def, ShortWeierstrass.add, Point.ofCoords, Point.coords,
        hpx, hqx, hx, hxpq, pow_two, div_eq_mul_inv]
  constructor
  · intro hflag
    dsimp [rowValue] at hflag ⊢
    simp at hflag ⊢
    by_cases hpx : input.p.x = 0
    · have hpy := Point.y_eq_zero_of_valid_of_x_eq_zero hp hpx
      change input.p.y = 0 at hpy
      simp [Point.add_def, ShortWeierstrass.add, Point.ofCoords, Point.coords,hpx, hpy]
    · have hcontra : input.p.x * input.p.x⁻¹ = 1 := by
        field_simp [hpx]
      exact False.elim (hflag hcontra)
  constructor
  · intro hflag
    dsimp [rowValue] at hflag ⊢
    by_cases hpx : input.p.x = 0
    · have hpy := Point.y_eq_zero_of_valid_of_x_eq_zero hp hpx
      by_cases hqx : input.q.x = 0
      · have hqy := Point.y_eq_zero_of_valid_of_x_eq_zero hq hqx
        change input.q.y = 0 at hqy
        have hpEq : input.p = Point.zero := by
          rw [Point.mk.injEq]
          exact ⟨hpx, hpy⟩
        have hqEq : input.q = Point.zero := by
          rw [Point.mk.injEq]
          exact ⟨hqx, hqy⟩
        simp [Point.add_def, ShortWeierstrass.add,
          Point.ofCoords, Point.coords,
          Point.zero, hpEq, hqEq]
      · have hcontra : input.q.x * input.q.x⁻¹ = 1 := by
          field_simp [hqx]
        exact False.elim (hflag hcontra)
    · by_cases hqx : input.q.x = 0
      · have hqy := Point.y_eq_zero_of_valid_of_x_eq_zero hq hqx
        change input.q.y = 0 at hqy
        simp [Point.add_def, ShortWeierstrass.add, Point.ofCoords, Point.coords, hpx, hqx, hqy]
      · have hcontra : input.q.x * input.q.x⁻¹ = 1 := by
          field_simp [hqx]
        exact False.elim (hflag hcontra)
  · intro hflag
    dsimp [rowValue] at hflag ⊢
    simp at hflag ⊢
    by_cases hpx : input.p.x = 0
    · have hpy := Point.y_eq_zero_of_valid_of_x_eq_zero hp hpx
      change input.p.y = 0 at hpy
      by_cases hqx : input.q.x = 0
      · have hqy := Point.y_eq_zero_of_valid_of_x_eq_zero hq hqx
        change input.q.y = 0 at hqy
        simp [Point.add_def, ShortWeierstrass.add,
          Point.ofCoords, Point.coords,
          hpx, hpy, hqx, hqy]
      · have hcontra :
            ((input.q.x - input.p.x) * (input.q.x - input.p.x)⁻¹ +
              if input.q.x = input.p.x then
                (input.q.y + input.p.y) * (input.q.y + input.p.y)⁻¹
          else 0) = 1 := by
          simp [hpx, hqx]
        exact False.elim (hflag hcontra)
    · by_cases hqx : input.q.x = 0
      · have hcontra :
            ((input.q.x - input.p.x) * (input.q.x - input.p.x)⁻¹ +
              if input.q.x = input.p.x then
                (input.q.y + input.p.y) * (input.q.y + input.p.y)⁻¹
          else 0) = 1 := by
          have hne : ¬ input.q.x = input.p.x := by
            rw [hqx]
            exact fun h => hpx h.symm
          have hne0 : ¬ (0 : Fp) = input.p.x := fun h => hpx h.symm
          simp [hpx, hqx, hne0]
        exact False.elim (hflag hcontra)
      · by_cases hx : input.q.x = input.p.x
        · by_cases hy : input.q.y = -input.p.y
          · simp [Point.add_def, ShortWeierstrass.add,
              Point.ofCoords, Point.coords,
              hpx, hx, hy]
          · have hsame := Point.y_eq_or_neg_of_same_x hp hq hpx hqx hx
            rcases hsame with hyeq | hyneg
            · have hysum : input.q.y + input.p.y ≠ 0 := by
                rw [hyeq]
                exact add_self_ne_zero
                  (Point.y_ne_zero_of_valid_of_x_ne_zero hp hpx)
              have hcontra :
                    ((input.q.x - input.p.x) * (input.q.x - input.p.x)⁻¹ +
                      if input.q.x = input.p.x then
                        (input.q.y + input.p.y) * (input.q.y + input.p.y)⁻¹
                      else 0) = 1 := by
                simp [hx, hysum]
              exact False.elim (hflag hcontra)
            · exact False.elim (hy hyneg)
        · have hcontra :
              ((input.q.x - input.p.x) * (input.q.x - input.p.x)⁻¹ +
                if input.q.x = input.p.x then
                  (input.q.y + input.p.y) * (input.q.y + input.p.y)⁻¹
                else 0) = 1 := by
            simp [hx]
            field_simp [sub_ne_zero.mpr hx]
          exact False.elim (hflag hcontra)

theorem add_of_spec {row : Gate.Input Fp}
    (hp : row.p.Valid) (hq : row.q.Valid) (hrow : Gate.Spec row) :
    row.r = row.p + row.q := by
  dsimp [Gate.Input.p, Gate.Input.q, Gate.Input.r] at hp hq hrow ⊢
  rcases hrow with ⟨hSlope, hTangent, hNonexceptionalDiff, hNonexceptionalSum,
    hLeftIdentity, hRightIdentity, hInverse⟩
  by_cases hpx : row.x_p = 0
  · have hflag : row.p.x * row.beta ≠ 1 := by
      simp [Gate.Input.p, hpx]
    have hr := hLeftIdentity hflag
    have hpy := Point.y_eq_zero_of_valid_of_x_eq_zero hp hpx
    change row.y_p = 0 at hpy
    apply Point.ext_coords
    simpa [Point.add_def, ShortWeierstrass.add,
      Point.coords, hpx, hpy, Gate.Input.q, Gate.Input.r] using congrArg Point.coords hr
  · by_cases hqx : row.x_qr.curr = 0
    · have hflag : row.q.x * row.gamma ≠ 1 := by
        simp [Gate.Input.q, hqx]
      have hr := hRightIdentity hflag
      have hqy := Point.y_eq_zero_of_valid_of_x_eq_zero hq hqx
      change row.y_qr.curr = 0 at hqy
      apply Point.ext_coords
      simpa [Point.add_def, ShortWeierstrass.add,
        Point.coords, hpx, hqx, hqy, Gate.Input.p, Gate.Input.r] using congrArg Point.coords hr
    · by_cases hinv : row.x_qr.curr = row.x_p ∧ row.y_qr.curr = -row.y_p
      · have hflag :
            (row.q.x - row.p.x) * row.alpha + (row.q.y + row.p.y) * row.delta ≠ 1 := by
          rcases hinv with ⟨hx, hy⟩
          simp [Gate.Input.p, Gate.Input.q, hx, hy]
        have hr := hInverse hflag
        have hr0 : row.r = Point.zero := by
          rw [Point.mk.injEq]
          exact hr
        rcases hinv with ⟨hx, hy⟩
        apply Point.ext_coords
        simp [Point.add_def, ShortWeierstrass.add,
          Point.coords, hpx, hx, hy]
        simpa [Point.zero, Point.coords, Gate.Input.r] using congrArg Point.coords hr0
      · have hr :
            row.r.x = row.lambda * row.lambda - row.p.x - row.q.x ∧
              row.r.y = row.lambda * (row.p.x - row.r.x) - row.p.y := by
          by_cases hx : row.x_qr.curr = row.x_p
          · have hsame := Point.y_eq_or_neg_of_same_x hp hq hpx hqx hx
            rcases hsame with hy | hy
            · have hysum : row.q.y + row.p.y ≠ 0 := by
                simp [Gate.Input.p, Gate.Input.q] at hy ⊢
                rw [hy]
                exact add_self_ne_zero (Point.y_ne_zero_of_valid_of_x_ne_zero hp hpx)
              have hprod : row.p.x * row.q.x * (row.q.y + row.p.y) ≠ 0 := by
                simpa [Gate.Input.p, Gate.Input.q] using
                  mul_ne_zero (mul_ne_zero hpx hqx) hysum
              exact hNonexceptionalSum hprod
            · exact False.elim (hinv ⟨hx, hy⟩)
          · have hxdiff : row.q.x - row.p.x ≠ 0 := by
              simp [Gate.Input.p, Gate.Input.q]
              intro hzero
              exact hx (sub_eq_zero.mp hzero)
            have hprod : row.p.x * row.q.x * (row.q.x - row.p.x) ≠ 0 := by
              simpa [Gate.Input.p, Gate.Input.q] using
                mul_ne_zero (mul_ne_zero hpx hqx) hxdiff
            exact hNonexceptionalDiff hprod
        have hlambda :
            row.lambda = lambdaValue { p := row.p, q := row.q } := by
          by_cases hx : row.x_qr.curr = row.x_p
          · have hpy : row.y_p ≠ 0 :=
              Point.y_ne_zero_of_valid_of_x_ne_zero hp hpx
            have hflag : (row.q.x - row.p.x) * row.alpha ≠ 1 := by
              simp [Gate.Input.p, Gate.Input.q, hx]
            have htangent := hTangent hflag
            simp [Gate.Input.p] at htangent
            unfold lambdaValue
            simp [Gate.Input.p, Gate.Input.q, hx, hpy]
            have hden : (2 : Fp) * row.y_p ≠ 0 :=
              mul_ne_zero two_ne_zero hpy
            field_simp [hden, two_ne_zero]
            linear_combination htangent
          · have hxdiff : row.q.x - row.p.x ≠ 0 := by
              simp [Gate.Input.p, Gate.Input.q]
              intro hzero
              exact hx (sub_eq_zero.mp hzero)
            have hslope := hSlope hxdiff
            simp [Gate.Input.p, Gate.Input.q] at hslope hxdiff
            unfold lambdaValue
            simp [Gate.Input.p, Gate.Input.q, hx]
            field_simp [hxdiff]
            linear_combination hslope
        rw [hlambda] at hr
        simp [Gate.Input.p, Gate.Input.q, Gate.Input.r] at hr
        apply Point.ext_coords
        by_cases hx : row.x_qr.curr = row.x_p
        · have hsame := Point.y_eq_or_neg_of_same_x hp hq hpx hqx hx
          rcases hsame with hy | hy
          · change row.y_qr.curr = row.y_p at hy
            have hysum : row.y_qr.curr + row.y_p ≠ 0 := by
              rw [hy]
              exact add_self_ne_zero
                (Point.y_ne_zero_of_valid_of_x_ne_zero hp hpx)
            have hysum' : row.y_p + row.y_qr.curr ≠ 0 := by
              rw [hy]
              exact add_self_ne_zero
                (Point.y_ne_zero_of_valid_of_x_ne_zero hp hpx)
            simp [Point.add_def, ShortWeierstrass.add,
              Point.coords, hpx, hx, hysum', pow_two, div_eq_mul_inv]
            rw [hr.1, hr.2, hr.1]
            simp [lambdaValue, hx, Point.y_ne_zero_of_valid_of_x_ne_zero hp hpx]
            simp [pallasA]
            ring_nf
            exact ⟨trivial, trivial⟩
          · exact False.elim (hinv ⟨hx, hy⟩)
        · have hxpq : row.x_p ≠ row.x_qr.curr := Ne.symm hx
          simp [Point.add_def, ShortWeierstrass.add,
            Point.coords, hpx, hqx, hxpq, pow_two, div_eq_mul_inv]
          rw [hr.1, hr.2, hr.1]
          simp [lambdaValue, hx]

/-- The evaluated `.ite` witness program for `lambda` is `lambdaValue`. Stated with the
`Decidable` instances as variables: `BExpr.feq`'s evaluation decides field equality
through its own instance, which is not syntactically the canonical one — an
instance-generic statement lets `simp` match either spelling (after
`decide_eq_true_eq` has turned the conditions propositional). -/
private theorem ite_lambdaValue (px py qx qy : Fp)
    {d1 : Decidable (qx = px)} {d2 : Decidable (py = 0)} :
    (@ite _ (qx = px) d1
      (@ite _ (py = 0) d2 (0 : Fp) (3 * px * px * (2 * py)⁻¹))
      ((qy - py) * (qx - px)⁻¹))
    = lambdaValue { p := { x := px, y := py }, q := { x := qx, y := qy } } := by
  unfold lambdaValue
  by_cases h : qx = px <;> by_cases h' : py = 0 <;> simp_all

/-- Same for the `delta` witness program and `rowValue`'s delta component. -/
private theorem ite_deltaValue (px py qx qy : Fp) {d : Decidable (qx = px)} :
    (@ite _ (qx = px) d ((qy + py)⁻¹) 0)
    = (rowValue { p := { x := px, y := py }, q := { x := qx, y := qy } }).delta := by
  unfold rowValue
  by_cases h : qx = px <;> simp_all

/-- The evaluated `.ite` witness tree for `r.x` computes the x-coordinate of the
complete point addition. Decidable instances are variables for the same reason as in
`ite_lambdaValue` (the compound `&&&` conditions arrive in this propositional shape
via `Bool.and_eq_true`/`decide_eq_true_eq`, both in `circuit_norm`). -/
private theorem ite_rX (px py qx qy : Fp)
    {d1 : Decidable (px = 0 ∧ py = 0)} {d2 : Decidable (qx = 0 ∧ qy = 0)}
    {d3 : Decidable (px = qx)} {d4 : Decidable (py + qy = 0)} :
    (@ite _ (px = 0 ∧ py = 0) d1 qx
      (@ite _ (qx = 0 ∧ qy = 0) d2 px
        (@ite _ (px = qx) d3
          (@ite _ (py + qy = 0) d4 0
            (3 * px * px * (2 * py)⁻¹ * (3 * px * px * (2 * py)⁻¹) - px - qx))
          ((qy - py) * (qx - px)⁻¹ * ((qy - py) * (qx - px)⁻¹) - px - qx))))
    = ({ x := px, y := py } + { x := qx, y := qy } : Point Fp).x := by
  simp only [Point.add_def, ShortWeierstrass.add, Point.ofCoords, Point.coords,
    Prod.mk.injEq, pallasA]
  by_cases h1 : px = 0 ∧ py = 0
  · simp only [eq_true h1, reduceIte]
  · by_cases h2 : qx = 0 ∧ qy = 0
    · simp only [eq_false h1, eq_true h2, reduceIte]
    · by_cases h3 : px = qx
      · by_cases h4 : py + qy = 0
        · simp only [eq_false h1, eq_false h2, eq_true h3, eq_true h4, reduceIte]
        · simp only [eq_false h1, eq_false h2, eq_true h3, eq_false h4, reduceIte]
          ring
      · simp only [eq_false h1, eq_false h2, eq_false h3, reduceIte]
        ring

/-- Same for the `r.y` witness tree and the y-coordinate of the complete addition. -/
private theorem ite_rY (px py qx qy : Fp)
    {d1 : Decidable (px = 0 ∧ py = 0)} {d2 : Decidable (qx = 0 ∧ qy = 0)}
    {d3 : Decidable (px = qx)} {d4 : Decidable (py + qy = 0)} :
    (@ite _ (px = 0 ∧ py = 0) d1 qy
      (@ite _ (qx = 0 ∧ qy = 0) d2 py
        (@ite _ (px = qx) d3
          (@ite _ (py + qy = 0) d4 0
            (3 * px * px * (2 * py)⁻¹ *
              (px - (3 * px * px * (2 * py)⁻¹ * (3 * px * px * (2 * py)⁻¹) - px - qx)) - py))
          ((qy - py) * (qx - px)⁻¹ *
            (px - ((qy - py) * (qx - px)⁻¹ * ((qy - py) * (qx - px)⁻¹) - px - qx)) - py))))
    = ({ x := px, y := py } + { x := qx, y := qy } : Point Fp).y := by
  simp only [Point.add_def, ShortWeierstrass.add, Point.ofCoords, Point.coords,
    Prod.mk.injEq, pallasA]
  by_cases h1 : px = 0 ∧ py = 0
  · simp only [eq_true h1, reduceIte]
  · by_cases h2 : qx = 0 ∧ qy = 0
    · simp only [eq_false h1, eq_true h2, reduceIte]
    · by_cases h3 : px = qx
      · by_cases h4 : py + qy = 0
        · simp only [eq_false h1, eq_false h2, eq_true h3, eq_true h4, reduceIte]
        · simp only [eq_false h1, eq_false h2, eq_true h3, eq_false h4, reduceIte]
          ring
      · simp only [eq_false h1, eq_false h2, eq_false h3, reduceIte]
        ring

end Halo2.Ironwood.Ecc.Add
