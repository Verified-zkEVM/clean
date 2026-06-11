import Clean.Orchard.Ecc.Theorems
import Clean.Utils.Tactics
import Mathlib.Tactic

namespace Orchard.Ecc

open CompElliptic.Curves.Pasta

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/add.rs`
- `complete addition`

This ports the complete-addition custom gate over the Halo2 advice columns `x_p`, `y_p`,
rotated `x_qr`/`y_qr`, and auxiliary advice values `lambda`, `alpha`, `beta`, `gamma`,
and `delta`. The entry circuit copies input points into the current row, witnesses the
next-row result and auxiliaries, and calls the gate assertion.
-/

namespace Add

structure Input (F : Type) where
  p : Point F
  q : Point F
deriving ProvableStruct

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

def main (row : Var Input Fp) : Circuit Fp Unit := do
  let x_q_minus_x_p := row.q.x - row.p.x
  let x_p_minus_x_r := row.p.x - row.r.x
  let y_q_plus_y_p := row.q.y + row.p.y
  let if_alpha := x_q_minus_x_p * row.alpha
  let if_beta := row.p.x * row.beta
  let if_gamma := row.q.x * row.gamma
  let if_delta := y_q_plus_y_p * row.delta
  let incomplete := x_q_minus_x_p * row.lambda - (row.q.y - row.p.y)
  assertZero (x_q_minus_x_p * incomplete)
  assertZero ((1 - if_alpha) * (2 * row.p.y * row.lambda - 3 * row.p.x * row.p.x))
  let nonexceptional_x_r := row.lambda * row.lambda - row.p.x - row.q.x - row.r.x
  let nonexceptional_y_r := row.lambda * x_p_minus_x_r - row.p.y - row.r.y
  assertZero (row.p.x * row.q.x * x_q_minus_x_p * nonexceptional_x_r)
  assertZero (row.p.x * row.q.x * x_q_minus_x_p * nonexceptional_y_r)
  assertZero (row.p.x * row.q.x * y_q_plus_y_p * nonexceptional_x_r)
  assertZero (row.p.x * row.q.x * y_q_plus_y_p * nonexceptional_y_r)
  assertZero ((1 - if_beta) * (row.r.x - row.q.x))
  assertZero ((1 - if_beta) * (row.r.y - row.q.y))
  assertZero ((1 - if_gamma) * (row.r.x - row.p.x))
  assertZero ((1 - if_gamma) * (row.r.y - row.p.y))
  assertZero ((1 - if_alpha - if_delta) * row.r.x)
  assertZero ((1 - if_alpha - if_delta) * row.r.y)

def circuit : FormalAssertion Fp Input where
  name := "GATE complete addition"
  main
  Spec := Spec
  soundness := by
    circuit_proof_start [main, Spec]
    let px := input_x_p
    let py := input_y_p
    let qx := input_x_qr_curr
    let qy := input_y_qr_curr
    let rx := input_x_qr_next
    let ry := input_y_qr_next
    simp_all [sub_eq_add_neg]
    rcases h_holds with
      ⟨h1, h2, h3a, h3b, h3c, h3d, h4a, h4b, h5a, h5b, h6a, h6b⟩
    constructor
    · intro hne
      rcases h1 with hzero | hline
      · exact False.elim (hne hzero)
      · linear_combination hline
    constructor
    · intro hne
      rcases h2 with hflag | htangent
      · have : (qx + -px) * input_alpha = 1 := by linear_combination -hflag
        exact False.elim (hne this)
      · linear_combination htangent
    constructor
    · intro hpx hqx hxdiff
      constructor
      · rcases h3a with hzero | hx
        · rcases hzero with hzero | hzero
          · rcases hzero with hzero | hzero
            · exact False.elim (hpx hzero)
            · exact False.elim (hqx hzero)
          · exact False.elim (hxdiff hzero)
        · linear_combination -hx
      · rcases h3b with hzero | hy
        · rcases hzero with hzero | hzero
          · rcases hzero with hzero | hzero
            · exact False.elim (hpx hzero)
            · exact False.elim (hqx hzero)
          · exact False.elim (hxdiff hzero)
        · linear_combination -hy
    constructor
    · intro hpx hqx hysum
      constructor
      · rcases h3c with hzero | hx
        · rcases hzero with hzero | hzero
          · rcases hzero with hzero | hzero
            · exact False.elim (hpx hzero)
            · exact False.elim (hqx hzero)
          · exact False.elim (hysum hzero)
        · linear_combination -hx
      · rcases h3d with hzero | hy
        · rcases hzero with hzero | hzero
          · rcases hzero with hzero | hzero
            · exact False.elim (hpx hzero)
            · exact False.elim (hqx hzero)
          · exact False.elim (hysum hzero)
        · linear_combination -hy
    constructor
    · intro hne
      constructor
      · rcases h4a with hflag | hx
        · have : px * input_beta = 1 := by linear_combination -hflag
          exact False.elim (hne this)
        · linear_combination hx
      · rcases h4b with hflag | hy
        · have : px * input_beta = 1 := by linear_combination -hflag
          exact False.elim (hne this)
        · linear_combination hy
    constructor
    · intro hne
      constructor
      · rcases h5a with hflag | hx
        · have : qx * input_gamma = 1 := by linear_combination -hflag
          exact False.elim (hne this)
        · linear_combination hx
      · rcases h5b with hflag | hy
        · have : qx * input_gamma = 1 := by linear_combination -hflag
          exact False.elim (hne this)
        · linear_combination hy
    · intro hne
      constructor
      · rcases h6a with hflag | hx
        · have : (qx + -px) * input_alpha + (qy + py) * input_delta = 1 := by
            linear_combination -hflag
          exact False.elim (hne this)
        · exact hx
      · rcases h6b with hflag | hy
        · have : (qx + -px) * input_alpha + (qy + py) * input_delta = 1 := by
            linear_combination -hflag
          exact False.elim (hne this)
        · exact hy
  completeness := by
    circuit_proof_start [main, Spec]
    let px := input_x_p
    let py := input_y_p
    let qx := input_x_qr_curr
    let qy := input_y_qr_curr
    let rx := input_x_qr_next
    let ry := input_y_qr_next
    simp_all [sub_eq_add_neg]
    rcases h_spec with ⟨h1, h2, h3, h3', h4, h5, h6⟩
    constructor
    · by_cases hzero : qx + -px = 0
      · exact Or.inl hzero
      · exact Or.inr (by
        have hline := h1 hzero
        linear_combination hline)
    constructor
    · by_cases hflag : (qx + -px) * input_alpha = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (by
        have htangent := h2 hflag
        linear_combination htangent)
    constructor
    · by_cases hpx : px = 0
      · exact Or.inl (Or.inl (Or.inl hpx))
      · by_cases hqx : qx = 0
        · exact Or.inl (Or.inl (Or.inr hqx))
        · by_cases hxdiff : qx + -px = 0
          · exact Or.inl (Or.inr hxdiff)
          · exact Or.inr (by
              have hx := (h3 hpx hqx hxdiff).1
              linear_combination -hx)
    constructor
    · by_cases hpx : px = 0
      · exact Or.inl (Or.inl (Or.inl hpx))
      · by_cases hqx : qx = 0
        · exact Or.inl (Or.inl (Or.inr hqx))
        · by_cases hxdiff : qx + -px = 0
          · exact Or.inl (Or.inr hxdiff)
          · exact Or.inr (by
              have hy := (h3 hpx hqx hxdiff).2
              linear_combination -hy)
    constructor
    · by_cases hpx : px = 0
      · exact Or.inl (Or.inl (Or.inl hpx))
      · by_cases hqx : qx = 0
        · exact Or.inl (Or.inl (Or.inr hqx))
        · by_cases hysum : qy + py = 0
          · exact Or.inl (Or.inr hysum)
          · exact Or.inr (by
              have hx := (h3' hpx hqx hysum).1
              linear_combination -hx)
    constructor
    · by_cases hpx : px = 0
      · exact Or.inl (Or.inl (Or.inl hpx))
      · by_cases hqx : qx = 0
        · exact Or.inl (Or.inl (Or.inr hqx))
        · by_cases hysum : qy + py = 0
          · exact Or.inl (Or.inr hysum)
          · exact Or.inr (by
              have hy := (h3' hpx hqx hysum).2
              linear_combination -hy)
    constructor
    · by_cases hflag : px * input_beta = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (by
          have hx := (h4 hflag).1
          linear_combination hx)
    constructor
    · by_cases hflag : px * input_beta = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (by
          have hy := (h4 hflag).2
          linear_combination hy)
    constructor
    · by_cases hflag : qx * input_gamma = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (by
          have hx := (h5 hflag).1
          linear_combination hx)
    constructor
    · by_cases hflag : qx * input_gamma = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (by
          have hy := (h5 hflag).2
          linear_combination hy)
    constructor
    · by_cases hflag : (qx + -px) * input_alpha + (qy + py) * input_delta = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (h6 hflag).1
    · by_cases hflag : (qx + -px) * input_alpha + (qy + py) * input_delta = 1
      · exact Or.inl (by linear_combination -hflag)
      · exact Or.inr (h6 hflag).2

end Gate

section ValueModel

def lambdaValue (input : Input Fp) : Fp :=
  if input.q.x = input.p.x then
    if input.p.y ≠ 0 then
      (3 * input.p.x * input.p.x) * (2 * input.p.y)⁻¹
    else
      0
  else
    (input.q.y - input.p.y) * (input.q.x - input.p.x)⁻¹

def outputValue (input : Input Fp) : Point Fp :=
  let lambda := lambdaValue input
  if input.p.x = 0 then
    input.q
  else if input.q.x = 0 then
    input.p
  else if input.q.x = input.p.x ∧ input.q.y = -input.p.y then
    Point.zero
  else
    let xR := lambda * lambda - input.p.x - input.q.x
    let yR := lambda * (input.p.x - xR) - input.p.y
    { x := xR, y := yR }

def rowValue (input : Input Fp) : Gate.Input Fp where
  x_p := input.p.x
  y_p := input.p.y
  x_qr := { curr := input.q.x, next := (outputValue input).x }
  y_qr := { curr := input.q.y, next := (outputValue input).y }
  lambda := lambdaValue input
  alpha := (input.q.x - input.p.x)⁻¹
  beta := input.p.x⁻¹
  gamma := input.q.x⁻¹
  delta :=
    if input.q.x = input.p.x then
      (input.q.y + input.p.y)⁻¹
    else
      0

theorem outputValue_eq_shortWeierstrass_add {input : Input Fp}
    (hp : Pallas.Valid input.p.coords)
    (hq : Pallas.Valid input.q.coords) :
    (outputValue input).coords =
      CompElliptic.CurveForms.ShortWeierstrass.add
        (0 : Fp) input.p.coords input.q.coords := by
  rcases input with ⟨⟨px, py⟩, ⟨qx, qy⟩⟩
  unfold Point.coords outputValue lambdaValue
    CompElliptic.CurveForms.ShortWeierstrass.add at *
  simp only
  by_cases hpx : px = 0
  · have hpy : py = 0 :=
      Point.y_eq_zero_of_valid_of_x_eq_zero (point := { x := px, y := py }) hp hpx
    simp [hpx, hpy]
  · by_cases hqx : qx = 0
    · have hqy : qy = 0 :=
        Point.y_eq_zero_of_valid_of_x_eq_zero (point := { x := qx, y := qy }) hq hqx
      simp [hpx, hqx, hqy]
    · simp [hpx, hqx]
      by_cases hx : px = qx
      · have hx' : qx = px := hx.symm
        rw [if_pos hx', if_pos hx]
        by_cases hy : py + qy = 0
        · have hqy : qy = -py := by linear_combination hy
          simp [Point.zero, hx', hqy]
        · have hqy : ¬ qy = -py := by
            intro h
            apply hy
            rw [h]
            ring
          simp [hx', hqy, hy]
          constructor <;>
            by_cases hpy : py = 0 <;>
              simp [hpy] <;> ring
      · have hx' : ¬ qx = px := fun h => hx h.symm
        simp [hx, hx']
        constructor <;> ring

theorem outputValue_eq_add {input : Input Fp}
    (hp : Pallas.Valid input.p.coords)
    (hq : Pallas.Valid input.q.coords) :
    (outputValue input).coords =
      Pallas.add input.p.coords input.q.coords := by
  exact outputValue_eq_shortWeierstrass_add
    hp
    hq

theorem outputValue_valid_pallas {input : Input Fp}
    (hp : Pallas.Valid input.p.coords)
    (hq : Pallas.Valid input.q.coords) :
    Pallas.Valid (outputValue input).coords := by
  rw [outputValue_eq_add hp hq]
  exact CompElliptic.CurveForms.ShortWeierstrass.valid_add hp hq

theorem pallas_two_ne_zero : (2 : Fp) ≠ 0 := by
  decide

theorem pallas_add_self_ne_zero {y : Fp} (hy : y ≠ 0) :
    y + y ≠ 0 := by
  intro h
  have hmul : (2 : Fp) * y = 0 := by
    linear_combination h
  exact hy ((mul_eq_zero.mp hmul).resolve_left pallas_two_ne_zero)

theorem pallas_y_eq_or_neg_of_same_x {p q : Point Fp}
    (hp : Pallas.Valid p.coords) (hq : Pallas.Valid q.coords)
    (hpx : p.x ≠ 0) (hqx : q.x ≠ 0) (hx : q.x = p.x) :
    q.y = p.y ∨ q.y = -p.y := by
  have hpCurve : Pallas.OnCurve p.coords := by
    rcases hp with hCurve | hIdentity
    · exact hCurve
    · rcases p with ⟨px, py⟩
      simp only [Point.coords, Prod.mk.injEq] at hIdentity
      exact False.elim (hpx hIdentity.1)
  have hqCurve : Pallas.OnCurve q.coords := by
    rcases hq with hCurve | hIdentity
    · exact hCurve
    · rcases q with ⟨qx, qy⟩
      simp only [Point.coords, Prod.mk.injEq] at hIdentity
      exact False.elim (hqx hIdentity.1)
  unfold Pallas.OnCurve CompElliptic.CurveForms.ShortWeierstrass.OnCurve
    Pallas.a Pallas.b Point.coords at hpCurve hqCurve
  have hsquare : (q.y - p.y) * (q.y + p.y) = 0 := by
    rw [hx] at hqCurve
    linear_combination hqCurve - hpCurve
  rcases mul_eq_zero.mp hsquare with h | h
  · left
    exact sub_eq_zero.mp h
  · right
    linear_combination h

end ValueModel

open Gate

theorem rowValue_spec_pallas {input : Input Fp}
    (hp : Pallas.Valid input.p.coords) (hq : Pallas.Valid input.q.coords) :
    Spec (rowValue input) := by
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
          mul_ne_zero pallas_two_ne_zero hpy
        field_simp [hden, pallas_two_ne_zero]
    · have hcontra : (input.q.x - input.p.x) * (input.q.x - input.p.x)⁻¹ = 1 := by
        field_simp [sub_ne_zero.mpr hx]
      exact False.elim (hflag hcontra)
  constructor
  · intro hprod
    dsimp [rowValue, outputValue, lambdaValue] at hprod ⊢
    simp at hprod ⊢
    have hpx : input.p.x ≠ 0 := hprod.1.1
    have hqx : input.q.x ≠ 0 := hprod.1.2
    have hxdiff : input.q.x - input.p.x ≠ 0 := hprod.2
    have hx : input.q.x ≠ input.p.x := fun h => hxdiff (sub_eq_zero.mpr h)
    simp [hpx, hqx, hx]
  constructor
  · intro hprod
    dsimp [rowValue, outputValue, lambdaValue] at hprod ⊢
    simp at hprod ⊢
    have hpx : input.p.x ≠ 0 := hprod.1.1
    have hqx : input.q.x ≠ 0 := hprod.1.2
    have hysum : input.q.y + input.p.y ≠ 0 := hprod.2
    by_cases hx : input.q.x = input.p.x
    · have hsame := pallas_y_eq_or_neg_of_same_x hp hq hpx hqx hx
      rcases hsame with hy | hy
      · have hnotInv : ¬(input.q.x = input.p.x ∧ input.q.y = -input.p.y) := by
          intro hinv
          apply hysum
          rw [hinv.2]
          ring
        have hpy : input.p.y ≠ 0 :=
          Point.y_ne_zero_of_valid_of_x_ne_zero hp hpx
        have hnotY : input.q.y ≠ -input.p.y := fun h => hnotInv ⟨hx, h⟩
        simp [hpx, hx, hnotY, hpy]
      · exact False.elim (hysum (by rw [hy]; ring))
    · have hnotInv : ¬(input.q.x = input.p.x ∧ input.q.y = -input.p.y) := by
        exact fun h => hx h.1
      simp [hpx, hqx, hx]
  constructor
  · intro hflag
    dsimp [rowValue, outputValue] at hflag ⊢
    simp at hflag ⊢
    by_cases hpx : input.p.x = 0
    · simp [hpx]
    · have hcontra : input.p.x * input.p.x⁻¹ = 1 := by
        field_simp [hpx]
      exact False.elim (hflag hcontra)
  constructor
  · intro hflag
    dsimp [rowValue, outputValue] at hflag ⊢
    by_cases hpx : input.p.x = 0
    · have hpy := Point.y_eq_zero_of_valid_of_x_eq_zero hp hpx
      by_cases hqx : input.q.x = 0
      · have hqy := Point.y_eq_zero_of_valid_of_x_eq_zero hq hqx
        have hpEq : input.p = Point.zero := by
          rw [Point.mk.injEq]
          exact ⟨hpx, hpy⟩
        have hqEq : input.q = Point.zero := by
          rw [Point.mk.injEq]
          exact ⟨hqx, hqy⟩
        simp [Point.zero, hpEq, hqEq]
      · have hcontra : input.q.x * input.q.x⁻¹ = 1 := by
          field_simp [hqx]
        exact False.elim (hflag hcontra)
    · by_cases hqx : input.q.x = 0
      · simp [hpx, hqx]
      · have hcontra : input.q.x * input.q.x⁻¹ = 1 := by
          field_simp [hqx]
        exact False.elim (hflag hcontra)
  · intro hflag
    dsimp [rowValue, outputValue] at hflag ⊢
    simp at hflag ⊢
    by_cases hpx : input.p.x = 0
    · have hpy := Point.y_eq_zero_of_valid_of_x_eq_zero hp hpx
      by_cases hqx : input.q.x = 0
      · have hqy := Point.y_eq_zero_of_valid_of_x_eq_zero hq hqx
        simp [hpx, hqx, hqy]
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
          · simp [Point.zero, hpx, hx, hy]
          · have hsame := pallas_y_eq_or_neg_of_same_x hp hq hpx hqx hx
            rcases hsame with hyeq | hyneg
            · have hysum : input.q.y + input.p.y ≠ 0 := by
                rw [hyeq]
                exact pallas_add_self_ne_zero
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

theorem spec_eq_outputValue_pallas {row : Gate.Input Fp}
    (hp : Pallas.Valid row.p.coords) (hq : Pallas.Valid row.q.coords) (hrow : Spec row) :
    row.r = outputValue { p := row.p, q := row.q } := by
  dsimp [Gate.Input.p, Gate.Input.q, Gate.Input.r] at hp hq hrow ⊢
  rcases hrow with ⟨hSlope, hTangent, hNonexceptionalDiff, hNonexceptionalSum,
    hLeftIdentity, hRightIdentity, hInverse⟩
  by_cases hpx : row.x_p = 0
  · have hflag : row.p.x * row.beta ≠ 1 := by
      simp [Gate.Input.p, hpx]
    have hr := hLeftIdentity hflag
    unfold outputValue
    simp [hpx]
    simpa [Point.mk.injEq, Gate.Input.q, Gate.Input.r] using hr
  · by_cases hqx : row.x_qr.curr = 0
    · have hflag : row.q.x * row.gamma ≠ 1 := by
        simp [Gate.Input.q, hqx]
      have hr := hRightIdentity hflag
      unfold outputValue
      simp [hpx, hqx]
      simpa [Point.mk.injEq, Gate.Input.p, Gate.Input.r] using hr
    · by_cases hinv : row.x_qr.curr = row.x_p ∧ row.y_qr.curr = -row.y_p
      · have hflag :
            (row.q.x - row.p.x) * row.alpha + (row.q.y + row.p.y) * row.delta ≠ 1 := by
          rcases hinv with ⟨hx, hy⟩
          simp [Gate.Input.p, Gate.Input.q, hx, hy]
        have hr := hInverse hflag
        have hr0 : row.r = Point.zero := by
          rw [Point.mk.injEq]
          exact hr
        unfold outputValue
        simp [hpx, hinv]
        simpa [Point.mk.injEq, Gate.Input.r] using hr0
      · have hr :
            row.r.x = row.lambda * row.lambda - row.p.x - row.q.x ∧
              row.r.y = row.lambda * (row.p.x - row.r.x) - row.p.y := by
          by_cases hx : row.x_qr.curr = row.x_p
          · have hsame := pallas_y_eq_or_neg_of_same_x hp hq hpx hqx hx
            rcases hsame with hy | hy
            · have hysum : row.q.y + row.p.y ≠ 0 := by
                simp [Gate.Input.p, Gate.Input.q] at hy ⊢
                rw [hy]
                exact pallas_add_self_ne_zero
                  (Point.y_ne_zero_of_valid_of_x_ne_zero hp hpx)
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
              mul_ne_zero pallas_two_ne_zero hpy
            field_simp [hden, pallas_two_ne_zero]
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
        unfold outputValue
        simp [hpx, hqx, hinv]
        constructor
        · exact hr.1
        · rw [← hr.1]
          exact hr.2

theorem spec_eq_add_pallas {row : Gate.Input Fp}
    (hp : Pallas.Valid row.p.coords) (hq : Pallas.Valid row.q.coords) (hrow : Spec row) :
    row.r.coords = Pallas.add row.p.coords row.q.coords := by
  rw [spec_eq_outputValue_pallas hp hq hrow]
  exact outputValue_eq_add hp hq

theorem spec_valid_pallas {row : Gate.Input Fp}
    (hp : Pallas.Valid row.p.coords) (hq : Pallas.Valid row.q.coords) (hrow : Spec row) :
    Pallas.Valid row.r.coords := by
  rw [spec_eq_outputValue_pallas hp hq hrow]
  exact outputValue_valid_pallas hp hq

def main (input : Var Input Fp) :
    Circuit Fp (Var Point Fp) := do
  let p <== input.p
  let q <== input.q
  let r ← witness fun env =>
    (rowValue { p := eval env p, q := eval env q }).r
  let lambda ← witnessField fun env =>
    (rowValue { p := eval env p, q := eval env q }).lambda
  let alpha ← witnessField fun env =>
    (rowValue { p := eval env p, q := eval env q }).alpha
  let beta ← witnessField fun env =>
    (rowValue { p := eval env p, q := eval env q }).beta
  let gamma ← witnessField fun env =>
    (rowValue { p := eval env p, q := eval env q }).gamma
  let delta ← witnessField fun env =>
    (rowValue { p := eval env p, q := eval env q }).delta
  Gate.circuit {
    x_p := p.x
    y_p := p.y
    x_qr := { curr := q.x, next := r.x }
    y_qr := { curr := q.y, next := r.y }
    lambda
    alpha
    beta
    gamma
    delta
  }
  return r

def Assumptions (input : Input Fp) : Prop :=
  Pallas.Valid input.p.coords ∧ Pallas.Valid input.q.coords

def Spec (input : Input Fp) (output : Point Fp) : Prop :=
  Pallas.Valid output.coords ∧
    output.coords = Pallas.add input.p.coords input.q.coords

instance elaborated : ElaboratedCircuit Fp Input Point main := by
  elaborate_circuit

theorem soundness : Soundness Fp main Assumptions Spec := by
  circuit_proof_start [main, Assumptions, Spec, Pallas.Valid,
    Gate.circuit, Gate.Spec, spec_eq_add_pallas, spec_valid_pallas]
  rcases h_assumptions with ⟨hp, hq⟩
  rcases h_holds with ⟨hpCopyEq, hqCopyEq, hrow⟩
  let pCopy : Point Fp := {
    x := Expression.eval env (varFromOffset Point i₀).x
    y := Expression.eval env (varFromOffset Point i₀).y
  }
  let qCopy : Point Fp := {
    x := Expression.eval env (varFromOffset Point (i₀ + 2)).x
    y := Expression.eval env (varFromOffset Point (i₀ + 2)).y
  }
  let row : Gate.Input Fp := {
    x_p := pCopy.x
    y_p := pCopy.y
    x_qr := { curr := qCopy.x, next := env.get (i₀ + 2 + 2) }
    y_qr := { curr := qCopy.y, next := env.get (i₀ + 2 + 2 + 1) }
    lambda := env.get (i₀ + 2 + 2 + 1 + 1)
    alpha := env.get (i₀ + 2 + 2 + 1 + 1 + 1)
    beta := env.get (i₀ + 2 + 2 + 1 + 1 + 1 + 1)
    gamma := env.get (i₀ + 2 + 2 + 1 + 1 + 1 + 1 + 1)
    delta := env.get (i₀ + 2 + 2 + 1 + 1 + 1 + 1 + 1 + 1)
  }
  have hpCopy : Pallas.Valid pCopy.coords := by
    simpa [pCopy, hpCopyEq] using hp
  have hqCopy : Pallas.Valid qCopy.coords := by
    simpa [qCopy, hqCopyEq] using hq
  have hvalid := spec_valid_pallas (row := row) hpCopy hqCopy hrow
  have hcoords := spec_eq_add_pallas (row := row) hpCopy hqCopy hrow
  exact ⟨by simpa [row] using hvalid,
    by simpa [row, pCopy, qCopy, hpCopyEq, hqCopyEq] using hcoords⟩

theorem completeness : Completeness Fp main Assumptions := by
  circuit_proof_start [main, Assumptions, Spec, Pallas.Valid,
    Gate.circuit, Gate.Spec, rowValue_spec_pallas]
  rcases h_assumptions with ⟨hp, hq⟩
  rcases input_p with ⟨px, py⟩
  rcases input_q with ⟨qx, qy⟩
  simp_all [circuit_norm, explicit_provable_type]
  have hrow := rowValue_spec_pallas
    (input := { p := { x := px, y := py }, q := { x := qx, y := qy } }) hp hq
  simpa [Gate.Spec, rowValue] using hrow

def circuit : FormalCircuit Fp Input Point where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end Orchard.Ecc.Add
