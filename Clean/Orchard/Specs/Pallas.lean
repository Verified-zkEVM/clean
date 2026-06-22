import Clean.Orchard.Specs.CompElliptic.Curves.Pasta

/-!
# Orchard-facing Pallas vocabulary

The vendored CompElliptic layer states curve facts over coordinate pairs. This module
defines the predicates in the point language we want to use for Orchard protocol specs,
and provides bridge lemmas back to CompElliptic when theorem support is needed.
-/

namespace Orchard

open CompElliptic.CurveForms
open ShortWeierstrass (SWPoint)
open CompElliptic.Curves.Pasta

abbrev Fp := CompElliptic.Fields.Pasta.PallasBaseField
abbrev Fq := CompElliptic.Fields.Pasta.PallasScalarField

def pallasB : Fp := 5
def pallasA : Fp := 0

/-- Pallas base-field canonicity threshold used by Orchard range-check gates. -/
def tP : Fp := 45560315531419706090280762371685220353

instance : (ShortWeierstrass.toW pallasA pallasB).IsElliptic :=
  inferInstanceAs <| WeierstrassCurve.IsElliptic <|
  (ShortWeierstrass.toW Pallas.curve.A Pallas.curve.B)

/--
This is the point vocabulary used by Orchard-facing specs and circuit interfaces. It is
generic in the coordinate type so the same structure can be used for concrete field values
and circuit expressions.
-/
structure Point (F : Type) where
  x : F
  y : F
deriving BEq, DecidableEq, Inhabited, Repr

namespace Point
variable {F : Type}

def coords (point : Point F) : F × F :=
  (point.x, point.y)

theorem ext_coords {p q : Point F} (h : p.coords = q.coords) : p = q := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simpa [Point.coords, Prod.ext_iff, mk.injEq] using h

def zero [Zero F] : Point F := { x := 0, y := 0 }

instance [Zero F] : Zero (Point F) := ⟨zero⟩

lemma zero_def [Zero F] : (0 : Point F) = { x := 0, y := 0 } := rfl

/-- The Pallas affine curve equation, phrased over Orchard `Point`s. -/
def OnCurve (point : Point Fp) : Prop :=
  point.y ^ 2 = point.x ^ 3 + 5

/-- A representable Pallas group point: affine on-curve, or the `(0, 0)` identity sentinel. -/
def Valid (point : Point Fp) : Prop :=
  OnCurve point ∨ point = 0

theorem onCurve_iff (point : Point Fp) :
    point.OnCurve ↔
      ShortWeierstrass.OnCurve pallasA pallasB point.coords := by
  simp only [OnCurve, Point.coords,
    CompElliptic.CurveForms.ShortWeierstrass.OnCurve,
    pallasA, pallasB, zero_mul, add_zero]

theorem valid_iff (point : Point Fp) :
    Valid point ↔ ShortWeierstrass.Valid pallasA pallasB point.coords := by
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl ((onCurve_iff point).mp h)
    · exact Or.inr (by rw [h]; rfl)
  · intro h
    rcases h with h | h
    · exact Or.inl ((onCurve_iff point).mpr h)
    · exact Or.inr (Point.ext_coords h)

theorem not_onCurve_zero : ¬ OnCurve (0 : Point Fp) := by
  intro h
  exact ShortWeierstrass.not_onCurve_zero (by decide) ((onCurve_iff 0).mp h)

theorem no_onCurve_of_x_zero (y : Fp) : ¬ OnCurve ({ x := 0, y } : Point Fp) := by
  intro h
  exact Pallas.no_onCurve_x_zero y ((onCurve_iff { x := 0, y }).mp h)

theorem ne_zero_of_onCurve {point : Point Fp} :
    point.OnCurve → point ≠ 0 := by
  intro h hzero
  exact not_onCurve_zero (hzero ▸ h)

def ofSW (point : SWPoint Pallas.curve) : Point Fp :=
  { x := point.x, y := point.y }

def neg [Neg F] (point : Point F) : Point F where
  x := point.x
  y := -point.y

instance [Neg F] : Neg (Point F) := ⟨neg⟩

lemma neg_def (point : Point Fp) :
  -point = {
    x := (ShortWeierstrass.neg point.coords).1,
    y := (ShortWeierstrass.neg point.coords).2 } := rfl


def add (p q : Point Fp) : Point Fp :=
  let coords := ShortWeierstrass.add pallasA p.coords q.coords
  { x := coords.1, y := coords.2 }

instance : Add (Point Fp) := ⟨add⟩

lemma add_def (p q : Point Fp) :
  p + q = {
    x := (ShortWeierstrass.add pallasA (p.x, p.y) (q.x, q.y)).1,
    y := (ShortWeierstrass.add pallasA (p.x, p.y) (q.x, q.y)).2 } := rfl

@[simp] theorem coords_add (p q : Point Fp) :
    (p + q).coords = ShortWeierstrass.add pallasA p.coords q.coords := rfl

theorem valid_add {p q : Point Fp} (hp : p.Valid) (hq : q.Valid) :
    (p + q).Valid := by
  exact (valid_iff (p + q)).mpr
    (ShortWeierstrass.valid_add
      ((valid_iff p).mp hp) ((valid_iff q).mp hq))

theorem add_comm {p q : Point Fp} (hp : p.Valid) (hq : q.Valid) :
    p + q = q + p := by
  apply ext_coords
  rw [coords_add, coords_add]
  exact ShortWeierstrass.add_comm ((valid_iff p).mp hp) ((valid_iff q).mp hq)

theorem valid_neg {p : Point Fp} (hp : p.Valid) :
    (-p).Valid := by
  exact (valid_iff (-p)).mpr
    (ShortWeierstrass.valid_neg ((valid_iff p).mp hp))

instance : Sub (Point Fp) where
  sub p q := add p (neg q)

def nsmul (n : ℕ) (point : Point Fp) : Point Fp :=
  let coords := ShortWeierstrass.smul pallasA n point.coords
  { x := coords.1, y := coords.2 }

instance : SMul ℕ (Point Fp) := ⟨nsmul⟩

def incompleteAdd (p q : Point Fp) : Point Fp :=
  let slope := (q.y - p.y) * (q.x - p.x)⁻¹
  let xR := slope * slope - p.x - q.x
  let yR := slope * (p.x - xR) - p.y
  { x := xR, y := yR }

theorem incompleteAdd_eq_add {p q : Point Fp}
    (hp : p ≠ 0) (hq : q ≠ 0) (hx : p.x ≠ q.x) :
    incompleteAdd p q = p + q := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp only [incompleteAdd, zero_def, add_def, ShortWeierstrass.add] at *
  have hp0 : ¬(px, py) = (0, 0) := by grind
  have hq0 : ¬(qx, qy) = (0, 0) := by grind
  rw [if_neg hp0, if_neg hq0]
  rw [if_neg hx, mk.injEq]
  constructor <;> ring

theorem incompleteAdd_onCurve {p q : Point Fp}
    (hp : p.OnCurve) (hq : q.OnCurve) (hx : p.x ≠ q.x) :
    (incompleteAdd p q).OnCurve := by
  have hpNonId : p ≠ 0 := ne_zero_of_onCurve hp
  have hqNonId : q ≠ 0 := ne_zero_of_onCurve hq
  rw [incompleteAdd_eq_add hpNonId hqNonId hx]
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp only [onCurve_iff, coords, add_def] at hp hq hx ⊢
  replace hpNonId : (px, py) ≠ (0, 0) := by convert hpNonId; simp [zero_def]
  replace hqNonId : (qx, qy) ≠ (0, 0) := by convert hqNonId; simp [zero_def]
  have hxy : ¬(px = qx ∧ py + qy = 0) := by intro h; exact hx h.1
  rw [ShortWeierstrass.add_eq_addXY (b:=pallasB) hpNonId hqNonId hxy,
      ← ShortWeierstrass.equation_toW]
  replace hxy : ¬(px = qx ∧ py = WeierstrassCurve.Affine.negY
    (ShortWeierstrass.toW pallasA pallasB) qx qy) := by
    rintro ⟨hxeq, _⟩
    exact hx hxeq
  have ⟨ hns, _ ⟩ : WeierstrassCurve.Affine.Equation _ _ _ ∧ _ := WeierstrassCurve.Affine.nonsingular_add
    (ShortWeierstrass.nonsingular_toW hp) (ShortWeierstrass.nonsingular_toW hq) hxy
  exact hns

theorem y_eq_zero_of_valid_of_x_eq_zero {point : Point Fp} :
    point.Valid → point.x = 0 → point.y = 0 := by
  intro hPoint hx
  rcases point with ⟨x, y⟩
  simp only [Point.valid_iff, Point.coords] at hPoint hx ⊢
  rcases hPoint with hCurve | hIdentity
  · rw [hx] at hCurve
    exact False.elim (Point.no_onCurve_of_x_zero y ((Point.onCurve_iff { x := 0, y }).mpr hCurve))
  · simp_all

theorem y_ne_zero_of_valid_of_x_ne_zero {point : Point Fp} :
    point.Valid → point.x ≠ 0 → point.y ≠ 0 := by
  intro hPoint hx
  rcases point with ⟨x, y⟩
  simp only [Point.valid_iff, Point.coords] at hPoint hx ⊢
  rintro rfl
  rcases hPoint with hCurve | hIdentity
  · apply Pallas.no_onCurve_y_zero x hCurve
  · simp_all

theorem x_zero_iff_y_zero_of_valid {point : Point Fp} :
    point.Valid → (point.x = 0 ↔ point.y = 0) := by
  intro hPoint
  constructor
  · exact y_eq_zero_of_valid_of_x_eq_zero hPoint
  · contrapose!
    exact y_ne_zero_of_valid_of_x_ne_zero hPoint

end Point

theorem two_ne_zero : (2 : Fp) ≠ 0 := by decide

theorem add_self_ne_zero {y : Fp} (hy : y ≠ 0) :
    y + y ≠ 0 := by
  intro h
  have hmul : (2 : Fp) * y = 0 := by linear_combination h
  simp_all [two_ne_zero]

namespace Point
theorem y_eq_or_neg_of_same_x {p q : Point Fp}
    (hp : p.Valid) (hq : q.Valid)
    (hpx : p.x ≠ 0) (hqx : q.x ≠ 0) (hx : q.x = p.x) :
    q.y = p.y ∨ q.y = -p.y := by
  have hpCurve : p.OnCurve := by
    rcases hp with hCurve | hIdentity
    · exact hCurve
    · exact False.elim (hpx (congrArg Point.x hIdentity))
  have hqCurve : q.OnCurve := by
    rcases hq with hCurve | hIdentity
    · exact hCurve
    · exact False.elim (hqx (congrArg Point.x hIdentity))
  unfold Point.OnCurve at hpCurve hqCurve
  have hsquare : (q.y - p.y) * (q.y + p.y) = 0 := by
    rw [hx] at hqCurve
    linear_combination hqCurve - hpCurve
  rcases mul_eq_zero.mp hsquare with h | h
  · left
    exact sub_eq_zero.mp h
  · right
    linear_combination h

def toSW (point : Point Fp) (h : point.Valid) : SWPoint Pallas.curve where
  x := point.x
  y := point.y
  onCurve := (valid_iff point).mp h

@[simp] theorem toSW_add {p q : Point Fp} (hp : p.Valid) (hq : q.Valid) :
    (p + q).toSW (valid_add hp hq) = p.toSW hp + q.toSW hq := by
  simp only [toSW, add_def]
  rfl

theorem valid_zero : (0 : Point Fp).Valid := Or.inr rfl

@[simp] theorem toSW_zero : toSW 0 valid_zero = 0 := by
  simp only [toSW, zero_def]
  rfl

theorem toSW_x (point : Point Fp) (h : point.Valid) : (toSW point h).x = point.x := rfl
theorem toSW_y (point : Point Fp) (h : point.Valid) : (toSW point h).y = point.y := rfl

theorem toSW_neg {p : Point Fp} (hp : p.Valid) :
    (-p).toSW (valid_neg hp) = -(p.toSW hp) := by
  simp only [toSW, neg_def]
  rfl
end Point

end Orchard
