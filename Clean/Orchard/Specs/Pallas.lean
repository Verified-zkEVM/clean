import Clean.Orchard.Specs.CompElliptic.Curves.Pasta

/-!
# Orchard-facing Pallas vocabulary

The vendored CompElliptic layer states curve facts over coordinate pairs. This module
defines the predicates in the point language we want to use for Orchard protocol specs,
and provides bridge lemmas back to CompElliptic when theorem support is needed.
-/

namespace Orchard

abbrev Fp := CompElliptic.Fields.Pasta.PallasBaseField
abbrev Fq := CompElliptic.Fields.Pasta.PallasScalarField

/-- Pallas base-field canonicity threshold used by Orchard range-check gates. -/
def tP : Fp := 45560315531419706090280762371685220353

def pallasB : Fp := 5

/--
This is the point vocabulary used by Orchard-facing specs and circuit interfaces. It is
generic in the coordinate type so the same structure can be used for concrete field values
and circuit expressions.
-/
structure Point (F : Type) where
  x : F
  y : F

namespace Point
variable {F : Type}

def coords (point : Point F) : F × F :=
  (point.x, point.y)

def zero [Zero F] : Point F := { x := 0, y := 0 }

instance [Zero F] : Zero (Point F) := ⟨zero⟩

theorem ext_coords {p q : Point F} (h : p.coords = q.coords) : p = q := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simpa [Point.coords, Prod.ext_iff, mk.injEq] using h

/-- The Pallas affine curve equation, phrased over Orchard `Point`s. -/
def OnCurve (point : Point Fp) : Prop :=
  point.y ^ 2 = point.x ^ 3 + 5

/-- A representable Pallas group point: affine on-curve, or the `(0, 0)` identity sentinel. -/
def Valid (point : Point Fp) : Prop :=
  OnCurve point ∨ point = 0

open CompElliptic.Curves.Pasta CompElliptic.CurveForms

theorem onCurve_iff (point : Point Fp) :
    point.OnCurve ↔
      Pallas.OnCurve point.coords := by
  simp only [OnCurve, Point.coords, Pallas.OnCurve,
    CompElliptic.CurveForms.ShortWeierstrass.OnCurve,
    Pallas.a, Pallas.b, zero_mul, add_zero]

theorem valid_iff (point : Point Fp) :
    Valid point ↔ Pallas.Valid point.coords := by
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
  exact Pallas.not_onCurve_zero ((onCurve_iff 0).mp h)

theorem no_onCurve_x_zero (y : Fp) : ¬ OnCurve ({ x := 0, y } : Point Fp) := by
  intro h
  exact Pallas.no_onCurve_x_zero y ((onCurve_iff { x := 0, y }).mp h)

theorem onCurve_ne_zero {point : Point Fp} (h : OnCurve point) :
    point ≠ 0 := by
  intro hzero
  exact not_onCurve_zero (hzero ▸ h)

def ofSW (point : ShortWeierstrass.SWPoint
    CompElliptic.Curves.Pasta.Pallas.curve) : Point Fp :=
  { x := point.x, y := point.y }

variable {F : Type} [Field F]

def neg [Neg F] (point : Point F) : Point F where
  x := point.x
  y := -point.y

instance [Neg F] : Neg (Point F) := ⟨neg⟩

def add (p q : Point Fp) : Point Fp :=
  let coords := ShortWeierstrass.add Pallas.a p.coords q.coords
  { x := coords.1, y := coords.2 }

instance : Add (Point Fp) := ⟨add⟩

@[simp] theorem coords_add (p q : Point Fp) :
    (p + q).coords = ShortWeierstrass.add Pallas.a p.coords q.coords := rfl

instance : Sub (Point Fp) where
  sub p q := add p (neg q)

def nsmul (n : ℕ) (point : Point Fp) : Point Fp :=
  let coords := ShortWeierstrass.smul Pallas.a n point.coords
  { x := coords.1, y := coords.2 }

instance : SMul ℕ (Point Fp) := ⟨nsmul⟩

end Orchard.Point
