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

def coords (point : Point F) : F × F := (point.x, point.y)

theorem ext_coords {p q : Point F} (h : p.coords = q.coords) : p = q := by
  rw [mk.injEq]
  simp_all [coords]

lemma ext_coords_iff {p q : Point F} : p.coords = q.coords ↔ p = q :=
  ⟨ ext_coords, by rintro rfl; rfl ⟩
lemma ext_coords_iff_left {p : Point F} {x y : F} : p.coords = (x, y) ↔ p = { x, y } :=
  ext_coords_iff (q := { x, y })
lemma ext_coords_iff_right {p : Point F} {x y : F} : (x, y) = p.coords ↔ { x, y } = p :=
  ext_coords_iff (p := { x, y })

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
    point.OnCurve ↔ ShortWeierstrass.OnCurve pallasA pallasB point.coords := by
  simp only [OnCurve, coords, ShortWeierstrass.OnCurve,
    pallasA, pallasB, zero_mul, add_zero]

theorem valid_iff (point : Point Fp) :
    Valid point ↔ ShortWeierstrass.Valid pallasA pallasB point.coords := by
  simp_rw [Valid, ShortWeierstrass.Valid, onCurve_iff, zero_def, ext_coords_iff_left]

theorem no_onCurve_of_x_zero (y : Fp) : ¬ OnCurve { x := 0, y } := by
  simp only [onCurve_iff, coords, pallasB]
  exact Pallas.no_onCurve_x_zero y

theorem not_onCurve_zero : ¬ OnCurve 0 := by
  apply no_onCurve_of_x_zero

theorem ne_zero_of_onCurve {point : Point Fp} :
    point.OnCurve → point ≠ 0 := by
  contrapose!
  rintro rfl
  exact not_onCurve_zero

lemma onCurve_of_valid_of_ne_zero {point : Point Fp} :
    point.Valid → point ≠ 0 → point.OnCurve := by
  rintro (hCurve | hIdentity) hNeZero
  · exact hCurve
  · exact False.elim (hNeZero hIdentity)

def ofSW (point : SWPoint Pallas.curve) : Point Fp :=
  { x := point.x, y := point.y }

def ofCoords (xy : Fp × Fp) : Point Fp := { x := xy.1, y := xy.2 }

@[simp] lemma ofCoords_x (xy : Fp × Fp) : (ofCoords xy).x = xy.1 := rfl
@[simp] lemma ofCoords_y (xy : Fp × Fp) : (ofCoords xy).y = xy.2 := rfl
@[simp] lemma ofCoords_coords (xy : Fp × Fp) : (ofCoords xy).coords = xy := rfl

def neg [Neg F] (point : Point F) : Point F :=
  { x := point.x, y := -point.y }

instance [Neg F] : Neg (Point F) := ⟨neg⟩

lemma neg_def (point : Point Fp) :
  -point = ofCoords (ShortWeierstrass.neg point.coords) := rfl
lemma neg_x (point : Point Fp) : (-point).x = point.x := rfl
lemma neg_y (point : Point Fp) : (-point).y = -point.y := rfl

def add (p q : Point Fp) : Point Fp :=
  ofCoords (ShortWeierstrass.add pallasA p.coords q.coords)

instance : Add (Point Fp) := ⟨add⟩

lemma add_def (p q : Point Fp) :
  p + q = ofCoords (ShortWeierstrass.add pallasA p.coords q.coords) := rfl

theorem coords_add (p q : Point Fp) :
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

lemma nsmul_def (n : ℕ) (point : Point Fp) :
  n • point = ofCoords (ShortWeierstrass.smul pallasA n point.coords) := rfl

def nondegenerateAdd {K : Type} [Sub K] [Mul K] [Inv K] (p q : Point K) : Point K :=
  let slope := (q.y - p.y) * (q.x - p.x)⁻¹
  let xR := slope * slope - p.x - q.x
  let yR := slope * (p.x - xR) - p.y
  { x := xR, y := yR }

theorem nondegenerateAdd_eq_add {p q : Point Fp}
    (hp : p ≠ 0) (hq : q ≠ 0) (hx : p.x ≠ q.x) :
    nondegenerateAdd p q = p + q := by
  rcases p with ⟨px, py⟩
  rcases q with ⟨qx, qy⟩
  simp only [nondegenerateAdd, zero_def, add_def, ofCoords, coords, ShortWeierstrass.add] at *
  have hp0 : ¬(px, py) = (0, 0) := by grind
  have hq0 : ¬(qx, qy) = (0, 0) := by grind
  rw [if_neg hp0, if_neg hq0]
  rw [if_neg hx, mk.injEq]
  constructor <;> ring

theorem nondegenerateAdd_onCurve {p q : Point Fp}
    (hp : p.OnCurve) (hq : q.OnCurve) (hx : p.x ≠ q.x) :
    (nondegenerateAdd p q).OnCurve := by
  have hpNonId : p ≠ 0 := ne_zero_of_onCurve hp
  have hqNonId : q ≠ 0 := ne_zero_of_onCurve hq
  rw [nondegenerateAdd_eq_add hpNonId hqNonId hx]
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

theorem toSW_x (point : Point Fp) (h : point.Valid) : (toSW point h).x = point.x := rfl
theorem toSW_y (point : Point Fp) (h : point.Valid) : (toSW point h).y = point.y := rfl

theorem ext_toSW_iff {p q : Point Fp} (hp : p.Valid) (hq : q.Valid) :
    p = q ↔ p.toSW hp = q.toSW hq := by
  constructor
  · rintro rfl
    rfl
  · intro h
    rw [mk.injEq]
    simp_all [toSW]

theorem toSW_add {p q : Point Fp} (hp : p.Valid) (hq : q.Valid) :
    (p + q).toSW (valid_add hp hq) = p.toSW hp + q.toSW hq := by
  simp only [toSW, add_def]
  rfl

theorem valid_zero : (0 : Point Fp).Valid := Or.inr rfl

theorem toSW_zero : toSW 0 valid_zero = 0 := by
  simp only [toSW, zero_def]
  rfl

theorem toSW_neg {p : Point Fp} (hp : p.Valid) :
    (-p).toSW (valid_neg hp) = -(p.toSW hp) := by
  simp only [toSW, neg_def]
  rfl

theorem valid_nsmul {p : Point Fp} (hp : p.Valid) (n : ℕ) :
    (n • p).Valid := by
  exact (valid_iff (n • p)).mpr
    (ShortWeierstrass.valid_smul ((valid_iff p).mp hp) n)

lemma ofCoords_toSW (P : SWPoint Pallas.curve) {hP} :
  (ofCoords (P.x, P.y)).toSW hP = P := by rfl

theorem toSW_nsmul {p : Point Fp} (hp : p.Valid) (n : ℕ) :
    (n • p).toSW (valid_nsmul hp n) = n • (p.toSW hp) := by
  simp_rw [nsmul_def, coords]
  set P : SWPoint Pallas.curve := p.toSW hp
  show (ofCoords (ShortWeierstrass.smul Pallas.curve.A n (P.x, P.y))).toSW _ = n • P
  simp_rw [← ShortWeierstrass.coords_nsmul, ofCoords_toSW]

theorem nsmul_add_nsmul {P : Point Fp} (hP : P.OnCurve) (a b : ℕ) :
    a • P + b • P = (a + b) • P := by
  apply (ext_toSW_iff
    (valid_add (valid_nsmul (.inl hP) a) (valid_nsmul (.inl hP) b))
    (valid_nsmul (.inl hP) (a + b))).mpr
  rw [toSW_add (valid_nsmul (.inl hP) a) (valid_nsmul (.inl hP) b),
    toSW_nsmul (.inl hP) a, toSW_nsmul (.inl hP) b, toSW_nsmul (.inl hP) (a + b)]
  rw [add_nsmul]

theorem nsmul_add_coords {P : Point Fp} (hP : P.OnCurve) {a b c : ℕ}
    (h : a + b = c) :
    ShortWeierstrass.add pallasA ((a • P).x, (a • P).y)
        ((b • P).x, (b • P).y) = (c • P).coords := by
  change (a • P + b • P).coords = (c • P).coords
  rw [nsmul_add_nsmul hP, h]

theorem add_coords_eq {P Q R : Point Fp} (h : P + Q = R) :
    ShortWeierstrass.add pallasA (P.x, P.y) (Q.x, Q.y) = R.coords := by
  change (P + Q).coords = R.coords
  rw [h]

theorem nsmul_add_one {P : Point Fp} (hP : P.OnCurve) (m : ℕ) :
    m • P + P = (m + 1) • P := by
  simpa using nsmul_add_nsmul hP m 1

theorem nsmul_add_neg_one {P : Point Fp} (hP : P.OnCurve) {m : ℕ} (h2 : 2 ≤ m) :
    m • P + -P = (m - 1) • P := by
  apply (ext_toSW_iff
    (valid_add (valid_nsmul (.inl hP) m) (valid_neg (.inl hP)))
    (valid_nsmul (.inl hP) (m - 1))).mpr
  rw [toSW_add (valid_nsmul (.inl hP) m) (valid_neg (.inl hP)),
    toSW_neg (.inl hP), toSW_nsmul (.inl hP) m, toSW_nsmul (.inl hP) (m - 1)]
  have hm : m • P.toSW (.inl hP) = (m - 1) • P.toSW (.inl hP) + P.toSW (.inl hP) := by
    rw [← succ_nsmul, Nat.sub_add_cancel (by omega)]
  rw [hm, add_neg_cancel_right]

theorem neg_ne_zero_of_ne_zero {P : Point Fp} (hP : P ≠ 0) : -P ≠ 0 := by
  intro h
  apply hP
  cases P
  rw [zero_def, mk.injEq]
  exact ⟨congrArg Point.x h, neg_eq_zero.mp (congrArg Point.y h)⟩

-- so we can use the cute ⊥ symbol for `none`
instance {α : Type} : Bot (Option α) := ⟨none⟩

-- but we remove it in proofs
@[simp] theorem bot_eq_none {α : Type} : (⊥ : Option α) = none := rfl

/-- Incomplete addition `⸭` for Sinsemilla (protocol spec §5.4.1.9):
`⊥` if an operand is the identity or the `x`-coordinates collide (equal or opposite
points), otherwise the group operation. `⊥` operands are handled by `Option.bind` at
use sites. -/
def incompleteAdd (p q : Point Fp) : Option (Point Fp) :=
  if p = 0 ∨ q = 0 ∨ p.x = q.x then ⊥ else p + q

infixl:65 " ⸭ " => incompleteAdd

lemma incompleteAdd_def (p q : Point Fp) :
    p ⸭ q = if p = 0 ∨ q = 0 ∨ p.x = q.x then ⊥ else some (p + q) := rfl

theorem incompleteAdd_some {p q : Point Fp}
    (hX : p ≠ 0) (hY : q ≠ 0) (hxy : p.x ≠ q.x) :
    p ⸭ q = some (p + q) := by
  rw [incompleteAdd_def, if_neg]
  push Not
  exact ⟨hX, hY, hxy⟩

/-- One incomplete double-and-add step: `(acc ⸭ p) ⸭ acc`. -/
def doubleAndAdd (acc p : Point Fp) : Option (Point Fp) := do
  let t ← acc ⸭ p
  t ⸭ acc

/-! ### Pallas group order -/

open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

/--
**Axiom**: the Pallas curve group has exactly `q = PALLAS_SCALAR_CARD` points.

This is the published point count of the Pallas curve. The vendored CompElliptic
formalization has no point counting, so this is the one central trust assumption behind
scalar-multiplication circuit proofs; all consumers needing order facts derive them from
here (see `addOrderOf_eq`).
-/
axiom pallas_natCard :
  Nat.card (ShortWeierstrass.SWPoint Pallas.curve) = PALLAS_SCALAR_CARD

/-- Every non-identity Pallas point generates the full prime-order group. -/
theorem addOrderOf_eq {P : ShortWeierstrass.SWPoint Pallas.curve} (h : P ≠ 0) :
    addOrderOf P = PALLAS_SCALAR_CARD := by
  have hdvd := addOrderOf_dvd_natCard P
  rw [pallas_natCard] at hdvd
  rcases CompElliptic.Fields.Pasta.PALLAS_SCALAR_is_prime.eq_one_or_self_of_dvd
      _ hdvd with h1 | hq
  · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) h
  · exact hq

theorem nsmul_eq_zero_iff {P : Point Fp} (hP : P.OnCurve) (n : ℕ) :
    n • P = 0 ↔ PALLAS_SCALAR_CARD ∣ n := by
  rw [ext_toSW_iff (valid_nsmul (.inl hP) n) valid_zero,
    toSW_zero, toSW_nsmul (.inl hP)]
  set p := P.toSW (.inl hP)
  have hp : p ≠ 0 := by
    intro h
    simp only [p, ← toSW_zero, ← ext_toSW_iff] at h
    rw [h] at hP
    exact not_onCurve_zero hP
  rw [← addOrderOf_eq hp, addOrderOf_dvd_iff_nsmul_eq_zero]

/-- Congruent scalars produce the same multiple of an on-curve point. -/
theorem nsmul_congr {P : Point Fp} (hP : P.OnCurve)
    {m n : ℕ} (h : m ≡ n [MOD PALLAS_SCALAR_CARD]) :
    m • P = n • P := by
  have hp_valid : P.Valid := .inl hP
  apply (ext_toSW_iff (valid_nsmul hp_valid m) (valid_nsmul hp_valid n)).mpr
  rw [toSW_nsmul hp_valid m, toSW_nsmul hp_valid n]
  rw [nsmul_eq_nsmul_iff_modEq, addOrderOf_eq]
  exact h
  intro hzero
  rw [← toSW_zero, ← ext_toSW_iff] at hzero
  rw [hzero] at hP
  exact not_onCurve_zero hP

theorem nsmul_ne_zero {P : Point Fp} (hP : P.OnCurve)
    {n : ℕ} (hn : 0 < n) (hlt : n < PALLAS_SCALAR_CARD) : n • P ≠ 0 := by
  rw [Ne, nsmul_eq_zero_iff hP]
  intro hdvd
  have := Nat.le_of_dvd hn hdvd
  omega

theorem nsmul_onCurve {P : Point Fp} (hP : P.OnCurve)
    {n : ℕ} (hn : 0 < n) (hlt : n < PALLAS_SCALAR_CARD) :
    (n • P).OnCurve := by
  apply onCurve_of_valid_of_ne_zero (valid_nsmul (.inl hP) n)
  apply nsmul_ne_zero hP hn hlt

/-- Nonzero representable points sharing an `x`-coordinate are equal or opposite. -/
theorem eq_or_eq_neg_of_x_eq {P Q : Point Fp} (hP : P.OnCurve) (hQ : Q.OnCurve) :
    P.x = Q.x → P = Q ∨ P = -Q := by
  intro h
  simp only [OnCurve] at *
  rw [h, ←hQ] at hP; clear hQ
  have hy : P.y = Q.y ∨ P.y = -Q.y := by grind
  rw [mk.injEq, mk.injEq, neg_x, neg_y]
  grind

/--
The collision-freedom fact behind incomplete additions on a variable base: distinct
small positive multiples of a non-identity point have distinct `x`-coordinates, since
equal `x` would force equal-or-opposite points and hence a relation `t ∓ s ≡ 0` modulo
the (large) group order.
-/
theorem nsmul_x_ne {P : Point Fp} (hP : P.OnCurve)
    {s t : ℕ} (hs : 0 < s) (hst : s < t) (hsum : s + t < PALLAS_SCALAR_CARD) :
    (t • P).x ≠ (s • P).x := by
  have hp_valid : P.Valid := .inl hP
  have ht_onCurve : (t • P).OnCurve := nsmul_onCurve hP (by omega) (by omega)
  have ht_valid : (t • P).Valid := .inl ht_onCurve
  have hs_onCurve : (s • P).OnCurve := nsmul_onCurve hP hs (by omega)
  have hs_valid : (s • P).Valid := .inl hs_onCurve
  intro hx
  rcases eq_or_eq_neg_of_x_eq ht_onCurve hs_onCurve hx with heq | hneg
  · rw [ext_toSW_iff ht_valid hs_valid, toSW_nsmul hp_valid, toSW_nsmul hp_valid] at heq
    rw [nsmul_eq_nsmul_iff_modEq, addOrderOf_eq, Nat.ModEq,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
    omega
    intro hzero
    rw [← toSW_zero, ← ext_toSW_iff] at hzero
    rw [hzero] at hP
    exact not_onCurve_zero hP
  · rw [ext_toSW_iff ht_valid (valid_neg hs_valid), toSW_nsmul hp_valid, toSW_neg hs_valid, toSW_nsmul hp_valid] at hneg
    have hzero : (t + s) • (P.toSW hp_valid) = 0 := by
      rw [add_nsmul, hneg, neg_add_cancel]
    rw [← toSW_nsmul, ← toSW_zero, ← ext_toSW_iff] at hzero
    rw [nsmul_eq_zero_iff hP] at hzero
    have := Nat.le_of_dvd (by omega) hzero
    omega

end Point

end Orchard
