import Clean.Halo2
import Clean.Orchard.Specs.Pallas
import Clean.Orchard.Ecc.Add
import Clean.Ironwood.Ecc.Basic

namespace Halo2.Ironwood.Ecc
/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/add.rs`
- `complete addition`

Port of the complete point-addition gadget. Mirrors `AddIncomplete.lean` but for the
*complete* group law, valid for ALL Pallas points (identity included).

The Rust chip's `EccConfig` hands `Config::configure` four advice columns `x_p, y_p,
x_qr, y_qr` (P coords at the current row; Q at the current row and R at the next row of
`x_qr, y_qr`) plus five auxiliary advice columns `lambda, alpha, beta, gamma, delta`
holding the `inv0` hints. `configure` enables equality on the four point columns and
allocates one simple selector `q_add`. The gate (12 polynomials) is queried at
`Rotation::cur()` for everything except `x_r, y_r` which are `Rotation::next()` on
`x_qr, y_qr`. `assign_region` copies P/Q into the current row, then witnesses `α = inv0(x_q
− x_p)`, `β = inv0(x_p)`, `γ = inv0(x_q)`, `δ = inv0(y_q+y_p) if x_q=x_p else 0`, `λ`, and
the complete-addition result `R` into the next row.
-/

namespace Add

/-- The Rust `add::Config`: one simple selector, the four point columns, and the five
auxiliary hint columns. `x_qr`/`y_qr` carry Q at the current row and R at the next row. -/
structure Config where
  qAdd : Selector
  lambda : Column .advice
  xP : Column .advice
  yP : Column .advice
  xQR : Column .advice
  yQR : Column .advice
  alpha : Column .advice
  beta : Column .advice
  gamma : Column .advice
  delta : Column .advice

/-- The twelve "complete addition" gate polynomials, as a pure function of the columns —
ported verbatim from the Rust `create_gate` closure. `x_p, y_p, x_q, y_q, λ, α, β, γ, δ`
are read at `Rotation::cur()` (0); `x_r, y_r` are read on `x_qr, y_qr` at
`Rotation::next()` (1).

- poly1:  `(x_q − x_p)·((x_q − x_p)·λ − (y_q − y_p))`
- poly2:  `(1 − (x_q − x_p)·α)·(2y_p·λ − 3x_p²)`
- poly3a: `x_p·x_q·(x_q − x_p)·(λ² − x_p − x_q − x_r)`
- poly3b: `x_p·x_q·(x_q − x_p)·(λ·(x_p − x_r) − y_p − y_r)`
- poly3c: `x_p·x_q·(y_q + y_p)·(λ² − x_p − x_q − x_r)`
- poly3d: `x_p·x_q·(y_q + y_p)·(λ·(x_p − x_r) − y_p − y_r)`
- poly4a: `(1 − x_p·β)·(x_r − x_q)`
- poly4b: `(1 − x_p·β)·(y_r − y_q)`
- poly5a: `(1 − x_q·γ)·(x_r − x_p)`
- poly5b: `(1 − x_q·γ)·(y_r − y_p)`
- poly6a: `(1 − (x_q − x_p)·α − (y_q + y_p)·δ)·x_r`
- poly6b: `(1 − (x_q − x_p)·α − (y_q + y_p)·δ)·y_r` -/
def gate (qAdd : Selector) (lambda xP yP xQR yQR alpha beta gamma delta : Column .advice) :
    Gate Fp where
  name := "complete addition"
  selector := qAdd
  constraints :=
    let x_p : Expression Fp Query := queryAdvice xP 0
    let y_p : Expression Fp Query := queryAdvice yP 0
    let x_q : Expression Fp Query := queryAdvice xQR 0
    let y_q : Expression Fp Query := queryAdvice yQR 0
    let x_r : Expression Fp Query := queryAdvice xQR 1
    let y_r : Expression Fp Query := queryAdvice yQR 1
    let lambda : Expression Fp Query := queryAdvice lambda 0
    let alpha : Expression Fp Query := queryAdvice alpha 0
    let beta : Expression Fp Query := queryAdvice beta 0
    let gamma : Expression Fp Query := queryAdvice gamma 0
    let delta : Expression Fp Query := queryAdvice delta 0
    let x_q_minus_x_p := x_q - x_p
    let x_p_minus_x_r := x_p - x_r
    let y_q_plus_y_p := y_q + y_p
    let if_alpha := x_q_minus_x_p * alpha
    let if_beta := x_p * beta
    let if_gamma := x_q * gamma
    let if_delta := y_q_plus_y_p * delta
    let poly1 := x_q_minus_x_p * (x_q_minus_x_p * lambda - (y_q - y_p))
    let poly2 := (1 - if_alpha) * (2 * y_p * lambda - 3 * x_p * x_p)
    let nonexceptional_x_r := lambda * lambda - x_p - x_q - x_r
    let nonexceptional_y_r := lambda * x_p_minus_x_r - y_p - y_r
    let poly3a := x_p * x_q * x_q_minus_x_p * nonexceptional_x_r
    let poly3b := x_p * x_q * x_q_minus_x_p * nonexceptional_y_r
    let poly3c := x_p * x_q * y_q_plus_y_p * nonexceptional_x_r
    let poly3d := x_p * x_q * y_q_plus_y_p * nonexceptional_y_r
    let poly4a := (1 - if_beta) * (x_r - x_q)
    let poly4b := (1 - if_beta) * (y_r - y_q)
    let poly5a := (1 - if_gamma) * (x_r - x_p)
    let poly5b := (1 - if_gamma) * (y_r - y_p)
    let poly6a := (1 - if_alpha - if_delta) * x_r
    let poly6b := (1 - if_alpha - if_delta) * y_r
    Constraints.withSelector qAdd
      [ ("1", poly1), ("2", poly2),
        ("3a", poly3a), ("3b", poly3b), ("3c", poly3c), ("3d", poly3d),
        ("4a", poly4a), ("4b", poly4b),
        ("5a", poly5a), ("5b", poly5b),
        ("6a", poly6a), ("6b", poly6b) ]

/-- Rust `Config::configure`: enable equality on the four point advice columns, allocate
the simple selector, register the gate. The five auxiliary hint columns are *not*
equality-enabled (they carry only prover hints). -/
def configure (xP yP xQR yQR lambda alpha beta gamma delta : Column .advice) :
    Configure Fp Config := do
  enableEquality xP.toAny
  enableEquality yP.toAny
  enableEquality xQR.toAny
  enableEquality yQR.toAny
  let qAdd ← selector
  createGate (gate qAdd lambda xP yP xQR yQR alpha beta gamma delta)
  return { qAdd, lambda, xP, yP, xQR, yQR, alpha, beta, gamma, delta }

/-!
## Algebraic core lemmas

The value-level mathematics, ported from the phase-one `Orchard.Ecc.Add`. Everything is
stated over concrete field coordinates with the gate polynomials written out literally, so
the lemmas do not depend on the gate's `Query`/`Expression` machinery. The complete group
law is `Orchard.Point.add` and validity is `Orchard.Point.Valid` (on-curve, or the `(0,0)`
identity sentinel), reused from the Orchard Pallas specs.
-/

open Orchard (Point)
open Orchard (pallasA pallasB two_ne_zero add_self_ne_zero)
open CompElliptic.CurveForms

/-- The intermediate "gate spec": the case-split characterization of the twelve
complete-addition polynomials. Ported verbatim from `Orchard.Ecc.Add.Gate.Spec`, phrased
over plain coordinates. Each conjunct is the "non-exceptional branch" implication guarded
by the corresponding `inv0`-flag being nonzero. -/
def Spec (px py qx qy rx ry lambda alpha beta gamma delta : Fp) : Prop :=
  (qx - px ≠ 0 → (qx - px) * lambda = qy - py) ∧
    ((qx - px) * alpha ≠ 1 → 2 * py * lambda = 3 * px * px) ∧
    (px * qx * (qx - px) ≠ 0 →
      rx = lambda * lambda - px - qx ∧ ry = lambda * (px - rx) - py) ∧
    (px * qx * (qy + py) ≠ 0 →
      rx = lambda * lambda - px - qx ∧ ry = lambda * (px - rx) - py) ∧
    (px * beta ≠ 1 → rx = qx ∧ ry = qy) ∧
    (qx * gamma ≠ 1 → rx = px ∧ ry = py) ∧
    ((qx - px) * alpha + (qy + py) * delta ≠ 1 → rx = 0 ∧ ry = 0)

/-- The `λ` slope witness, over plain coordinates (Rust `assign_region`'s `lambda`
closure). Ported from `Orchard.Ecc.Add.lambdaValue`: the tangent slope when `x_q = x_p`
(and `y_p ≠ 0`), the chord slope otherwise (with `inv0` semantics `0⁻¹ = 0` making the
degenerate cases `0`). -/
def lambdaValueRaw (px py qx qy : Fp) : Fp :=
  if qx = px then
    if py ≠ 0 then (3 * px * px) * (2 * py)⁻¹ else 0
  else
    (qy - py) * (qx - px)⁻¹

/-- Soundness half of the gate: the twelve polynomials vanishing implies the `Spec`
case-split. Ported from the soundness half of `Orchard.Ecc.Add.Gate.circuit`. -/
theorem spec_of_polysZero {px py qx qy rx ry lambda alpha beta gamma delta : Fp}
    (h1 : (qx - px) * ((qx - px) * lambda - (qy - py)) = 0)
    (h2 : (1 - (qx - px) * alpha) * (2 * py * lambda - 3 * px * px) = 0)
    (h3a : px * qx * (qx - px) * (lambda * lambda - px - qx - rx) = 0)
    (h3b : px * qx * (qx - px) * (lambda * (px - rx) - py - ry) = 0)
    (h3c : px * qx * (qy + py) * (lambda * lambda - px - qx - rx) = 0)
    (h3d : px * qx * (qy + py) * (lambda * (px - rx) - py - ry) = 0)
    (h4a : (1 - px * beta) * (rx - qx) = 0)
    (h4b : (1 - px * beta) * (ry - qy) = 0)
    (h5a : (1 - qx * gamma) * (rx - px) = 0)
    (h5b : (1 - qx * gamma) * (ry - py) = 0)
    (h6a : (1 - (qx - px) * alpha - (qy + py) * delta) * rx = 0)
    (h6b : (1 - (qx - px) * alpha - (qy + py) * delta) * ry = 0) :
    Spec px py qx qy rx ry lambda alpha beta gamma delta := by
  simp only [Spec]
  and_intros
  · grind
  · grind
  · intros; and_intros <;> grind
  · intros; and_intros <;> grind
  · intros; and_intros <;> grind
  · intros; and_intros <;> grind
  · intros; and_intros <;> grind

/-- Completeness half of the gate: `Spec` implies each of the twelve polynomials vanishes.
Ported from the completeness half of `Orchard.Ecc.Add.Gate.circuit`. Returns the twelve
equations as a conjunction (in the gate's constraint order). -/
theorem polysZero_of_spec {px py qx qy rx ry lambda alpha beta gamma delta : Fp}
    (h : Spec px py qx qy rx ry lambda alpha beta gamma delta) :
    (qx - px) * ((qx - px) * lambda - (qy - py)) = 0 ∧
    (1 - (qx - px) * alpha) * (2 * py * lambda - 3 * px * px) = 0 ∧
    px * qx * (qx - px) * (lambda * lambda - px - qx - rx) = 0 ∧
    px * qx * (qx - px) * (lambda * (px - rx) - py - ry) = 0 ∧
    px * qx * (qy + py) * (lambda * lambda - px - qx - rx) = 0 ∧
    px * qx * (qy + py) * (lambda * (px - rx) - py - ry) = 0 ∧
    (1 - px * beta) * (rx - qx) = 0 ∧
    (1 - px * beta) * (ry - qy) = 0 ∧
    (1 - qx * gamma) * (rx - px) = 0 ∧
    (1 - qx * gamma) * (ry - py) = 0 ∧
    (1 - (qx - px) * alpha - (qy + py) * delta) * rx = 0 ∧
    (1 - (qx - px) * alpha - (qy + py) * delta) * ry = 0 := by
  obtain ⟨h1, h2, h3, h3', h4, h5, h6⟩ := h
  and_intros
  · by_cases hz : qx - px = 0 <;> grind
  · by_cases hz : (qx - px) * alpha = 1 <;> grind
  · by_cases hz : px * qx * (qx - px) = 0 <;> grind
  · by_cases hz : px * qx * (qx - px) = 0 <;> grind
  · by_cases hz : px * qx * (qy + py) = 0 <;> grind
  · by_cases hz : px * qx * (qy + py) = 0 <;> grind
  · by_cases hz : px * beta = 1 <;> grind
  · by_cases hz : px * beta = 1 <;> grind
  · by_cases hz : qx * gamma = 1 <;> grind
  · by_cases hz : qx * gamma = 1 <;> grind
  · by_cases hz : (qx - px) * alpha + (qy + py) * delta = 1 <;> grind
  · by_cases hz : (qx - px) * alpha + (qy + py) * delta = 1 <;> grind

/-- Bridge: our plain-coordinate `Spec` is exactly the donor's `Gate.Spec` on the
corresponding `Gate.Input`. Both are the same seven-way case split; only the field
packaging differs. -/
theorem spec_toGateInput {px py qx qy rx ry lambda alpha beta gamma delta : Fp} :
    Spec px py qx qy rx ry lambda alpha beta gamma delta ↔
    Orchard.Ecc.Add.Gate.Spec
      { x_p := px, y_p := py, x_qr := { curr := qx, next := rx },
        y_qr := { curr := qy, next := ry }, lambda, alpha, beta, gamma, delta } := by
  simp only [Spec, Orchard.Ecc.Add.Gate.Spec,
    Orchard.Ecc.Add.Gate.Input.p, Orchard.Ecc.Add.Gate.Input.q, Orchard.Ecc.Add.Gate.Input.r,
    Point.mk.injEq]

/-- Soundness core: given valid P, Q and the gate `Spec` at coordinates
`(px,py) (qx,qy) (rx,ry)`, the result `R = (rx, ry)` is the complete sum `P + Q`.
Delegates to the phase-one `Orchard.Ecc.Add.add_of_spec`. -/
theorem add_eq_add_of_spec {px py qx qy rx ry lambda alpha beta gamma delta : Fp}
    (hp : ({ x := px, y := py } : Point Fp).Valid)
    (hq : ({ x := qx, y := qy } : Point Fp).Valid)
    (hrow : Spec px py qx qy rx ry lambda alpha beta gamma delta) :
    ({ x := rx, y := ry } : Point Fp) = { x := px, y := py } + { x := qx, y := qy } :=
  Orchard.Ecc.Add.add_of_spec (row :=
    { x_p := px, y_p := py, x_qr := { curr := qx, next := rx },
      y_qr := { curr := qy, next := ry }, lambda, alpha, beta, gamma, delta })
    hp hq (spec_toGateInput.mp hrow)

/-!
## Witness values (the honest prover's hints)

The five auxiliary hints and the output R, over plain coordinates. Together with
`rowValue_spec` (delegated to the donor) they give the completeness direction: the honest
prover's witnesses satisfy the gate `Spec`, hence the twelve polynomials
(`polysZero_of_spec`).
-/

/-- The complete `Spec` holds for the honest prover's witness values: `λ` = the slope
hint, `α,β,γ` = the `inv0` hints, `δ` the conditional hint, and R the complete sum.
Delegates to `Orchard.Ecc.Add.rowValue_spec`. -/
theorem spec_of_valid {px py qx qy : Fp}
    (hp : ({ x := px, y := py } : Point Fp).Valid)
    (hq : ({ x := qx, y := qy } : Point Fp).Valid) :
    Spec px py qx qy
      (({ x := px, y := py } : Point Fp) + { x := qx, y := qy }).x
      (({ x := px, y := py } : Point Fp) + { x := qx, y := qy }).y
      (lambdaValueRaw px py qx qy)
      ((qx - px)⁻¹) (px⁻¹) (qx⁻¹)
      (if qx = px then (qy + py)⁻¹ else 0) := by
  have hrow := Orchard.Ecc.Add.rowValue_spec
    (input := { p := { x := px, y := py }, q := { x := qx, y := qy } }) hp hq
  rw [spec_toGateInput]
  convert hrow using 2

/-!
## Witness-program evaluation lemmas

The evaluated `if`-trees of the R/λ/δ witness programs, in closed form. Ported from the
private `ite_rX`/`ite_rY`/`ite_lambdaValue`/`ite_deltaValue` of `Orchard.Ecc.Add`. The
`Decidable` instances are variables: `BExpr.feq`'s evaluation decides field equality
through its own instance, not necessarily the canonical one, so an instance-generic
statement lets `simp` match either spelling (after the compound `∧` conditions arrive
propositionally via `Bool.and_eq_true`/`decide_eq_true_eq`, both in `circuit_norm`).
-/

theorem ite_lambdaProgram_eq (px py qx qy : Fp)
    {d1 : Decidable (qx = px)} {d2 : Decidable (py = 0)} :
    (@ite _ (qx = px) d1
      (@ite _ (py = 0) d2 (0 : Fp) (3 * px * px * (2 * py)⁻¹))
      ((qy - py) * (qx - px)⁻¹))
    = lambdaValueRaw px py qx qy := by
  unfold lambdaValueRaw
  by_cases h : qx = px <;> by_cases h' : py = 0 <;> simp_all

theorem ite_deltaProgram_eq (px py qx qy : Fp) {d : Decidable (qx = px)} :
    (@ite _ (qx = px) d ((qy + py)⁻¹) 0)
    = (if qx = px then (qy + py)⁻¹ else 0 : Fp) := by
  by_cases h : qx = px <;> simp_all

theorem ite_rXProgram_eq (px py qx qy : Fp)
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
  split_ifs <;> ring

theorem ite_rYProgram_eq (px py qx qy : Fp)
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
  split_ifs <;> ring

/-!
## The gadget

Input is the pair of input points (P, Q), both `AssignedCell`-backed (copied in). Unlike
incomplete addition, complete addition works for **all** valid points (identity included),
so the assumptions are just `P, Q` valid, with no `x_p ≠ x_q` restriction.
-/

/-- The pair of input points P and Q. -/
structure Inputs (F : Type) where
  p : Point F
  q : Point F
deriving ProvableStruct

/-!
The three witness programs spell the Rust `assign_region` closures over Halo2-Clean's
`FExpr Fp = Witgen.FExprOver Fp (AssignedCell Fp)`. The field arithmetic, numeric
literals and the Boolean conditions (`=?`, `&&&`) all come from the atom-generic
authoring sugar in `Clean/Circuit/WitnessIRSugar.lean`. -/

/-- The witness-IR value of the `λ` slope, spelled exactly as the Rust `lambda` closure
(`inv0` = `.inv`; the `if x_q = x_p` split is the `.ite` on `x_q = x_p`). -/
def lambdaProgram (px py qx qy : FExpr Fp) : FExpr Fp :=
  .ite (qx =? px)
    (.ite (py =? 0) 0 ((3 * px * px) * (2 * py)⁻¹))
    ((qy - py) * (qx - px)⁻¹)

/-- The witness-IR value of R.x, spelled as the Rust `r` closure: `0 + Q`, `P + 0`,
`P + (−P) ↦ (0,0)`, else the non-exceptional `λ`-line. -/
def rXProgram (px py qx qy : FExpr Fp) : FExpr Fp :=
  .ite ((px =? 0) &&& (py =? 0)) qx <|
  .ite ((qx =? 0) &&& (qy =? 0)) px <|
  .ite (px =? qx)
    (.ite (py + qy =? 0) 0
      ((3 * px * px) * (2 * py)⁻¹ * ((3 * px * px) * (2 * py)⁻¹) - px - qx))
    ((qy - py) * (qx - px)⁻¹ * ((qy - py) * (qx - px)⁻¹) - px - qx)

/-- The witness-IR value of R.y, spelled as the Rust `r` closure. -/
def rYProgram (px py qx qy : FExpr Fp) : FExpr Fp :=
  .ite ((px =? 0) &&& (py =? 0)) qy <|
  .ite ((qx =? 0) &&& (qy =? 0)) py <|
  .ite (px =? qx)
    (.ite (py + qy =? 0) 0
      ((3 * px * px) * (2 * py)⁻¹ *
        (px - ((3 * px * px) * (2 * py)⁻¹ * ((3 * px * px) * (2 * py)⁻¹) - px - qx)) - py))
    ((qy - py) * (qx - px)⁻¹ *
      (px - ((qy - py) * (qx - px)⁻¹ * ((qy - py) * (qx - px)⁻¹) - px - qx)) - py)

def add : FormalRegionCircuit Fp
    (Column .advice × Column .advice × Column .advice × Column .advice ×
      Column .advice × Column .advice × Column .advice × Column .advice × Column .advice)
    Config Inputs Point where
  configure := fun (xP, yP, xQR, yQR, lambda, alpha, beta, gamma, delta) =>
    configure xP yP xQR yQR lambda alpha beta gamma delta

  synthesize config offset (input : Inputs (AssignedCell Fp)) := do
    -- enable `q_add` selector at `offset`
    (gate config.qAdd config.lambda config.xP config.yP config.xQR config.yQR
      config.alpha config.beta config.gamma config.delta).enable offset
    -- copy P into `(x_p, y_p)` at `offset`
    let _xP ← copyAdvice input.p.x config.xP offset
    let _yP ← copyAdvice input.p.y config.yP offset
    -- copy Q into `(x_qr, y_qr)` at `offset`
    let _xQ ← copyAdvice input.q.x config.xQR offset
    let _yQ ← copyAdvice input.q.y config.yQR offset
    -- the copied input coordinates as witness-IR reads
    let px : FExpr Fp := .expr input.p.x
    let py : FExpr Fp := .expr input.p.y
    let qx : FExpr Fp := .expr input.q.x
    let qy : FExpr Fp := .expr input.q.y
    -- witness the auxiliary `inv0` hints at `offset` (Rust `assign_advice` closures)
    let _alpha ← assignAdvice config.alpha offset (.ofFExpr ((qx - px)⁻¹))
    let _beta ← assignAdvice config.beta offset (.ofFExpr (px⁻¹))
    let _gamma ← assignAdvice config.gamma offset (.ofFExpr (qx⁻¹))
    let _delta ← assignAdvice config.delta offset
      (.ofFExpr (.ite (qx =? px) ((qy + py)⁻¹) 0))
    let _lambda ← assignAdvice config.lambda offset (.ofFExpr (lambdaProgram px py qx qy))
    -- witness the result R at `offset + 1` on `(x_qr, y_qr)`
    let xR ← assignAdvice config.xQR (offset + 1) (.ofFExpr (rXProgram px py qx qy))
    let yR ← assignAdvice config.yQR (offset + 1) (.ofFExpr (rYProgram px py qx qy))
    return ⟨ xR, yR ⟩

  -- P, Q are valid Pallas points (complete addition has no exceptional cases).
  Assumptions input := input.p.Valid ∧ input.q.Valid
  Spec input output _ := output.Valid ∧ output = input.p + input.q

  soundness := by
    intro config offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output h_assumptions hc
    -- reduce circuit structure (gate polys + copy equalities), running the eval simprocs
    simp only [circuit_norm, gate] at hc h_output
    -- destructure input/output; split the input/output eval equations into coordinates
    provable_type_simp
    simp only [h_input, h_output] at hc ⊢
    clear h_input h_output
    -- ══ user-facing half: pure field values + curve math ══
    obtain ⟨⟨h1, h2, h3a, h3b, h3c, h3d, h4a, h4b, h5a, h5b, h6a, h6b⟩,
      hcpx, hcpy, hcqx, hcqy⟩ := hc
    -- the copy equations rewrite the gate's P/Q cells to the input coordinates
    simp only [hcpx, hcpy, hcqx, hcqy] at h1 h2 h3a h3b h3c h3d h4a h4b h5a h5b h6a h6b
    obtain ⟨hpValid, hqValid⟩ := h_assumptions
    -- the five witness cells (λ,α,β,γ,δ) have no copy equation, so they stay as
    -- `env.env.advice config.λ …` terms — but they are only ever passed *positionally* to
    -- the coordinate-generic `spec_of_polysZero`, never reasoned about, so no framework
    -- object is manipulated in the user half.
    have hspec := spec_of_polysZero h1 h2 h3a h3b h3c h3d h4a h4b h5a h5b h6a h6b
    have hsum := add_eq_add_of_spec hpValid hqValid hspec
    rw [hsum]
    exact ⟨Orchard.Point.valid_add hpValid hqValid, rfl⟩
  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit hA hlast
    simp only [circuit_norm, gate, lambdaProgram, rXProgram, rYProgram] at hwit hA h_input h_output ⊢
    provable_type_simp
    -- land the copied input-cell reads on the input coordinates, then the gate/witness
    -- cells on their witness programs (over the input coordinates)
    simp only [circuit_norm, h_input] at hwit
    simp only [circuit_norm, h_input, hwit] at ⊢ hA
    clear h_input h_output hwit
    -- ══ user-facing half ══
    obtain ⟨hpValid, hqValid⟩ := hA
    -- the witness R cells equal the complete sum; λ/δ equal their closed-form values
    rw [ite_rXProgram_eq input_p_x input_p_y input_q_x input_q_y,
        ite_rYProgram_eq input_p_x input_p_y input_q_x input_q_y,
        ite_lambdaProgram_eq input_p_x input_p_y input_q_x input_q_y,
        ite_deltaProgram_eq input_p_x input_p_y input_q_x input_q_y]
    exact polysZero_of_spec (spec_of_valid hpValid hqValid)

end Add

end Halo2.Ironwood.Ecc
