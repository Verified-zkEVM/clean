import Clean.Halo2
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.AddTheorems
import Clean.Ironwood.Ecc.Basic

namespace Zcash.Circuits.Ecc

open Halo2
/-!
Complete point addition `P + Q = R`, valid for ALL Pallas points including the identity. The gate's
twelve polynomials implement the complete group law, selecting the branch (`P = Q`, `P = −Q`, either
point at infinity, or generic) via the `inv0` hints `α, β, γ, δ` and the slope `λ`. `x_qr`/`y_qr`
carry `Q` at the current row and `R` at the next row.

Reference: `halo2_gadgets/src/ecc/chip/add.rs`.
-/

namespace Add

structure Config where
  qAdd : Selector
  -- lambda
  lambda : Column .advice
  -- x-coordinate of P in P + Q = R
  xP : Column .advice
  -- y-coordinate of P in P + Q = R
  yP : Column .advice
  -- x-coordinate of Q or R in P + Q = R
  xQR : Column .advice
  -- y-coordinate of Q or R in P + Q = R
  yQR : Column .advice
  -- α = inv0(x_q − x_p)
  alpha : Column .advice
  -- β = inv0(x_p)
  beta : Column .advice
  -- γ = inv0(x_q)
  gamma : Column .advice
  -- δ = inv0(y_p + y_q) if x_q = x_p, 0 otherwise
  delta : Column .advice

/-- The twelve complete-addition gate polynomials, a pure function of the columns.
`x_p, y_p, x_q, y_q, λ, α, β, γ, δ` are read at the current row; `x_r, y_r` at the next row. -/
def gate (qAdd : Selector) (lambda xP yP xQR yQR alpha beta gamma delta : Column .advice) :
    Gate Fp :=
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
  Gate.withSelector "complete addition" qAdd
    [x_p, y_p, x_q, y_q, x_r, y_r, lambda, alpha, beta, gamma, delta] <|
    let x_q_minus_x_p := x_q - x_p
    let x_p_minus_x_r := x_p - x_r
    let y_q_plus_y_p := y_q + y_p
    let if_alpha := x_q_minus_x_p * alpha
    let if_beta := x_p * beta
    let if_gamma := x_q * gamma
    let if_delta := y_q_plus_y_p * delta
    let poly1 := x_q_minus_x_p * (x_q_minus_x_p * lambda - (y_q - y_p))
    -- `3 * (x_p * x_p)`: matches Rust `three * x_p.square()` = `Product(3, Product(x_p, x_p))`
    -- (right-associated). Writing `3 * x_p * x_p` would left-associate and diverge from the
    -- pinned VK AST; the field value is identical, so soundness proofs are unaffected.
    let poly2 := (1 - if_alpha) * (2 * y_p * lambda - 3 * (x_p * x_p))
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
    [ ("1", poly1), ("2", poly2),
      ("3a", poly3a), ("3b", poly3b), ("3c", poly3c), ("3d", poly3d),
      ("4a", poly4a), ("4b", poly4b),
      ("5a", poly5a), ("5b", poly5b),
      ("6a", poly6a), ("6b", poly6b) ]

@[circuit_norm, configure_selector_norm, keygen_norm]
theorem gate_selector
    (qAdd : Selector)
    (lambda xP yP xQR yQR alpha beta gamma delta : Column .advice) :
    (gate qAdd lambda xP yP xQR yQR alpha beta gamma delta).selector = qAdd := rfl

/-!
## Algebraic core lemmas

The value-level mathematics. Everything is stated over concrete field coordinates with the gate
polynomials written out literally, so the lemmas do not depend on the gate's `Query`/`Expression`
machinery. The complete group law is `Point.add` and validity is
`Point.Valid` (on-curve, or the `(0,0)` identity sentinel).
-/

open CompElliptic.CurveForms

/-- The gate spec: the case-split characterization of the twelve complete-addition polynomials over
plain coordinates. Each conjunct is the non-exceptional-branch implication guarded by the
corresponding `inv0`-flag being nonzero. -/
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
closure). Ported from `Ecc.Add.lambdaValue`: the tangent slope when `x_q = x_p`
(and `y_p ≠ 0`), the chord slope otherwise (with `inv0` semantics `0⁻¹ = 0` making the
degenerate cases `0`). -/
def lambdaValueRaw (px py qx qy : Fp) : Fp :=
  if qx = px then
    if py ≠ 0 then (3 * px * px) * (2 * py)⁻¹ else 0
  else
    (qy - py) * (qx - px)⁻¹

/-- Soundness half of the gate: the twelve polynomials vanishing implies the `Spec`
case-split. Ported from the soundness half of `Ecc.Add.Gate.circuit`. -/
theorem spec_of_polysZero {px py qx qy rx ry lambda alpha beta gamma delta : Fp}
    (h1 : (qx - px) * ((qx - px) * lambda - (qy - py)) = 0)
    (h2 : (1 - (qx - px) * alpha) * (2 * py * lambda - 3 * (px * px)) = 0)
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
Ported from the completeness half of `Ecc.Add.Gate.circuit`. Returns the twelve
equations as a conjunction (in the gate's constraint order). -/
theorem polysZero_of_spec {px py qx qy rx ry lambda alpha beta gamma delta : Fp}
    (h : Spec px py qx qy rx ry lambda alpha beta gamma delta) :
    (qx - px) * ((qx - px) * lambda - (qy - py)) = 0 ∧
    (1 - (qx - px) * alpha) * (2 * py * lambda - 3 * (px * px)) = 0 ∧
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

/-- Bridge: our plain-coordinate `Spec` is exactly `Gate.Spec` on the corresponding
`Gate.Input`. Both are the same seven-way case split; only the field packaging differs. -/
theorem spec_toGateInput {px py qx qy rx ry lambda alpha beta gamma delta : Fp} :
    Spec px py qx qy rx ry lambda alpha beta gamma delta ↔
    Ecc.Add.Gate.Spec
      { x_p := px, y_p := py, x_qr := { curr := qx, next := rx },
        y_qr := { curr := qy, next := ry }, lambda, alpha, beta, gamma, delta } := by
  simp only [Spec, Ecc.Add.Gate.Spec,
    Ecc.Add.Gate.Input.p, Ecc.Add.Gate.Input.q, Ecc.Add.Gate.Input.r,
    Point.mk.injEq]

/-- Soundness core: given valid P, Q and the gate `Spec` at coordinates
`(px,py) (qx,qy) (rx,ry)`, the result `R = (rx, ry)` is the complete sum `P + Q`.
Delegates to `Ecc.Add.add_of_spec`. -/
theorem add_eq_add_of_spec {px py qx qy rx ry lambda alpha beta gamma delta : Fp}
    (hp : ({ x := px, y := py } : Point Fp).Valid)
    (hq : ({ x := qx, y := qy } : Point Fp).Valid)
    (hrow : Spec px py qx qy rx ry lambda alpha beta gamma delta) :
    ({ x := rx, y := ry } : Point Fp) = { x := px, y := py } + { x := qx, y := qy } :=
  Ecc.Add.add_of_spec (row :=
    { x_p := px, y_p := py, x_qr := { curr := qx, next := rx },
      y_qr := { curr := qy, next := ry }, lambda, alpha, beta, gamma, delta })
    hp hq (spec_toGateInput.mp hrow)

/-!
## Witness values (the honest prover's hints)

The five auxiliary hints and the output R, over plain coordinates. Together with
`rowValue_spec` they give the completeness direction: the honest prover's witnesses satisfy
the gate `Spec`, hence the twelve polynomials (`polysZero_of_spec`).
-/

/-- The complete `Spec` holds for the honest prover's witness values: `λ` = the slope
hint, `α,β,γ` = the `inv0` hints, `δ` the conditional hint, and R the complete sum.
Delegates to `Ecc.Add.rowValue_spec`. -/
theorem spec_of_valid {px py qx qy : Fp}
    (hp : ({ x := px, y := py } : Point Fp).Valid)
    (hq : ({ x := qx, y := qy } : Point Fp).Valid) :
    Spec px py qx qy
      (({ x := px, y := py } : Point Fp) + { x := qx, y := qy }).x
      (({ x := px, y := py } : Point Fp) + { x := qx, y := qy }).y
      (lambdaValueRaw px py qx qy)
      ((qx - px)⁻¹) (px⁻¹) (qx⁻¹)
      (if qx = px then (qy + py)⁻¹ else 0) := by
  have hrow := Ecc.Add.rowValue_spec
    (input := { p := { x := px, y := py }, q := { x := qx, y := qy } }) hp hq
  rw [spec_toGateInput]
  convert hrow using 2

/-!
## Witness-program evaluation lemmas

The evaluated `if`-trees of the R/λ/δ witness programs, in closed form. Ported from the
private `ite_rX`/`ite_rY`/`ite_lambdaValue`/`ite_deltaValue` of `Ecc.Add`. The
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

structure Inputs (F : Type) where
  -- The point P in P + Q = R.
  p : Point F
  -- The point Q in P + Q = R.
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

/-- The point-coordinate columns registered for equality by `add.configure`. -/
@[keygen_norm]
def permutationColumns (config : Config) : List AnyColumn :=
  [config.xP, config.yP, config.xQR, config.yQR]

def synthesisSummary (config : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector config.qAdd.index,
      .column .advice config.xP.index,
      .column .advice config.yP.index,
      .column .advice config.xQR.index,
      .column .advice config.yQR.index,
      .column .advice config.alpha.index,
      .column .advice config.beta.index,
      .column .advice config.gamma.index,
      .column .advice config.delta.index,
      .column .advice config.lambda.index,
      .column .advice config.xQR.index,
      .column .advice config.yQR.index]
    (offset + 2) 0

@[synthesis_summary_norm]
theorem synthesisSummary_constantSiteCount (config : Config) (offset : ℕ) :
    (synthesisSummary config offset).constantSiteCount = 0 := rfl

def add : FormalRegionCircuit Fp
    (Column .advice × Column .advice × Column .advice × Column .advice ×
      Column .advice × Column .advice × Column .advice × Column .advice × Column .advice)
    Config Inputs Point where
  /- Rust `Config::configure`: enable equality on the four point advice columns, allocate
  the simple selector, register the gate. The five auxiliary hint columns are *not*
  equality-enabled (they carry only prover hints). -/
  configure | (xP, yP, xQR, yQR, lambda, alpha, beta, gamma, delta) => do
    enableEquality xP
    enableEquality yP
    enableEquality xQR
    enableEquality yQR
    let qAdd ← selector
    createGate (gate qAdd lambda xP yP xQR yQR alpha beta gamma delta)
    return { qAdd, lambda, xP, yP, xQR, yQR, alpha, beta, gamma, delta }

  elaborated :=
    { keygenRequirements :=
        { inputCells _ _ input :=
            [input.p.x.cell, input.p.y.cell, input.q.x.cell, input.q.y.cell] }
      output config offset _ self :=
        { x := .of self (offset + 1) config.xQR,
          y := .of self (offset + 1) config.yQR }
      synthesisSummary config offset _ _ := synthesisSummary config offset
      output_eq := by
        intro _ _ _ _
        rfl
      synthesisSummary_eq := by
        intro _ _ _ _
        apply FloorPlanner.RegionSynthesisSummary.ext
        · simp only [synthesisSummary]
          rw [FloorPlanner.regionSynthesisSummary_columns_eq_unionColumns]
          simp only [circuit_norm, gate, List.flatMap_cons,
            List.flatMap_nil, FloorPlanner.regionOperationShapeColumns,
            List.append_nil, List.nil_append, List.singleton_append]
        · simp only [synthesisSummary, circuit_norm, gate]
          omega
        · simp only [synthesisSummary, circuit_norm, gate]
        · simp only [synthesisSummary, circuit_norm, gate, synthesis_summary_norm] }

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
    return ⟨xR, yR⟩

  -- P, Q are valid Pallas points (complete addition has no exceptional cases).
  Assumptions input := input.p.Valid ∧ input.q.Valid
  Spec input output _ := output.Valid ∧ output = input.p + input.q

  soundness := by
    circuit_proof_start2 [gate]
    -- land the copied P/Q cells on the input coordinates in the gate polynomials
    simp only [region_1, region_2, region_3, region_4] at region_0
    obtain ⟨h1, h2, h3a, h3b, h3c, h3d, h4a, h4b, h5a, h5b, h6a, h6b⟩ := region_0
    obtain ⟨hpValid, hqValid⟩ := assumptions
    -- the five witness cells (λ,α,β,γ,δ) have no copy equation, so they stay as
    -- `env.advice cfg.λ …` terms — but they are only ever passed *positionally* to
    -- the coordinate-generic `spec_of_polysZero`, never reasoned about.
    have hspec := spec_of_polysZero h1 h2 h3a h3b h3c h3d h4a h4b h5a h5b h6a h6b
    rw [add_eq_add_of_spec hpValid hqValid hspec]
    use Point.valid_add hpValid hqValid
  completeness := by
    circuit_proof_start2 [gate, lambdaProgram, rXProgram, rYProgram]
    obtain ⟨hpValid, hqValid⟩ := assumptions
    -- substitute the copied/witnessed cells, with the R/λ programs in closed form
    -- (one simp call: the closed-form ite lemmas must fire as the programs are exposed,
    -- before ite-congruence can rewrite inside their branches)
    simp only [and_true, region_0, region_1, region_2, region_3, region_4, region_5,
      region_6, region_7, region_8, region_9, region_10,
      ite_rXProgram_eq, ite_rYProgram_eq, ite_lambdaProgram_eq]
    exact polysZero_of_spec (spec_of_valid hpValid hqValid)

@[keygen_norm]
theorem Configured.permutationColumns_eq {config : Config}
    (configured : add.Configured config) :
    configured.permutationColumns = permutationColumns config := by
  rcases configured with ⟨configInput, counts, hconfig, outputEq⟩
  cases outputEq
  simp only [keygen_norm, FormalRegionCircuit.Configured.permutationColumns,
    FormalRegionCircuit.keygenRequirements, ElaboratedRegionCircuit.keygenRequirements,
    add, permutationColumns, List.singleton_append]

@[keygen_norm]
theorem Configured.inputPermutationColumns_eq {config : Config}
    (configured : add.Configured config) (input : Var Inputs Fp) :
    configured.inputPermutationColumns input =
      [input.p.x.cell.column, input.p.y.cell.column,
        input.q.x.cell.column, input.q.y.cell.column] := by
  rfl

@[keygen_norm]
theorem configure_output_permutationColumns
    (xP yP xQR yQR lambda alpha beta gamma delta : Column .advice)
    (counts : ConfigureCounts) :
    permutationColumns
        ((add.configure
          (xP, yP, xQR, yQR, lambda, alpha, beta, gamma, delta)).output counts) =
      [xP, yP, xQR, yQR] := by
  simp [add, permutationColumns]

/-- The layouter-level complete addition: `add` in its own region, named once here as
in the Rust chip (`ecc/chip.rs`: `assign_region(|| "complete point addition", …)`). -/
def addFormal :=
  add.toFormal "complete point addition"

@[synthesis_summary_norm]
theorem addFormal_synthesisSummary_eq
    (config : Config) (input : Var Inputs Fp) (region : RegionIndex) :
    addFormal.elaborated.synthesisSummary config input region =
      FloorPlanner.SynthesisSummary.ofRegion (synthesisSummary config 0) := rfl

/-- Complete addition requests no deferred constant allocations inside its region. -/
@[synthesis_summary_norm]
theorem add_synthesisSummary_eq
    (config : Config) (offset : ℕ) (input : Var Inputs Fp)
    (region : RegionIndex) :
    add.elaborated.synthesisSummary config offset input region =
      synthesisSummary config offset := rfl

/-- Complete addition requests no deferred constant allocations inside its region. -/
@[synthesis_summary_norm]
theorem add_synthesisSummary_constantSiteCount
    (config : Config) (offset : ℕ) (input : Var Inputs Fp)
    (region : RegionIndex) :
    (add.elaborated.synthesisSummary
      config offset input region).constantSiteCount = 0 := by
  rw [add_synthesisSummary_eq]
  simp only [synthesisSummary, circuit_norm]

/-- Complete addition requests no deferred constant allocations. -/
@[synthesis_summary_norm]
theorem addFormal_synthesisSummary_constantSiteCount
    (config : Config) (input : Var Inputs Fp) (region : RegionIndex) :
    (addFormal.elaborated.synthesisSummary
      config input region).constantSiteCount = 0 := by
  unfold addFormal
  rw [FormalRegionCircuit.toFormal_synthesisSummary_constantSiteCount]
  exact add_synthesisSummary_constantSiteCount config 0 input region

/-- The layouter-level complete addition has the same positional output as its single
region. -/
@[keygen_norm, keygen_output_norm]
theorem addFormal_output_cells (config : Config) (input : Var Inputs Fp)
    (self : RegionIndex) :
    addFormal.output config input self =
      { x := .of self 1 config.xQR,
        y := .of self 1 config.yQR } := by
  rfl

@[keygen_norm]
theorem addFormal_inputCells (config : Config)
    (configured : addFormal.Configured config) (input : Var Inputs Fp) :
    configured.inputCells input =
      [input.p.x.cell, input.p.y.cell, input.q.x.cell, input.q.y.cell] := by
  rfl

/-- The complete-addition region's positional output cells. -/
theorem add_output_cells (config : Config) (offset : ℕ) (input : Var Inputs Fp)
    (self : RegionIndex) :
    add.output config offset input self =
      { x := .of self (offset + 1) config.xQR,
        y := .of self (offset + 1) config.yQR } := rfl

@[keygen_norm]
theorem add_inputCells (config : Config) (hconfigured : add.Configured config)
    (input : Var Inputs Fp) :
    FormalRegionCircuit.Configured.inputCells hconfigured input =
      [input.p.x.cell, input.p.y.cell, input.q.x.cell, input.q.y.cell] := rfl

/-- Both coordinates returned by complete addition are assigned by its call body. -/
theorem add_output_cells_assigned (config : Config) (offset : ℕ)
    (input : Var Inputs Fp) (self : RegionIndex) (available : List Cell) :
    let output := add.output config offset input self
    output.x.cell ∈
        (((add.call config offset input).operations self).assignedCellsAfter self available) ∧
      output.y.cell ∈
        (((add.call config offset input).operations self).assignedCellsAfter self available) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [add_output_cells, AssignedCell.of_cell,
    RegionOperations.mem_assignedCellsAfter_iff, List.mem_append]
  constructor <;> right <;>
    simp only [add, circuit_norm, RegionOperations.assignedCells,
      List.flatMap_cons, RegionOperation.assignedCells, List.singleton_append,
      List.mem_cons, true_or]

/-- Both coordinates returned by the layouter-level complete-addition call are
assigned in its single region. -/
theorem addFormal_call_output_cells_assigned
    (config : Config) (input : Var Inputs Fp) (self : RegionIndex) :
    let output := addFormal.output config input self
    output.x.cell ∈ Operations.assignedCellsFrom
        ((addFormal.call config input).operations self) self ∧
      output.y.cell ∈ Operations.assignedCellsFrom
        ((addFormal.call config input).operations self) self := by
  rw [addFormal_output_cells, FormalCircuit.call_operations]
  have hassigned := add_output_cells_assigned config 0 input self []
  rw [FormalRegionCircuit.call_operations] at hassigned
  simp only [addFormal, FormalRegionCircuit.toFormal, operations_assignRegion,
    Operations.assignedCellsFrom, List.append_nil]
  simpa only [add_output_cells, AssignedCell.of_cell,
    RegionOperations.mem_assignedCellsAfter_iff, List.nil_append] using hassigned

/-- The layouter-level complete addition returns its coordinates in `xQR` and `yQR`. -/
@[keygen_norm, keygen_output_norm]
theorem addFormal_output_x_column (config : Config) (input : Var Inputs Fp)
    (self : RegionIndex) :
    (addFormal.output config input self).x.cell.column = config.xQR := by
  rfl

@[keygen_norm, keygen_output_norm]
theorem addFormal_output_y_column (config : Config) (input : Var Inputs Fp)
    (self : RegionIndex) :
    (addFormal.output config input self).y.cell.column = config.yQR := by
  rfl

derive_contract_bridges addFormal := addFormal

end Add

end Zcash.Circuits.Ecc
