import Clean.Halo2
import Clean.Orchard.Specs.Pallas
import Clean.Ironwood.Ecc.Basic

namespace Halo2.Ironwood.Ecc
/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/add_incomplete.rs`
- `incomplete addition`

Port of the incomplete point-addition gadget. Mirrors `WitnessPoint.lean`:
a `Config` holding exactly the Rust `Config` fields, the custom gate as a standalone pure
def of the selector and columns (referenced by both `configure` and the soundness proof),
algebraic core lemmas, and the `FormalRegionCircuit` bundle.

The Rust chip's `EccConfig` hands `Config::configure` four advice columns
`x_p, y_p, x_qr, y_qr`; the parent enables equality on them and allocates one simple
selector `q_add_incomplete`. The gate queries `x_p, y_p` at `Rotation::cur()`, `x_qr, y_qr`
at both `Rotation::cur()` (= Q) and `Rotation::next()` (= R). `assign_region` copies P into
`(x_p, y_p)` at `offset`, Q into `(x_qr, y_qr)` at `offset`, and assigns R into
`(x_qr, y_qr)` at `offset + 1`.
-/

namespace AddIncomplete

/-- The Rust `add_incomplete::Config`: one simple selector plus the four advice columns.
`x_qr`/`y_qr` carry Q at the current row and R at the next row. -/
structure Config where
  qAddIncomplete : Selector
  xP : Column .advice
  yP : Column .advice
  xQR : Column .advice
  yQR : Column .advice

/-- The two "incomplete addition" gate polynomials, as a pure function of the columns —
ported verbatim from the Rust `create_gate` closure. `x_p, y_p` are read at
`Rotation::cur()` (0); `x_qr, y_qr` are read at `Rotation::cur()` (0, = Q) and
`Rotation::next()` (1, = R).

- poly1: `(x_r + x_q + x_p)·(x_p − x_q)² − (y_p − y_q)²`
- poly2: `(y_r + y_q)·(x_p − x_q) − (y_p − y_q)·(x_q − x_r)` -/
def gate (qAddIncomplete : Selector) (xP yP xQR yQR : Column .advice) : Gate Fp where
  name := "incomplete addition"
  selector := qAddIncomplete
  constraints :=
    let x_p : Expression Fp Query := queryAdvice xP 0
    let y_p : Expression Fp Query := queryAdvice yP 0
    let x_q : Expression Fp Query := queryAdvice xQR 0
    let y_q : Expression Fp Query := queryAdvice yQR 0
    let x_r : Expression Fp Query := queryAdvice xQR 1
    let y_r : Expression Fp Query := queryAdvice yQR 1
    let poly1 :=
      (x_r + x_q + x_p) * (x_p - x_q) * (x_p - x_q) - (y_p - y_q) * (y_p - y_q)
    let poly2 :=
      (y_r + y_q) * (x_p - x_q) - (y_p - y_q) * (x_q - x_r)
    Constraints.withSelector qAddIncomplete [("x_r", poly1), ("y_r", poly2)]

/-- Rust `Config::configure`: enable equality on the four advice columns, allocate the
simple selector, register the gate. -/
def configure (xP yP xQR yQR : Column .advice) : Configure Fp Config := do
  enableEquality xP.toAny
  enableEquality yP.toAny
  enableEquality xQR.toAny
  enableEquality yQR.toAny
  let qAddIncomplete ← selector
  createGate (gate qAddIncomplete xP yP xQR yQR)
  return { qAddIncomplete, xP, yP, xQR, yQR }

/-!
## Algebraic core lemmas

These are the `WitnessPoint`-style separated cores: the soundness direction shows the two
gate polynomials imply the output is the incomplete sum, and the completeness direction
shows a valid incomplete sum satisfies the two polynomials. Both are stated over concrete
field values (the coordinates of P, Q, R), and reuse the phase-one point-addition
definition `Point.nondegenerateAdd` (via the Orchard specs).

We restate the two polynomials over concrete `Fp` coordinates so the lemmas do not depend
on the gate's `Query`/`Expression` machinery.
-/

/-- poly1 at concrete coordinates. -/
def poly1 (xP yP xQ yQ xR _yR : Fp) : Fp :=
  (xR + xQ + xP) * (xP - xQ) * (xP - xQ) - (yP - yQ) * (yP - yQ)

/-- poly2 at concrete coordinates. -/
def poly2 (xP yP xQ yQ xR yR : Fp) : Fp :=
  (yR + yQ) * (xP - xQ) - (yP - yQ) * (xQ - xR)

/-- Soundness core: if both gate polynomials vanish at concrete coordinates and
`x_p ≠ x_q`, then `R = P +ᵢ Q` (the incomplete sum). Mirrors the phase-one
`Orchard.Ecc.AddIncomplete.Gate.eq_nondegenerateAdd_of_polys_zero`. -/
theorem eq_nondegenerateAdd_of_polys_zero {xP yP xQ yQ xR yR : Fp}
    (hx : xP ≠ xQ)
    (h1 : poly1 xP yP xQ yQ xR yR = 0)
    (h2 : poly2 xP yP xQ yQ xR yR = 0) :
    ({ x := xR, y := yR } : Point Fp)
      = ({ x := xP, y := yP } : Point Fp).nondegenerateAdd { x := xQ, y := yQ } := by
  simp only [poly1, poly2] at h1 h2
  unfold Orchard.Point.nondegenerateAdd
  have hden : xQ - xP ≠ 0 := fun h => hx (sub_eq_zero.mp h).symm
  have hden' : xP - xQ ≠ 0 := fun h => hx (sub_eq_zero.mp h)
  rw [Orchard.Point.mk.injEq]
  have hxout :
      xR = (yQ - yP) * (xQ - xP)⁻¹ * ((yQ - yP) * (xQ - xP)⁻¹) - xP - xQ := by
    apply sub_eq_zero.mp
    field_simp [hden, hden']
    ring_nf at h1 ⊢
    linear_combination h1
  refine ⟨hxout, ?_⟩
  rw [← hxout]
  apply sub_eq_zero.mp
  field_simp [hden, hden']
  ring_nf at h2 ⊢
  linear_combination -h2

/-- Completeness core: the incomplete sum `R = P +ᵢ Q` satisfies both gate polynomials
(given `x_p ≠ x_q`). Mirrors the phase-one
`Orchard.Ecc.AddIncomplete.Gate.polys_zero_of_nondegenerateAdd`. -/
theorem polys_zero_of_nondegenerateAdd {xP yP xQ yQ : Fp}
    (hx : xP ≠ xQ) :
    let r := ({ x := xP, y := yP } : Point Fp).nondegenerateAdd { x := xQ, y := yQ }
    poly1 xP yP xQ yQ r.x r.y = 0 ∧ poly2 xP yP xQ yQ r.x r.y = 0 := by
  simp only [poly1, poly2, Orchard.Point.nondegenerateAdd]
  have hden : xQ - xP ≠ 0 := fun h => hx (sub_eq_zero.mp h).symm
  constructor <;> field_simp [hden] <;> ring

/-!
## The gadget

Input is the pair of input points (P, Q). We use a small `ProvableStruct` for it, matching
the repo convention (`Orchard.Ecc.AddIncomplete.Input`). The verifier assumptions and spec
express what the Rust gadget guarantees: incomplete addition is only correct when both
inputs are non-identity on-curve points and `x_p ≠ x_q` (the Rust `assign_region` errors on
`P = O`, `Q = O`, or `x_p = x_q`).
-/

/-- The pair of input points P and Q. -/
structure Inputs (F : Type) where
  p : Point F
  q : Point F
deriving ProvableStruct

def add : FormalRegionCircuit Fp
    (Column .advice × Column .advice × Column .advice × Column .advice) Config
    Inputs Point where
  configure := fun (xP, yP, xQR, yQR) => configure xP yP xQR yQR

  synthesize config offset (input : Inputs (AssignedCell Fp)) := do
    -- enable `q_add_incomplete` selector at `offset`
    (gate config.qAddIncomplete config.xP config.yP config.xQR config.yQR).enable offset
    -- copy P into `(x_p, y_p)` at `offset`
    let _xP ← copyAdvice input.p.x config.xP offset
    let _yP ← copyAdvice input.p.y config.yP offset
    -- copy Q into `(x_qr, y_qr)` at `offset`
    let _xQ ← copyAdvice input.q.x config.xQR offset
    let _yQ ← copyAdvice input.q.y config.yQR offset
    -- compute R = P +ᵢ Q as a witness program, assign into `(x_qr, y_qr)` at `offset + 1`
    let r : Point (FExpr Fp) :=
      ({ x := .expr input.p.x, y := .expr input.p.y } : Point (FExpr Fp)).nondegenerateAdd
        { x := .expr input.q.x, y := .expr input.q.y }
    let xR ← assignAdvice config.xQR (offset + 1) (.ofFExpr r.x)
    let yR ← assignAdvice config.yQR (offset + 1) (.ofFExpr r.y)
    return ⟨ xR, yR ⟩

  -- P, Q are non-identity on-curve points with distinct x-coordinates (Rust's exceptional
  -- cases: P = O, Q = O, x_p = x_q all cause `assign_region` to error).
  Assumptions input :=
    input.p.OnCurve ∧ input.q.OnCurve ∧ input.p.x ≠ input.q.x
  Spec input output _ :=
    output.OnCurve ∧ output = input.p + input.q

  -- no ProverAssumptions (default True): completeness already assumes `Assumptions` on
  -- the input's verifier-visible value, and this gadget needs no hint-side facts.
  -- no ProverSpec (default True): `Assumptions → Spec` already ties output to input,
  -- which is all downstream completeness proofs need. Rule of thumb: only introduce a
  -- (minimal) ProverSpec once a parent gadget's completeness actually requires it —
  -- typically for hint-consuming gadgets (cf. WitnessPoint's `output = input`).

  soundness := by
    intro config offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output h_assumptions hc
    -- reduce circuit structure (gate polys + copy equalities), running the eval simprocs
    simp only [circuit_norm, gate, Constraints.withSelector] at hc h_output
    -- destructure input/output; split the input/output eval equations into coordinates
    provable_type_simp
    -- ══ user-facing half: pure field values + curve math ══
    obtain ⟨⟨hpoly1, hpoly2⟩, hcpx, hcpy, hcqx, hcqy⟩ := hc
    -- eval → value: gate cell = copy source (`hc…`) = input coord (`h_input`), R row = output
    -- coord (`h_output`)
    simp only [hcpx, hcpy, hcqx, hcqy, h_input, h_output] at hpoly1 hpoly2
    obtain ⟨hpx_curve, hqx_curve, hxne⟩ := h_assumptions
    have hp1 : poly1 input_p_x input_p_y input_q_x input_q_y output_x output_y = 0 := by
      simp only [poly1]; linear_combination hpoly1
    have hp2 : poly2 input_p_x input_p_y input_q_x input_q_y output_x output_y = 0 := by
      simp only [poly2]; linear_combination hpoly2
    have hsum := eq_nondegenerateAdd_of_polys_zero hxne hp1 hp2
    rw [hsum]
    exact ⟨Orchard.Point.nondegenerateAdd_onCurve hpx_curve hqx_curve hxne,
      Orchard.Point.nondegenerateAdd_eq_add
        (Orchard.Point.ne_zero_of_onCurve hpx_curve) (Orchard.Point.ne_zero_of_onCurve hqx_curve) hxne⟩

  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit hA hlast
    -- reduce circuit structure, running the eval simprocs
    simp only [circuit_norm, gate, Constraints.withSelector] at hwit hA h_input h_output ⊢
    -- destructure input/output/input_var; split every struct equation into coordinates
    provable_type_simp
    -- ══ user-facing half ══
    -- unpack the witness-assignment equalities (copy `ExtendsWitness`es are trivially `True`)
    obtain ⟨hwpx, -, hwpy, -, hwqx, -, hwqy, -, hwrx, hwry⟩ := hwit
    -- reduce the witness cell reads to input coords: `readVar` (copies) / `FExprOver.eval`
    -- (the R row, a `nondegenerateAdd` witness) → `env.get` → input coord via `h_input`
    simp only [Witgen.WitgenEnv.readVar, Orchard.Point.nondegenerateAdd,
      Witgen.FExprOver.eval, AssignedCell.eval, h_input] at hwpx hwpy hwqx hwqy hwrx hwry
    -- land the `Assumptions` facts on the input coordinates
    simp only [h_input] at hA
    obtain ⟨hpCurve, hqCurve, hxne⟩ := hA
    -- gate polynomials vanish at the `nondegenerateAdd` result
    have hpolys := polys_zero_of_nondegenerateAdd (xP := input_p_x) (yP := input_p_y)
      (xQ := input_q_x) (yQ := input_q_y) hxne
    simp only at hpolys
    obtain ⟨hp1, hp2⟩ := hpolys
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- poly1
      simp only [poly1, Orchard.Point.nondegenerateAdd] at hp1
      simp only [hwrx, hwpx, hwpy, hwqx, hwqy]
      linear_combination hp1
    · -- poly2
      simp only [poly2, Orchard.Point.nondegenerateAdd] at hp2
      simp only [hwrx, hwry, hwpx, hwpy, hwqx, hwqy]
      linear_combination hp2
    · -- copy equalities
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp only [hwpx, hwpy, hwqx, hwqy, h_input]

end AddIncomplete

end Halo2.Ironwood.Ecc
