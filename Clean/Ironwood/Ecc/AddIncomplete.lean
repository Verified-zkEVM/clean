import Clean.Halo2
import Clean.Orchard.Specs.Pallas
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.WitnessPoint

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
## Arithmetic on halo2 witness expressions

The arithmetic instances for witness expressions (`Sub`/`Mul`/`Inv`/`Add`/`Neg`) in
`Clean/Circuit/WitnessIRSugar.lean` are stated only for main Clean's `FExpr F`
(variable atom `Expression F`). Halo2's `FExpr F` uses `AssignedCell F` atoms, so we
provide the same instances here at the halo2 atom — this lets us reuse
`Point.nondegenerateAdd` to build the witness program for R.
-/
namespace FExprInst
scoped instance : Add (FExpr Fp) := ⟨.add⟩
scoped instance : Mul (FExpr Fp) := ⟨.mul⟩
scoped instance : Inv (FExpr Fp) := ⟨.inv⟩
scoped instance : Neg (FExpr Fp) := ⟨.neg⟩
scoped instance : Sub (FExpr Fp) := ⟨.sub⟩
end FExprInst

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

/-- Componentwise verifier evaluation of `Inputs`. -/
theorem Inputs.eval_eq (env : Placed Environment Fp) (input : Inputs (AssignedCell Fp)) :
    eval env input = { p := eval env input.p, q := eval env input.q } := by
  simp_all [circuit_norm, explicit_provable_type, fromComponents, toComponents, components,
    ProvableStruct.componentsFromElements, ProvableStruct.componentsToElements]
  and_intros <;> ((try rw [Vector.getElem_extract]); (try simp); rfl)

/-- Componentwise prover evaluation of `Inputs`. -/
theorem Inputs.eval_eq_prover (env : Placed ProverEnvironment Fp) (input : Inputs (AssignedCell Fp)) :
    eval env input = { p := eval env input.p, q := eval env input.q } := by
  simp_all [circuit_norm, explicit_provable_type, fromComponents, toComponents, components,
    ProvableStruct.componentsFromElements, ProvableStruct.componentsToElements]
  and_intros <;> ((try rw [Vector.getElem_extract]); (try simp); rfl)

open scoped FExprInst in
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

  ProverAssumptions input _ :=
    input.p.OnCurve ∧ input.q.OnCurve ∧ input.p.x ≠ input.q.x
  -- no ProverSpec (default True): `Assumptions → Spec` already ties output to input,
  -- which is all downstream completeness proofs need. Rule of thumb: only introduce a
  -- (minimal) ProverSpec once a parent gadget's completeness actually requires it —
  -- typically for hint-consuming gadgets (cf. WitnessPoint's `output = input`).

  soundness := by
    intro config offset
    rw [FormalRegionCircuit.soundness_iff]
    rintro self env input_var input ⟨ox, oy⟩ h_input h_output h_assumptions hc
    -- reduce the constraints: enableGate produces the two polynomials at the gate row,
    -- copyAdvice produces the copy equalities.
    simp only [circuit_norm, gate, Constraints.withSelector] at hc h_output
    -- decompose the input equation: cell reads (as they appear in the gate polys after the
    -- copy rewrites) equal the input coordinates
    rw [Inputs.eval_eq, Point.eval_eq, Point.eval_eq] at h_input
    simp only [ProvableType.eval_field, AssignedCell.eval] at h_input
    have hipx := congrArg (fun r => r.p.x) h_input
    have hipy := congrArg (fun r => r.p.y) h_input
    have hiqx := congrArg (fun r => r.q.x) h_input
    have hiqy := congrArg (fun r => r.q.y) h_input
    simp only at hipx hipy hiqx hiqy
    clear h_input
    -- decompose the output equation into `ox`/`oy` equalities
    rw [Point.eval_eq, Orchard.Point.mk.injEq] at h_output
    simp only [ProvableType.eval_field, AssignedCell.eval] at h_output
    obtain ⟨hox, hoy⟩ := h_output
    obtain ⟨⟨hpoly1, hpoly2⟩, hcpx, hcpy, hcqx, hcqy⟩ := hc
    simp only [Cell.eval] at hcpx hcpy hcqx hcqy
    -- normalize the R-row index spelling (`↑(a+offset)+1` → `↑(a+(offset+1))`) to match `hox`/`hoy`
    have hrow : ((env.place self + offset : ℕ) : ℤ) + 1 = ((env.place self + (offset + 1) : ℕ) : ℤ) := by
      push_cast; ring
    -- rewrite the gate polys into the input/output coordinates
    simp only [hrow, hox, hoy, hcpx, hcpy, hcqx, hcqy, hipx, hipy, hiqx, hiqy] at hpoly1 hpoly2
    obtain ⟨hpx_curve, hqx_curve, hxne⟩ := h_assumptions
    have hp1 : poly1 input.p.x input.p.y input.q.x input.q.y ox oy = 0 := by
      simp only [poly1]; linear_combination hpoly1
    have hp2 : poly2 input.p.x input.p.y input.q.x input.q.y ox oy = 0 := by
      simp only [poly2]; linear_combination hpoly2
    -- `hsum` is stated over rebuilt records `{x:=input.p.x,..}`, defeq to `input.p`/`input.q`
    have hxne' : input.p.x ≠ input.q.x := hxne
    have hsum := eq_nondegenerateAdd_of_polys_zero hxne' hp1 hp2
    have hsum' : ({ x := ox, y := oy } : Point Fp) = input.p.nondegenerateAdd input.q := hsum
    rw [hsum']
    exact ⟨Orchard.Point.nondegenerateAdd_onCurve hpx_curve hqx_curve hxne',
      Orchard.Point.nondegenerateAdd_eq_add
        (Orchard.Point.ne_zero_of_onCurve hpx_curve) (Orchard.Point.ne_zero_of_onCurve hqx_curve) hxne'⟩

  completeness := by
    intro config offset
    rw [FormalRegionCircuit.completeness_iff]
    rintro self ⟨place, penv⟩ input_var input _output h_input _h_output hwit hpa
    simp only [circuit_norm, gate, Constraints.withSelector] at hwit hpa h_input ⊢
    -- unpack the witness-assignment equalities (copy `ExtendsWitness`es are trivially `True`)
    obtain ⟨hwpx, -, hwpy, -, hwqx, -, hwqy, -, hwrx, hwry⟩ := hwit
    -- input coordinates equal the copied cell reads (via `h_input`)
    rw [Inputs.eval_eq_prover, Point.eval_eq_prover, Point.eval_eq_prover] at h_input
    simp only [ProvableType.eval_field_prover, AssignedCell.eval] at h_input
    have hipx := congrArg (fun r => r.p.x) h_input
    have hipy := congrArg (fun r => r.p.y) h_input
    have hiqx := congrArg (fun r => r.q.x) h_input
    have hiqy := congrArg (fun r => r.q.y) h_input
    simp only at hipx hipy hiqx hiqy
    obtain ⟨hpCurve, hqCurve, hxne⟩ := hpa
    -- reduce `readVar` cell reads to the same `penv.get` form as `hipx`, then chain
    simp only [Witgen.WitgenEnv.readVar, AssignedCell.eval] at hwpx hwpy hwqx hwqy
    have hpx_eq := hwpx.trans hipx
    have hpy_eq := hwpy.trans hipy
    have hqx_eq := hwqx.trans hiqx
    have hqy_eq := hwqy.trans hiqy
    -- the assigned R-row values are the `nondegenerateAdd` coordinates over the input coords
    simp only [Orchard.Point.nondegenerateAdd, Witgen.FExprOver.eval, Witgen.WitgenEnv.readVar,
      AssignedCell.eval, hipx, hipy, hiqx, hiqy] at hwrx hwry
    have hxne' : input.p.x ≠ input.q.x := hxne
    -- gate polynomials vanish at the `nondegenerateAdd` result
    have hpolys := polys_zero_of_nondegenerateAdd (xP := input.p.x) (yP := input.p.y)
      (xQ := input.q.x) (yQ := input.q.y) hxne'
    simp only at hpolys
    obtain ⟨hp1, hp2⟩ := hpolys
    -- normalize the R-row index spelling in the goal so the witness equations apply
    have hgrow : ((place self + offset : ℕ) : ℤ) + 1 = ((place self + (offset + 1) : ℕ) : ℤ) := by
      push_cast; ring
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · -- poly1
      simp only [poly1, Orchard.Point.nondegenerateAdd] at hp1
      simp only [hgrow, hwrx, hpx_eq, hpy_eq, hqx_eq, hqy_eq]
      linear_combination hp1
    · -- poly2
      simp only [poly2, Orchard.Point.nondegenerateAdd] at hp2
      simp only [hgrow, hwrx, hwry, hpx_eq, hpy_eq, hqx_eq, hqy_eq]
      linear_combination hp2
    · -- copy equalities
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        simp only [Cell.eval, hpx_eq, hpy_eq, hqx_eq, hqy_eq,
          hipx, hipy, hiqx, hiqy]

end AddIncomplete

end Halo2.Ironwood.Ecc
