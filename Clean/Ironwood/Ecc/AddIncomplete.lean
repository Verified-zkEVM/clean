import Clean.Halo2
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.Basic

namespace Zcash.Circuits.Ecc

open Halo2
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

def gate (qAddIncomplete : Selector) (xP yP xQR yQR : Column .advice) : Gate Fp :=
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
  Gate.withSelector "incomplete addition" qAddIncomplete
    [x_p, y_p, x_q, y_q, x_r, y_r]
    [("x_r", poly1), ("y_r", poly2)]

@[circuit_norm, configure_selector_norm, keygen_norm]
theorem gate_selector
    (qAddIncomplete : Selector) (xP yP xQR yQR : Column .advice) :
    (gate qAddIncomplete xP yP xQR yQR).selector = qAddIncomplete := rfl

/-!
## The gadget

Input is the pair of input points (P, Q). We use a small `ProvableStruct` for it, matching
the repo convention (`Ecc.AddIncomplete.Input`). The verifier assumptions and spec
express what the Rust gadget guarantees: incomplete addition is only correct when both
inputs are non-identity on-curve points and `x_p ≠ x_q` (the Rust `assign_region` errors on
`P = O`, `Q = O`, or `x_p = x_q`).
-/

/-- The pair of input points P and Q. -/
structure Inputs (F : Type) where
  p : Point F
  q : Point F
deriving ProvableStruct

/-- The point-coordinate columns registered for equality by `AddIncomplete.add.configure`. -/
@[keygen_norm]
def permutationColumns (config : Config) : List AnyColumn :=
  [config.xP, config.yP, config.xQR, config.yQR]

def synthesisSummary (config : Config) (offset : ℕ) :
    FloorPlanner.RegionSynthesisSummary :=
  .ofColumns
    [.selector config.qAddIncomplete.index,
      .column .advice config.xP.index,
      .column .advice config.yP.index,
      .column .advice config.xQR.index,
      .column .advice config.yQR.index,
      .column .advice config.xQR.index,
      .column .advice config.yQR.index]
    (offset + 2) 0 [(config.qAddIncomplete.index, offset)]

def add : FormalRegionCircuit Fp
    (Column .advice × Column .advice × Column .advice × Column .advice) Config
    Inputs Point where
  /- Rust `Config::configure`: enable equality on the four advice columns, allocate the
    simple selector, register the gate. -/
  configure | (xP, yP, xQR, yQR) => do
    enableEquality xP
    enableEquality yP
    enableEquality xQR
    enableEquality yQR
    let qAddIncomplete ← selector
    createGate (gate qAddIncomplete xP yP xQR yQR)
    return { qAddIncomplete, xP, yP, xQR, yQR }

  elaborated :=
    { keygenRequirements :=
        { inputCells _ _ input :=
            [input.p.x.cell, input.p.y.cell, input.q.x.cell, input.q.y.cell] }
      synthesisSummary config offset _ _ := synthesisSummary config offset
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
        all_goals simp only [synthesisSummary, circuit_norm, gate,
          synthesis_summary_norm] }

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
    circuit_proof_start2 [gate]
    obtain ⟨hpoly1, hpoly2⟩ := region_0
    obtain ⟨hpx_curve, hqx_curve, hxne⟩ := assumptions
    -- formulate gate polys in terms of `nondegenerateAdd`
    have hsum : ⟨output_x, output_y⟩ = Point.nondegenerateAdd
        ⟨input_p_x, input_p_y⟩ ⟨input_q_x, input_q_y⟩ := by
      grind [Point.nondegenerateAdd]
    rw [hsum]
    use Point.nondegenerateAdd_onCurve hpx_curve hqx_curve hxne
    apply Point.nondegenerateAdd_eq_add ?_ ?_ hxne
    exact Point.ne_zero_of_onCurve hpx_curve
    exact Point.ne_zero_of_onCurve hqx_curve

  completeness := by
    circuit_proof_start2 [gate, Point.nondegenerateAdd]
    obtain ⟨-, -, hxne⟩ := assumptions
    simp_all only
    grind

/-- Incomplete addition never requests a deferred constant allocation. -/
@[synthesis_summary_norm]
theorem add_synthesisSummary_eq
    (config : Config) (offset : ℕ) (input : Var Inputs Fp)
    (region : RegionIndex) :
    add.elaborated.synthesisSummary config offset input region =
      synthesisSummary config offset := rfl

@[synthesis_summary_norm]
theorem synthesisSummary_constantSiteCount (config : Config) (offset : ℕ) :
    (synthesisSummary config offset).constantSiteCount = 0 := by
  simp only [synthesisSummary, synthesis_summary_norm]

@[synthesis_summary_norm]
theorem add_synthesisSummary_constantSiteCount
    (config : Config) (offset : ℕ) (input : Inputs (AssignedCell Fp))
    (region : RegionIndex) :
    (add.elaborated.synthesisSummary
      config offset input region).constantSiteCount = 0 := by
  rw [add_synthesisSummary_eq]
  simp only [synthesisSummary, circuit_norm]

@[keygen_norm]
theorem Configured.fixedColumns_eq_nil {config : Config}
    (configured : add.Configured config) :
    configured.fixedColumns = [] := by
  rcases configured with ⟨configInput, counts, hconfig, outputEq⟩
  cases outputEq
  simp only [FormalRegionCircuit.Configured.fixedColumns]
  constructor

@[keygen_norm]
theorem Configured.lookups_eq_nil {config : Config}
    (configured : add.Configured config) :
    configured.lookups = [] := by
  rcases configured with ⟨configInput, counts, hconfig, outputEq⟩
  cases outputEq
  simp only [FormalRegionCircuit.Configured.lookups,
    FormalRegionCircuit.keygenRequirements,
    ElaboratedRegionCircuit.keygenRequirements, add, keygen_norm]

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
theorem Configured.inputCells_eq {config : Config}
    (configured : add.Configured config) (input : Var Inputs Fp) :
    configured.inputCells input =
      [input.p.x.cell, input.p.y.cell, input.q.x.cell, input.q.y.cell] := by
  rfl

/-- Both coordinates returned by incomplete addition are assigned by its call body. -/
theorem add_output_cells_assigned (config : Config) (offset : ℕ)
    (input : Var Inputs Fp) (self : RegionIndex) (available : List Cell) :
    let output := add.output config offset input self
    output.x.cell ∈
        (((add.call config offset input).operations self).assignedCellsAfter self available) ∧
      output.y.cell ∈
        (((add.call config offset input).operations self).assignedCellsAfter self available) := by
  rw [FormalRegionCircuit.call_operations]
  simp only [FormalRegionCircuit.output]
  rw [add.elaborated.output_eq]
  simp only [add, circuit_norm, AssignedCell.of_cell,
    RegionOperations.mem_assignedCellsAfter_iff, List.mem_append]
  constructor <;> right <;>
    simp only [RegionOperations.assignedCells, List.flatMap_cons,
      RegionOperation.assignedCells, List.singleton_append,
      List.flatMap_nil, List.nil_append, List.mem_cons, true_or, or_true]

@[keygen_norm]
theorem Configured.inputPermutationColumns_eq {config : Config}
    (configured : add.Configured config) (input : Var Inputs Fp) :
    configured.inputPermutationColumns input =
      [input.p.x.cell.column, input.p.y.cell.column,
        input.q.x.cell.column, input.q.y.cell.column] := by
  rfl

@[keygen_norm]
theorem configure_output_permutationColumns
    (xP yP xQR yQR : Column .advice) (counts : ConfigureCounts) :
    permutationColumns
        ((add.configure (xP, yP, xQR, yQR)).output counts) =
      [xP, yP, xQR, yQR] := by
  simp [add, permutationColumns]

end AddIncomplete

end Zcash.Circuits.Ecc
