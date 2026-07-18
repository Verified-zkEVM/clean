import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Orchard.Specs.Pallas
import Clean.Orchard.Ecc.MulFixed
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.AddIncomplete
import Clean.Ironwood.Utilities.DecomposeRunningSum

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul_fixed.rs` (read in full) —
the shared core of fixed-base scalar multiplication (`H = 8`, 3-bit windows).

- `Config` (lines 35-52): the running-sum config, the 8 Lagrange-coefficient fixed
  columns, the `fixed_z` column, the `window`/`u` advices, and the `add`/`add_incomplete`
  child configs.
- `configure` (lines 54-104): equality on `window`/`u`, the running-sum config on a fresh
  selector, a fresh `fixed_z` column, then the "Running sum coordinates check" gate
  registered on the running sum's OWN `q_range_check` selector (lines 115-129) — so
  enabling a running-sum row fires both the range check and the coords check.
- `coords_check` (lines 131-169): per window row, the interpolated `x_p` (degree-7
  Lagrange polynomial in the window value over the 8 fixed columns), the `u² = y_p + z`
  sign fix, and the curve equation.
- The region body `assign_region_inner` (lines 171-193): `assign_fixed_constants` (the
  per-window fixed columns + coords-gate enables, lines 195-252), the window-0
  accumulator initialization, the incomplete-addition window loop (lines 323-360), and
  the most significant window (lines 378-405). Realized here as region-relative
  `RegionCircuit` pieces consumed by the wrappers (`base_field_elem`, later
  `full_width`/`short`); the wrapper bundles own the composed proofs.

The proof-content donor is `Clean/Orchard/Ecc/MulFixed.lean`: `CoordsParams`,
`interpolate`, `FixedBase` (the fixed-base data + the halo2 out-of-circuit invariants)
and its window-point algebra (`windowScalar`/`windowPoint`/`partialSum`/
`coords_eq_windowPoint`) are consumed directly from there.
-/

namespace Halo2.Ironwood.Ecc.MulFixed

open Halo2.Ironwood (Fp)
open Orchard (Point)
open Orchard.Ecc.MulFixed (CoordsParams interpolate FixedBase windowPoint windowScalar)

open Orchard (pallasB)
open Halo2.Ironwood.DecomposeRunningSum (copyDecompose)

/-- Rust `H = 2^3` (`constants.rs:15`): the window size. -/
def H : ℕ := 8

/-- Rust `NUM_WINDOWS = 85` (`constants.rs:18`): windows of a full-width decomposition. -/
def NUM_WINDOWS : ℕ := 85

/-- The fixed-base DATA a synthesize needs (no invariants): the per-window fixed-column
values (`params`), and the window tables feeding the witness programs (the generator
point and the `u` square roots). The donor `FixedBase` (data + the halo2 out-of-circuit
invariants) lowers to this via `toData`; proof-free consumers (the VK layout tests, which
only need concrete `params` values in the keygen view) construct it directly from dumped
tables. -/
structure FixedBaseData where
  params : ℕ → CoordsParams Fp
  point : Point Fp
  u : ℕ → ℕ → Fp

/-- The data of a proven fixed base. -/
def _root_.Orchard.Ecc.MulFixed.FixedBase.toData (B : FixedBase) : FixedBaseData :=
  { params := B.params, point := B.point, u := B.u }

/-- Rust `mul_fixed::Config` (`mul_fixed.rs:35-52`). -/
structure Config where
  runningSumConfig : DecomposeRunningSum.Config
  lagrangeCoeffs : Fin 8 → Column .fixed
  fixedZ : Column .fixed
  window : Column .advice
  u : Column .advice
  addConfig : Add.Config
  addIncompleteConfig : AddIncomplete.Config

/-! ## The "Running sum coordinates check" gate (`mul_fixed.rs:106-169`) -/

/-- `window_pow[k] = (0..k).fold(Const 1, |acc,_| acc * window)` — the exact Rust AST
(`mul_fixed.rs:143-149`): `1`, `1·w`, `(1·w)·w`, …. -/
def windowPow (word : Expression Fp Query) (k : ℕ) : Expression Fp Query :=
  (List.range k).foldl (fun acc _ => acc * word) (Expression.const 1)

/-- The interpolated `x_p` (`mul_fixed.rs:151-154`): fold from `Const 0`,
`acc + window_pow[k] · lagrange_coeffs[k]` — the 8-iteration fold written out (identical
AST; keeps the eval bridge fold-free). -/
def interpolatedX (cfg : Config) (word : Expression Fp Query) : Expression Fp Query :=
  Expression.const 0
    + windowPow word 0 * queryFixed (cfg.lagrangeCoeffs 0)
    + windowPow word 1 * queryFixed (cfg.lagrangeCoeffs 1)
    + windowPow word 2 * queryFixed (cfg.lagrangeCoeffs 2)
    + windowPow word 3 * queryFixed (cfg.lagrangeCoeffs 3)
    + windowPow word 4 * queryFixed (cfg.lagrangeCoeffs 4)
    + windowPow word 5 * queryFixed (cfg.lagrangeCoeffs 5)
    + windowPow word 6 * queryFixed (cfg.lagrangeCoeffs 6)
    + windowPow word 7 * queryFixed (cfg.lagrangeCoeffs 7)

/-- Rust `coords_check` (`mul_fixed.rs:131-169`): the shared per-window-row constraint
list over a given window-value expression. Reads `x_p`/`y_p` on the add config's columns
at `cur`, `u` at `cur`, `fixed_z` and the 8 Lagrange columns as rotation-0 fixed queries.
Used by BOTH the running-sum coords gate (word = `z_cur − z_next·8`) and the full-width
gate (word = the raw `window` query). -/
def coordsCheck (cfg : Config) (word : Expression Fp Query) :
    List (String × Expression Fp Query) :=
  let yP : Expression Fp Query := queryAdvice cfg.addConfig.yP 0
  let xP : Expression Fp Query := queryAdvice cfg.addConfig.xP 0
  let z : Expression Fp Query := queryFixed cfg.fixedZ
  let u : Expression Fp Query := queryAdvice cfg.u 0
  -- check x: interpolated_x − x_p   (`mul_fixed.rs:156-157`)
  let xCheck := interpolatedX cfg word - xP
  -- check y: u² − y_p − z           (`mul_fixed.rs:158-159`)
  let yCheck := u * u - yP - z
  -- on-curve: y_p² − x_p²·x_p − b   (`mul_fixed.rs:160-162`)
  let onCurve := yP * yP - xP * xP * xP - (pallasB : Expression Fp Query)
  [("check x", xCheck), ("check y", yCheck), ("on-curve", onCurve)]

/-- The "Running sum coordinates check" gate (`mul_fixed.rs:115-129`), registered on the
running sum's `q_range_check` selector. The window value is derived:
`word = z_cur − z_next·8` (`mul_fixed.rs:120-125`, constant scale on the right). -/
def coordsGate (cfg : Config) : Gate Fp where
  name := "Running sum coordinates check"
  selector := cfg.runningSumConfig.qRangeCheck
  constraints :=
    let zCur : Expression Fp Query := queryAdvice cfg.window 0
    let zNext : Expression Fp Query := queryAdvice cfg.window 1
    let word := zCur - zNext * (((H : ℕ) : Fp) : Expression Fp Query)
    Constraints.withSelector cfg.runningSumConfig.qRangeCheck (coordsCheck cfg word)

/-- The `CoordsParams` read off the environment's fixed cells at a given row — what the
coords gate's queries see. -/
def readParams (cfg : Config) (f : Query → Fp) : CoordsParams Fp where
  z := f (.fixed cfg.fixedZ 0)
  lagrange0 := f (.fixed (cfg.lagrangeCoeffs 0) 0)
  lagrange1 := f (.fixed (cfg.lagrangeCoeffs 1) 0)
  lagrange2 := f (.fixed (cfg.lagrangeCoeffs 2) 0)
  lagrange3 := f (.fixed (cfg.lagrangeCoeffs 3) 0)
  lagrange4 := f (.fixed (cfg.lagrangeCoeffs 4) 0)
  lagrange5 := f (.fixed (cfg.lagrangeCoeffs 5) 0)
  lagrange6 := f (.fixed (cfg.lagrangeCoeffs 6) 0)
  lagrange7 := f (.fixed (cfg.lagrangeCoeffs 7) 0)

/-- `interpolatedX` evaluates to the donor `interpolate` over the read-back params — the
bridge from the gate AST to the donor's coordinate algebra. -/
theorem eval_interpolatedX (cfg : Config) (word : Expression Fp Query) (f : Query → Fp) :
    (interpolatedX cfg word).eval f
      = Orchard.Ecc.MulFixed.interpolate (readParams cfg f) (word.eval f) := by
  simp only [interpolatedX, windowPow, queryFixed, List.range_succ, List.range_zero,
    List.append_nil, List.nil_append, List.cons_append, List.foldl_cons, List.foldl_nil,
    List.foldl_append, circuit_norm, Orchard.Ecc.MulFixed.interpolate, readParams]

/-- `interpolate` only depends on the params componentwise — the bridge from the
`readParams` cell reads to a known `CoordsParams` value. -/
theorem interpolate_congr_params {p q : CoordsParams Fp}
    (h0 : p.lagrange0 = q.lagrange0) (h1 : p.lagrange1 = q.lagrange1)
    (h2 : p.lagrange2 = q.lagrange2) (h3 : p.lagrange3 = q.lagrange3)
    (h4 : p.lagrange4 = q.lagrange4) (h5 : p.lagrange5 = q.lagrange5)
    (h6 : p.lagrange6 = q.lagrange6) (h7 : p.lagrange7 = q.lagrange7) (w : Fp) :
    Orchard.Ecc.MulFixed.interpolate p w = Orchard.Ecc.MulFixed.interpolate q w := by
  unfold Orchard.Ecc.MulFixed.interpolate
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

/-- Rust `mul_fixed::Config::configure` (`mul_fixed.rs:54-104`): equality on `window` and
`u`, a fresh selector for the running-sum config (whose `configure` registers the "range
check" gate and re-enables equality on `window` — a dedup no-op, as in Rust), a fresh
`fixed_z` column, then the coords gate on the same selector. The cross-config column
identities Rust asserts (`add.x_p = add_incomplete.x_p` etc., lines 81-99) hold by
construction at the call site (`EccChip::configure` hands both configs the same
columns). -/
def configure (lagrangeCoeffs : Fin 8 → Column .fixed) (window u : Column .advice)
    (addConfig : Add.Config) (addIncompleteConfig : AddIncomplete.Config) :
    Configure Fp Config := do
  enableEquality window
  enableEquality u
  let qRunningSum ← selector
  let runningSumConfig ← DecomposeRunningSum.configure 3 qRunningSum window
  let fixedZ ← fixedColumn
  let cfg : Config :=
    { runningSumConfig, lagrangeCoeffs, fixedZ, window, u, addConfig, addIncompleteConfig }
  createGate (coordsGate cfg)
  return cfg

/-! ## Region-relative synthesize pieces (`assign_region_inner`, `mul_fixed.rs:171-405`)

All pieces are offset-generic `RegionCircuit`s; the wrapper bundles compose them inside
one region. The fixed-base data comes from the donor `FixedBase` (its `params w` are the
window-`w` fixed-column values; `windowPoint`/`u` feed the witness programs). -/

/-- The `k = ⌊α/8^w⌋ mod 8` window value of the scalar cell, inside a witness closure. -/
def windowVal (env : Placed ProverEnvironment Fp) (alpha : AssignedCell Fp) (w : ℕ) : ℕ :=
  (readCell env alpha).val / 8 ^ w % 8

/-- Witness program for `x_p` of window `w`: the window-table point's x-coordinate at the
scalar's window value (`process_window`, `mul_fixed.rs:268-283`). The 8 candidate
coordinates are precomputed per window (Rust precomputes the whole window table). -/
def xPWit (B : FixedBaseData) (alpha : AssignedCell Fp) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => (windowPoint B.point w k.val).x)[windowVal env alpha w]!)]

/-- Witness program for `y_p` of window `w` (`mul_fixed.rs:285-295`). -/
def yPWit (B : FixedBaseData) (alpha : AssignedCell Fp) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => (windowPoint B.point w k.val).y)[windowVal env alpha w]!)]

/-- Witness program for `u` of window `w`: `u² = y_p + z` (`mul_fixed.rs:300-302`). -/
def uWit (B : FixedBaseData) (alpha : AssignedCell Fp) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => B.u w k.val)[windowVal env alpha w]!)]

/-- One window row of `assign_fixed_constants` (`mul_fixed.rs:214-249`): enable the
coords-check toggle gate (Rust's `coords_check_toggle` selector parameter — the coords
gate for the running-sum wrappers, the full-width gate for `full_width`), then the 8
Lagrange coefficients and the `z` value into the fixed columns. -/
def fixedConstantsWindow (toggle : Gate Fp) (B : FixedBaseData) (cfg : Config) (w row : ℕ) :
    RegionCircuit Fp Unit := do
  toggle.enable row
  let p := B.params w
  let _ ← assignFixed (cfg.lagrangeCoeffs 0) row p.lagrange0
  let _ ← assignFixed (cfg.lagrangeCoeffs 1) row p.lagrange1
  let _ ← assignFixed (cfg.lagrangeCoeffs 2) row p.lagrange2
  let _ ← assignFixed (cfg.lagrangeCoeffs 3) row p.lagrange3
  let _ ← assignFixed (cfg.lagrangeCoeffs 4) row p.lagrange4
  let _ ← assignFixed (cfg.lagrangeCoeffs 5) row p.lagrange5
  let _ ← assignFixed (cfg.lagrangeCoeffs 6) row p.lagrange6
  let _ ← assignFixed (cfg.lagrangeCoeffs 7) row p.lagrange7
  let _ ← assignFixed cfg.fixedZ row p.z
  return ()

/-- `assign_fixed_constants` (`mul_fixed.rs:195-252`): the per-window fixed columns and
coords-toggle enables, one row per window, before any advice assignment. -/
def fixedConstantsLoop (toggle : Gate Fp) (B : FixedBaseData) (cfg : Config)
    (offset numWindows : ℕ) : RegionCircuit Fp Unit :=
  RegionCircuit.forRange' offset 1 numWindows
    (fun w row => fixedConstantsWindow toggle B cfg w row)

/-- `process_window` (`mul_fixed.rs:254-305`): witness `[window_scalar]B`'s coordinates
into the add config's `x_p`/`y_p` at the window row, and the `u` value. Returns the
window-point cells. -/
def processWindow (B : FixedBaseData) (cfg : Config) (alpha : AssignedCell Fp) (w row : ℕ) :
    RegionCircuit Fp (Point (AssignedCell Fp)) := do
  let x ← assignAdvice cfg.addConfig.xP row (xPWit B alpha w)
  let y ← assignAdvice cfg.addConfig.yP row (yPWit B alpha w)
  let _u ← assignAdvice cfg.u row (uWit B alpha w)
  return { x, y }

/-- The shared window chain of `assign_region_inner` (`mul_fixed.rs:183-192`):
`initialize_accumulator` (window 0), the incomplete-addition loop over windows
`1..numWindows−2` (window 1's accumulator q-copy is REAL — the window-0 point; later
windows' are the Rust "copied into themselves" self-copies of the previous round's
output), and `process_msb` (window `numWindows−1`, no addition). Generic over the
per-window witness function (cell-scalar for the running-sum wrappers, hint-driven for
`full_width`). Returns `(acc, mul_b)`. -/
def windowChain (cfg : Config)
    (processW : ℕ → ℕ → RegionCircuit Fp (Point (AssignedCell Fp)))
    (offset numWindows : ℕ) :
    RegionCircuit Fp (Point (AssignedCell Fp) × Point (AssignedCell Fp)) := do
  let acc0 ← processW 0 offset
  let mulB1 ← processW 1 (offset + 1)
  let _a1 ← AddIncomplete.add.call cfg.addIncompleteConfig (offset + 1) ⟨mulB1, acc0⟩
  RegionCircuit.forRange' (offset + 2) 1 (numWindows - 3) (fun i row => do
    let mulB ← processW (i + 2) row
    let qx ← cellAt cfg.addIncompleteConfig.xQR row
    let qy ← cellAt cfg.addIncompleteConfig.yQR row
    let _ ← AddIncomplete.add.call cfg.addIncompleteConfig row
      ⟨mulB, { x := qx, y := qy }⟩
    return ())
  let mulB ← processW (numWindows - 1) (offset + (numWindows - 1))
  let accX ← cellAt cfg.addIncompleteConfig.xQR (offset + (numWindows - 1))
  let accY ← cellAt cfg.addIncompleteConfig.yQR (offset + (numWindows - 1))
  return ({ x := accX, y := accY }, mulB)

end Halo2.Ironwood.Ecc.MulFixed
