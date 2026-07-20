import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.MulFixed.Theorems
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.AddIncomplete
import Clean.Ironwood.Utilities.DecomposeRunningSum

/-!
The shared core of fixed-base scalar multiplication (`H = 8`, 3-bit windows): `[scalar]B` for a
fixed base `B`, by decomposing the scalar into 3-bit windows. Per window, the window point's `x`
is interpolated by a degree-7 Lagrange polynomial in the window value over 8 fixed columns, its
`y` sign is fixed by `u² = y_p + z`, and the accumulator advances by incomplete addition; the most
significant window uses complete addition. The `full_width` / `short` / `base_field_elem` wrappers
compose this core.

`coords_check` is the per-window-row constraint: the interpolated `x_p`, the `u² = y_p + z` sign
fix, and the curve equation. It is registered on the running sum's own range-check selector, so
enabling a running-sum row fires both the range check and the coordinates check.

Reference: `halo2_gadgets/src/ecc/chip/mul_fixed.rs`.
-/

namespace Halo2.Ironwood.Ecc.MulFixed

open Halo2.Ironwood (Fp)
open Halo2.Ironwood (Point)
open Halo2.Ironwood.Ecc.MulFixed (CoordsParams interpolate FixedBase windowPoint windowScalar)

open Halo2.Ironwood (pallasB)
open Halo2.Ironwood.DecomposeRunningSum (copyDecompose)

/-- The window size, `H = 2^3`. -/
def H : ℕ := 8

/-- The number of windows in a full-width decomposition. -/
def NUM_WINDOWS : ℕ := 85

/-- The fixed-base data a synthesize needs (no invariants): the per-window fixed-column values,
and the window tables feeding the witness programs. `FixedBase` (data + the halo2 out-of-circuit
invariants) lowers to this via `toData`; proof-free consumers (the VK layout tests, which only
need concrete `params` values in the keygen view) construct it directly from dumped tables. -/
structure FixedBaseData where
  -- Per-window Lagrange-coefficient and z fixed-column values.
  params : ℕ → CoordsParams Fp
  -- The base's generator point.
  point : Point Fp
  -- Per-window, per-index u square roots (u² = y_p + z).
  u : ℕ → ℕ → Fp

/-- The data of a proven fixed base. -/
def _root_.Halo2.Ironwood.Ecc.MulFixed.FixedBase.toData (B : FixedBase) : FixedBaseData :=
  { params := B.params, point := B.point, u := B.u }

/-! ## Config -/

structure Config where
  -- The running-sum config for decomposing the scalar into windows.
  runningSumConfig : DecomposeRunningSum.Config
  -- The fixed Lagrange interpolation coefficients for `x_p`.
  lagrangeCoeffs : Fin 8 → Column .fixed
  -- The fixed `z` for each window such that `y + z = u²`.
  fixedZ : Column .fixed
  -- Decomposition of an `n − 1`-bit scalar into `k`-bit windows:
  -- `a = a_0 + 2^k·a_1 + 2^{2k}·a_2 + … + 2^{(n−1)k}·a_{n−1}`.
  window : Column .advice
  -- `u` such that `u² = y_p + z`.
  u : Column .advice
  -- Configuration for `add`.
  addConfig : Add.Config
  -- Configuration for `add_incomplete`.
  addIncompleteConfig : AddIncomplete.Config

/-! ## The "Running sum coordinates check" gate -/

/-- `window_pow[k] = (0..k).fold(Const 1, |acc,_| acc * window)` — the exact Rust AST: `1`,
`1·w`, `(1·w)·w`, …. -/
def windowPow (word : Expression Fp Query) (k : ℕ) : Expression Fp Query :=
  (List.range k).foldl (fun acc _ => acc * word) (Expression.const 1)

/-- The interpolated `x_p`: fold from `Const 0`, `acc + window_pow[k] · lagrange_coeffs[k]` — the
8-iteration fold written out (identical AST; keeps the eval bridge fold-free). -/
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

/-- The shared per-window-row constraint list over a given window-value expression. Reads
`x_p`/`y_p` on the add config's columns at `cur`, `u` at `cur`, `fixed_z` and the 8 Lagrange
columns as rotation-0 fixed queries. Used by BOTH the running-sum coords gate (word = `z_cur −
z_next·8`) and the full-width gate (word = the raw `window` query). -/
def coordsCheck (cfg : Config) (word : Expression Fp Query) :
    List (String × Expression Fp Query) :=
  let yP : Expression Fp Query := queryAdvice cfg.addConfig.yP 0
  let xP : Expression Fp Query := queryAdvice cfg.addConfig.xP 0
  let z : Expression Fp Query := queryFixed cfg.fixedZ
  let u : Expression Fp Query := queryAdvice cfg.u 0
  -- check x: interpolated_x − x_p
  let xCheck := interpolatedX cfg word - xP
  -- check y: u² − y_p − z
  let yCheck := u * u - yP - z
  -- on-curve: y_p² − x_p²·x_p − b
  let onCurve := yP * yP - xP * xP * xP - (pallasB : Expression Fp Query)
  [("check x", xCheck), ("check y", yCheck), ("on-curve", onCurve)]

/-- The "Running sum coordinates check" gate, registered on the running sum's `q_range_check`
selector. The window value is derived: `word = z_cur − z_next·8` (constant scale on the
right). -/
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

/-- `interpolatedX` evaluates to `interpolate` over the read-back params — the bridge from the
gate AST to the coordinate algebra. -/
theorem eval_interpolatedX (cfg : Config) (word : Expression Fp Query) (f : Query → Fp) :
    (interpolatedX cfg word).eval f
      = Halo2.Ironwood.Ecc.MulFixed.interpolate (readParams cfg f) (word.eval f) := by
  simp only [interpolatedX, windowPow, queryFixed, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.foldl_cons, List.foldl_nil,
    circuit_norm, Halo2.Ironwood.Ecc.MulFixed.interpolate, readParams]

/-- `interpolate` only depends on the params componentwise — the bridge from the
`readParams` cell reads to a known `CoordsParams` value. -/
theorem interpolate_congr_params {p q : CoordsParams Fp}
    (h0 : p.lagrange0 = q.lagrange0) (h1 : p.lagrange1 = q.lagrange1)
    (h2 : p.lagrange2 = q.lagrange2) (h3 : p.lagrange3 = q.lagrange3)
    (h4 : p.lagrange4 = q.lagrange4) (h5 : p.lagrange5 = q.lagrange5)
    (h6 : p.lagrange6 = q.lagrange6) (h7 : p.lagrange7 = q.lagrange7) (w : Fp) :
    Halo2.Ironwood.Ecc.MulFixed.interpolate p w = Halo2.Ironwood.Ecc.MulFixed.interpolate q w := by
  unfold Halo2.Ironwood.Ecc.MulFixed.interpolate
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

/-- Equality on `window` and `u`, a fresh selector for the running-sum config (whose `configure`
registers the "range check" gate and re-enables equality on `window` — a dedup no-op), a fresh
`fixed_z` column, then the coords gate on the same selector. The cross-config column identities
Rust asserts (`add.x_p = add_incomplete.x_p` etc.) hold by construction at the call site
(`EccChip::configure` hands both configs the same columns). -/
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

/-! ## Region-relative synthesize pieces

Offset-generic `RegionCircuit`s; the wrapper bundles compose them inside one region. -/

/-- The `k = ⌊α/8^w⌋ mod 8` window value of the scalar cell, inside a witness closure. -/
def windowVal (env : Placed ProverEnvironment Fp) (alpha : AssignedCell Fp) (w : ℕ) : ℕ :=
  (readCell env alpha).val / 8 ^ w % 8

/-- Witness program for `x_p` of window `w`: the window-table point's x-coordinate at the
scalar's window value. The 8 candidate coordinates are precomputed per window (from the base's
own scalar-kind-specific window formula — hence the table parameter `tbl`: `windowPoint point`
for the 85-window kinds, `Short.windowPoint point` for short). -/
def xPWit (tbl : ℕ → ℕ → Point Fp) (alpha : AssignedCell Fp) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => (tbl w k.val).x)[windowVal env alpha w]!)]

/-- Witness program for `y_p` of window `w`. -/
def yPWit (tbl : ℕ → ℕ → Point Fp) (alpha : AssignedCell Fp) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => (tbl w k.val).y)[windowVal env alpha w]!)]

/-- Witness program for `u` of window `w`: `u² = y_p + z`. -/
def uWit (B : FixedBaseData) (alpha : AssignedCell Fp) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => B.u w k.val)[windowVal env alpha w]!)]

/-- One window row: enable the coords-check toggle gate (the coords gate for the running-sum
wrappers, the full-width gate for `full_width`), then the 8 Lagrange coefficients and the `z`
value into the fixed columns. -/
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

/-- The per-window fixed columns and coords-toggle enables, one row per window, before any
advice assignment. -/
def fixedConstantsLoop (toggle : Gate Fp) (B : FixedBaseData) (cfg : Config)
    (offset numWindows : ℕ) : RegionCircuit Fp Unit :=
  RegionCircuit.forRange' offset 1 numWindows
    (fun w row => fixedConstantsWindow toggle B cfg w row)

/-- Witness `[window_scalar]B`'s coordinates into the add config's `x_p`/`y_p` at the window row,
and the `u` value. Returns the window-point cells. -/
def processWindow (B : FixedBaseData) (tbl : ℕ → ℕ → Point Fp) (cfg : Config)
    (alpha : AssignedCell Fp) (w row : ℕ) :
    RegionCircuit Fp (Point (AssignedCell Fp)) := do
  let x ← assignAdvice cfg.addConfig.xP row (xPWit tbl alpha w)
  let y ← assignAdvice cfg.addConfig.yP row (yPWit tbl alpha w)
  let _u ← assignAdvice cfg.u row (uWit B alpha w)
  return { x, y }

/-- The shared window chain: `initialize_accumulator` (window 0), the incomplete-addition loop
over windows `1..numWindows−2` (window 1's accumulator q-copy is REAL — the window-0 point; later
windows' are self-copies of the previous round's output), and `process_msb` (window
`numWindows−1`, no addition). Generic over the per-window witness function (cell-scalar for the
running-sum wrappers, hint-driven for `full_width`). Returns `(acc, mul_b)`. -/
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

/-! ## Shared proof helpers for the wrapper bundles

Context-free value lemmas the sibling proof arcs (`base_field_elem`, `full_width`, `short`) all
consume, kept file-level so in-proof uses run in an empty context (`omega` whnf-scans every
hypothesis). -/

/-- Structure eta for `Point` as an equation. -/
theorem point_eta (P : Point Fp) : ({ x := P.x, y := P.y } : Point Fp) = P := rfl

/-- `OnCurve` of the coords-mk of a point is `OnCurve` of the point (structure eta). -/
theorem point_eta_onCurve {P : Point Fp} (h : P.OnCurve) :
    ({ x := P.x, y := P.y } : Point Fp).OnCurve := h

/-- `partialSum` at 1, unfolded (context-free arithmetic). -/
theorem partialSum_one (ks : ℕ → ℕ) :
    Halo2.Ironwood.Ecc.MulFixed.partialSum ks 1 = ks 0 + 2 + (ks 1 + 2) * 8 ^ 1 := by
  simp [Halo2.Ironwood.Ecc.MulFixed.partialSum]

/-- `partialSum` at a successor (context-free unfold). -/
theorem partialSum_succ (ks : ℕ → ℕ) (n : ℕ) :
    Halo2.Ironwood.Ecc.MulFixed.partialSum ks (n + 1)
      = Halo2.Ironwood.Ecc.MulFixed.partialSum ks n + (ks (n + 1) + 2) * 8 ^ (n + 1) := rfl

/-- Pure-ℕ bounds for the ladder's first addition (windows 0 + 1). -/
theorem base_bounds {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    0 < (a + 2) * 8 ^ 0 ∧ (a + 2) * 8 ^ 0 < (b + 2) * 8 ^ 1 ∧
    (a + 2) * 8 ^ 0 + (b + 2) * 8 ^ 1
      < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
  have hcard : 100 < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
    norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]
  norm_num
  omega

/-- Pure-ℕ bounds for a ladder step. -/
theorem step_bounds {k S j : ℕ} (hk : k < 8) (hS_lt : S < 2 * 8 ^ (j + 1))
    (_hS_pos : 0 < S) (hj : j ≤ 82) :
    0 < (k + 2) * 8 ^ (j + 1) ∧ S < (k + 2) * 8 ^ (j + 1) ∧
    (k + 2) * 8 ^ (j + 1) < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD ∧
    S < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD ∧
    S + (k + 2) * 8 ^ (j + 1) < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
  have hpow : 0 < (8 : ℕ) ^ (j + 1) := pow_pos (by norm_num) _
  have htu : (k + 2) * 8 ^ (j + 1) ≤ 9 * 8 ^ (j + 1) := Nat.mul_le_mul_right _ (by omega)
  have htl : 2 * 8 ^ (j + 1) ≤ (k + 2) * 8 ^ (j + 1) := Nat.mul_le_mul_right _ (by omega)
  have hp83 : (8 : ℕ) ^ (j + 1) ≤ 8 ^ 83 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcard : 11 * 8 ^ 83 < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
    norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]
  refine ⟨by positivity, by omega, by omega, by omega, by omega⟩

/-- `partialSum` only reads windows `0..w`. -/
theorem partialSum_congr {ks ks' : ℕ → ℕ} (w : ℕ) (h : ∀ t ≤ w, ks t = ks' t) :
    Halo2.Ironwood.Ecc.MulFixed.partialSum ks w = Halo2.Ironwood.Ecc.MulFixed.partialSum ks' w := by
  induction w with
  | zero => simp [Halo2.Ironwood.Ecc.MulFixed.partialSum, h 0 (by omega)]
  | succ n ih =>
    simp only [Halo2.Ironwood.Ecc.MulFixed.partialSum]
    rw [ih (fun t ht => h t (by omega)), h (n + 1) le_rfl]

/-- Lower windows' table point as a plain scalar multiple (the `+2`-padded window
scalar; both the 85- and 22-window families share this form below the MSB). -/
theorem windowPoint_lower (point : Point Fp) {w k : ℕ} (hw : w < 84) (hk : k < 8) :
    Halo2.Ironwood.Ecc.MulFixed.windowPoint point w k = (((k + 2) * 8 ^ w : ℕ) • point) := by
  unfold Halo2.Ironwood.Ecc.MulFixed.windowPoint
  rw [Halo2.Ironwood.Ecc.MulFixed.windowScalar_val hw hk]

/-- The shared incomplete-addition ladder, abstract over the base point, window count
and cell reads: window `w < N−1` holds `[(ks w + 2)·8^w]·P` (`hWP`), the entering
accumulator is window 0 (`hAcc0`), and each guarded addition fact (`hStep`, the
post-`subcircuit_rw` shape of an `add_incomplete` chunk) — then the accumulator after
windows `0..j` is `[partialSum ks j]·P`. One induction for every wrapper's soundness
AND completeness ladder (85-window and 22-window families alike); the circuit-fact glue
differs per caller, the value algebra does not. -/
theorem chain_ladder (point : Point Fp) (hP : point.OnCurve)
    (N : ℕ) (hN2 : 2 ≤ N) (hN85 : N ≤ 85)
    (ks : ℕ → ℕ) (hks_lt : ∀ t, ks t < 8)
    (wx wy ax ay : ℕ → Fp)
    (hWP : ∀ w, w < N - 1 →
      wx w = ((((ks w + 2) * 8 ^ w : ℕ)) • point).x ∧
      wy w = ((((ks w + 2) * 8 ^ w : ℕ)) • point).y)
    (hAcc0 : ax 0 = wx 0 ∧ ay 0 = wy 0)
    (hStep : ∀ j, 1 ≤ j → j ≤ N - 2 →
      (({ x := wx j, y := wy j } : Point Fp).OnCurve ∧
        ({ x := ax (j - 1), y := ay (j - 1) } : Point Fp).OnCurve ∧
        wx j ≠ ax (j - 1)) →
      ({ x := ax j, y := ay j } : Point Fp)
        = { x := wx j, y := wy j } + { x := ax (j - 1), y := ay (j - 1) }) :
    ∀ j, j ≤ N - 2 →
      ax j = (Halo2.Ironwood.Ecc.MulFixed.partialSum ks j • point).x ∧
      ay j = (Halo2.Ironwood.Ecc.MulFixed.partialSum ks j • point).y := by
  intro j
  induction j with
  | zero =>
    intro _
    obtain ⟨h0x, h0y⟩ := hWP 0 (by omega)
    rw [show ((ks 0 + 2) * 8 ^ 0 : ℕ) = Halo2.Ironwood.Ecc.MulFixed.partialSum ks 0 from by
      simp [Halo2.Ironwood.Ecc.MulFixed.partialSum]] at h0x h0y
    exact ⟨hAcc0.1.trans h0x, hAcc0.2.trans h0y⟩
  | succ n ih =>
    intro hle
    have hih := ih (by omega)
    obtain ⟨hpx, hpy⟩ := hWP (n + 1) (by omega)
    -- opaque scalars (performance: keep the products off the goal)
    obtain ⟨t, ht_def⟩ : ∃ t : ℕ, t = (ks (n + 1) + 2) * 8 ^ (n + 1) := ⟨_, rfl⟩
    obtain ⟨S, hS_def⟩ : ∃ S : ℕ, S = Halo2.Ironwood.Ecc.MulFixed.partialSum ks n := ⟨_, rfl⟩
    rw [← ht_def] at hpx hpy
    rw [← hS_def] at hih
    have hS_lt : S < 2 * 8 ^ (n + 1) := by
      rw [hS_def]
      exact Halo2.Ironwood.Ecc.MulFixed.partialSum_lt _ n (fun _ _ => hks_lt _)
    have hS_pos : 0 < S := by
      rw [hS_def]; exact Halo2.Ironwood.Ecc.MulFixed.partialSum_pos _ n
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ :=
      step_bounds (hks_lt (n + 1)) hS_lt hS_pos (by omega)
    rw [← ht_def] at hb1 hb2 hb3 hb5
    have hOut := hStep (n + 1) (by omega) (by omega) ⟨by
        rw [hpx, hpy]
        exact point_eta_onCurve (Halo2.Ironwood.Point.nsmul_onCurve hP hb1 hb3),
      by
        rw [show n + 1 - 1 = n from by omega, hih.1, hih.2]
        exact point_eta_onCurve (Halo2.Ironwood.Point.nsmul_onCurve hP hS_pos hb4),
      by
        rw [show n + 1 - 1 = n from by omega, hpx, hih.1]
        exact Halo2.Ironwood.Point.nsmul_x_ne hP hS_pos hb2 (by omega)⟩
    rw [show n + 1 - 1 = n from by omega, hpx, hpy, hih.1, hih.2] at hOut
    rw [point_eta ((t : ℕ) • point), point_eta ((S : ℕ) • point),
      Halo2.Ironwood.Point.nsmul_add_nsmul hP] at hOut
    have hps : t + S = Halo2.Ironwood.Ecc.MulFixed.partialSum ks (n + 1) := by
      rw [ht_def, hS_def, partialSum_succ]
      ring
    rw [hps] at hOut
    exact ⟨congrArg Halo2.Ironwood.Point.x hOut, congrArg Halo2.Ironwood.Point.y hOut⟩

/-- Reduce the witness tables' `getElem!` at the honest window value: index
`windowVal = α.val / 8^w % 8 < 8`, and `8^w = 2^{3w}`. -/
theorem ofFn8_get_windowVal (f : Fin 8 → Fp) (env : Placed ProverEnvironment Fp)
    (alpha : AssignedCell Fp) (w : ℕ) (a : Fp) (ha : readCell env alpha = a) :
    (Vector.ofFn f)[windowVal env alpha w]!
      = f ⟨a.val / 2 ^ (3 * w) % 8, Nat.mod_lt _ (by norm_num)⟩ := by
  have hidx : windowVal env alpha w = a.val / 2 ^ (3 * w) % 8 := by
    unfold windowVal
    rw [ha, pow_mul]
    norm_num
  have hlt : windowVal env alpha w < 8 := by
    rw [hidx]; exact Nat.mod_lt _ (by norm_num)
  rw [getElem!_pos (Vector.ofFn f) (windowVal env alpha w) (by simpa using hlt)]
  rw [Vector.getElem_ofFn]
  congr 1
  exact Fin.ext hidx

/-- The incomplete-addition child's output cells (`rfl`; the hand `add_output_eq`
pattern). -/
theorem addinc_output_cells (cfgI : AddIncomplete.Config) (row : ℕ)
    (input : Var AddIncomplete.Inputs Fp) (self : RegionIndex) :
    AddIncomplete.add.output cfgI row input self
      = { x := AssignedCell.of self (row + 1) cfgI.xQR,
          y := AssignedCell.of self (row + 1) cfgI.yQR } := rfl

end Halo2.Ironwood.Ecc.MulFixed
