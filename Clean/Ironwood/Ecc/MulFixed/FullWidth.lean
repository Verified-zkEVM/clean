import Clean.Ironwood.Ecc.MulFixed
import Clean.Orchard.Ecc.MulFixed.BaseFieldElem

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul_fixed/full_width.rs`
(read in full) — fixed-base scalar multiplication by a full-width scalar.

- `Config` (lines 13-17): the `q_mul_fixed_full` selector and the shared `mul_fixed`
  super config.
- `configure` (lines 19-32) + the "Full-width fixed-base scalar mul" gate (lines 34-51):
  on `q_mul_fixed_full`, the shared `coords_check` over the RAW `window` query (the
  windows are witnessed directly, not derived from a running sum) plus the 3-bit
  "window range check".
- `assign` (lines 115-177), two regions:
  1. "Full-width fixed-base mul (incomplete addition)": `witness` (lines 55-70 →
     `decompose_scalar_fixed`, lines 75-114: enable `q_mul_fixed_full` on all 85 rows,
     witness `k[w]` into the `window` column), then the shared `assign_region_inner`
     with `q_mul_fixed_full` as the coords toggle;
  2. "Full-width fixed-base mul (last window, complete addition)": `add(mul_b, acc)`.

The scalar is prover-side only (`Value<pallas::Scalar>`, witnessed inside — "allowed to
be non-canonical"): per the no-prover-info rule the bundle input is `Unconstrained`
hint data. The hint is the 85 three-bit windows themselves (each fits `Fp`); the
`Fq`-valued scalar has no `Fp`-cell representation, and the nat-valued IR hint
(`UnconstrainedNat`, queued follow-up #32) is not yet ported.

Phase-2 spec note (vs the phase-1 donor `Orchard/Ecc/MulFixed/FullWidth.lean`): the
donor's verifier spec is the existential `∃ s : Fq, output = s • B` — the scalar exists
only as window cells, so input/output soundness can say nothing stronger. The
requirements doc upgrades exactly this family to extractor form
(`Witness := Fq` read off the window cells, `Spec _ output s := output = s • B`);
that lands with this file's proof arc.
-/

-- The variable-name style linter whnf-walks the chunk-typed statements of the proof
-- helpers below and times out; disabled file-wide (as in `BaseFieldElem.lean`).
set_option linter.constructorNameAsVariable false

namespace Halo2.Ironwood.Ecc.MulFixed.FullWidth

open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Ecc.MulFixed
  (coordsCheck fixedConstantsLoop processWindow FixedBaseData)
open Halo2.Ironwood.DecomposeRunningSum (rangeCheckExpr)
open Orchard (Point)
open Orchard.Ecc.MulFixed (FixedBase)

/-- Rust `full_width::Config` (lines 13-17). -/
structure Config where
  qMulFixedFull : Selector
  superConfig : MulFixed.Config

/-- The "Full-width fixed-base scalar mul" gate (lines 34-51): the shared `coords_check`
over the raw `window` query, plus the 3-bit window range check — all on
`q_mul_fixed_full`. -/
def fullWidthGate (cfg : Config) : Gate Fp where
  name := "Full-width fixed-base scalar mul"
  selector := cfg.qMulFixedFull
  constraints :=
    let window : Expression Fp Query := queryAdvice cfg.superConfig.window 0
    Constraints.withSelector cfg.qMulFixedFull
      (coordsCheck cfg.superConfig window
        ++ [("window range check", rangeCheckExpr 8 window)])

/-- Rust `full_width::Config::configure` (lines 19-32). -/
def configure (superConfig : MulFixed.Config) : Configure Fp Config := do
  let qMulFixedFull ← selector
  let cfg : Config := { qMulFixedFull, superConfig }
  createGate (fullWidthGate cfg)
  return cfg

/-- `decompose_scalar_fixed` (lines 75-114): enable `q_mul_fixed_full` on all
`numWindows` rows, then witness the scalar's 3-bit windows `k[w]` into the `window`
column — from the window hints. Returns nothing; the window cells are read positionally
(the coords rows consume them via queries, `process_window` via the hint values). -/
def witnessScalarLoop (cfg : Config) (windows : Vector (FExpr Fp) 85) (offset : ℕ) :
    RegionCircuit Fp Unit := do
  RegionCircuit.forRange' offset 1 85 (fun _ row =>
    (fullWidthGate cfg).enable row)
  RegionCircuit.forRange' offset 1 85 (fun w row => do
    let _k ← assignAdvice cfg.superConfig.window row (.ofFExpr windows[w]!)
    return ())

/-- The full-width `process_window` witness values, driven by the WINDOW HINTS (not a
scalar cell): `x_p`/`y_p`/`u` of window `w` at hint value `k_w`. -/
def hintWindowVal (env : Placed ProverEnvironment Fp) (windows : Vector (FExpr Fp) 85)
    (w : ℕ) : ℕ :=
  (Witgen.FExprOver.eval { env } windows[w]!).val % 8

def xPWitH (B : FixedBaseData) (windows : Vector (FExpr Fp) 85) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => (Orchard.Ecc.MulFixed.windowPoint B.point w k.val).x)[
      hintWindowVal env windows w]!)]

def yPWitH (B : FixedBaseData) (windows : Vector (FExpr Fp) 85) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => (Orchard.Ecc.MulFixed.windowPoint B.point w k.val).y)[
      hintWindowVal env windows w]!)]

def uWitH (B : FixedBaseData) (windows : Vector (FExpr Fp) 85) (w : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[((Vector.ofFn fun k : Fin 8 => B.u w k.val)[hintWindowVal env windows w]!)]

/-- `process_window` over the window hints. -/
def processWindowH (B : FixedBaseData) (cfg : Config) (windows : Vector (FExpr Fp) 85)
    (w row : ℕ) : RegionCircuit Fp (Point (AssignedCell Fp)) := do
  let x ← assignAdvice cfg.superConfig.addConfig.xP row (xPWitH B windows w)
  let y ← assignAdvice cfg.superConfig.addConfig.yP row (yPWitH B windows w)
  let _u ← assignAdvice cfg.superConfig.u row (uWitH B windows w)
  return { x, y }

/-- Output of the inner region: the exit accumulator (windows 0..83) and the MSB window
point. -/
structure InnerOut (F : Type) where
  acc : Point F
  mulB : Point F
deriving ProvableStruct

/-- Region 1, "Full-width fixed-base mul (incomplete addition)" (lines 126-147): witness
the scalar windows, then the shared inner body — fixed constants (toggle =
`q_mul_fixed_full`), window-0 accumulator, the incomplete-addition loop over windows
1..83, the most significant window 84. -/
def innerRegion (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (FExpr Fp) 85) :
    RegionCircuit Fp (InnerOut (AssignedCell Fp)) := do
  -- witness the scalar (lines 132-136)
  witnessScalarLoop cfg windows offset
  -- `assign_fixed_constants` with `q_mul_fixed_full` as the coords toggle (line 143)
  fixedConstantsLoop (fullWidthGate cfg) B cfg.superConfig offset 85
  -- the shared window chain: init (window 0), incomplete additions (1..83), MSB (84)
  let r ← MulFixed.windowChain cfg.superConfig (processWindowH B cfg windows) offset 85
  return { acc := r.1, mulB := r.2 }

/-- Rust `full_width::Config::assign` (lines 115-177): the two regions. Returns the
result point `[scalar]B`. -/
def synthesize (B : FixedBaseData) (cfg : Config) (windows : Vector (FExpr Fp) 85) :
    Circuit Fp (Var Point Fp) := do
  let inn ←
    assignRegion "Full-width fixed-base mul (incomplete addition)"
      (innerRegion B cfg 0 windows)
  assignRegion "Full-width fixed-base mul (last window, complete addition)"
    (Add.add.call cfg.superConfig.addConfig 0 ⟨inn.mulB, inn.acc⟩)

/-! ## The inner-region bundle (proof boundary for region 1)

Extractor-form contracts: the 85 window cells are the designated env readings
(`Witness := fields 85`); the digits are existentially bound in `Spec` (soundness pins
each window cell to a 3-bit value via the gate's range check), and `ProverSpec` exposes
the honest exit values at the witnessed digits. -/

private theorem innerRegion_output_acc (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (FExpr Fp) 85) (self : RegionIndex) :
    ((innerRegion B cfg offset windows).output self).acc
      = { x := AssignedCell.of self (offset + 84) cfg.superConfig.addIncompleteConfig.xQR,
          y := AssignedCell.of self (offset + 84)
            cfg.superConfig.addIncompleteConfig.yQR } := by
  simp only [innerRegion, MulFixed.windowChain, circuit_norm]

private theorem innerRegion_output_mulB (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (FExpr Fp) 85) (self : RegionIndex) :
    ((innerRegion B cfg offset windows).output self).mulB
      = { x := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.xP,
          y := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.yP } := by
  simp only [innerRegion, MulFixed.windowChain, processWindowH, circuit_norm]

/-- The whole inner-region output as a cell literal (structure eta over the
projections). -/
private theorem innerRegion_output (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (FExpr Fp) 85) (self : RegionIndex) :
    (innerRegion B cfg offset windows).output self
      = { acc := { x := AssignedCell.of self (offset + 84)
                     cfg.superConfig.addIncompleteConfig.xQR,
                   y := AssignedCell.of self (offset + 84)
                     cfg.superConfig.addIncompleteConfig.yQR },
          mulB := { x := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.xP,
                    y := AssignedCell.of self (offset + 84)
                      cfg.superConfig.addConfig.yP } } := by
  rw [← innerRegion_output_acc, ← innerRegion_output_mulB]

derive_contract_bridges addinc := Halo2.Ironwood.Ecc.AddIncomplete.add
derive_contract_bridges addc := Halo2.Ironwood.Ecc.Add.add

/-- The shared-config asserts the inner proofs consume (Rust `EccChip` wiring:
`add_incomplete.x_p/y_p` are `add.x_p/y_p`). -/
def InnerEnvAssumptions (cfg : Config) (_ : Placed Environment Fp) : Prop :=
  cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP ∧
  cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP

/-- The window cells (positional; the extraction data). -/
def windowCells (cfg : Config) (offset : ℕ) (self : RegionIndex) :
    Var (fields 85) Fp :=
  Vector.ofFn (fun w : Fin 85 =>
    AssignedCell.of self (offset + w.val) cfg.superConfig.window)

/-- The inner region's output cells, reduced (the explicit `elaborated` output). -/
def innerOutCells (cfg : Config) (offset : ℕ) (self : RegionIndex) :
    Var InnerOut Fp where
  acc := { x := AssignedCell.of self (offset + 84) cfg.superConfig.addIncompleteConfig.xQR,
           y := AssignedCell.of self (offset + 84) cfg.superConfig.addIncompleteConfig.yQR }
  mulB := { x := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.xP,
            y := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.yP }

/-- Soundness contract: each window cell is a 3-bit digit, and the exit cells hold the
windowed ladder values at those digits. -/
def InnerSpec (B : FixedBase) (_ : Value unit Fp) (out : Value InnerOut Fp)
    (ws : Vector Fp 85) : Prop :=
  ∃ ks : ℕ → ℕ, (∀ w, w < 85 → ks w < 8) ∧
    (∀ w : Fin 85, ws[w.val] = ((ks w.val : ℕ) : Fp)) ∧
    out.acc = { x := ((Orchard.Ecc.MulFixed.partialSum ks 83) • B.point).x,
                y := ((Orchard.Ecc.MulFixed.partialSum ks 83) • B.point).y } ∧
    out.mulB = Orchard.Ecc.MulFixed.windowPoint B.point 84 (ks 84)

/-- Honest-prover precondition: the witnessed windows are genuine 3-bit digits (Rust's
`decompose_scalar_fixed` guarantee on the hint programs). -/
def InnerProverAssumptions (_ : ProverValue unit Fp) (ws : Vector Fp 85)
    (_ : ProverHint Fp) : Prop :=
  ∀ w : Fin 85, (ws[w.val]).val < 8

/-- Honest-prover postcondition: the exit cells at the witnessed digits. -/
def InnerProverSpec (B : FixedBase) (_ : ProverValue unit Fp)
    (out : ProverValue InnerOut Fp) (ws : Vector Fp 85) (_ : ProverHint Fp) : Prop :=
  out.acc.x = (Orchard.Ecc.MulFixed.partialSum (fun t => (ws[t]!).val) 83 • B.point).x ∧
  out.acc.y = (Orchard.Ecc.MulFixed.partialSum (fun t => (ws[t]!).val) 83 • B.point).y ∧
  out.mulB.x = (Orchard.Ecc.MulFixed.windowPoint B.point 84 ((ws[84]!).val)).x ∧
  out.mulB.y = (Orchard.Ecc.MulFixed.windowPoint B.point 84 ((ws[84]!).val)).y

/-- The elaborated-metadata instance for the inner region's synthesize lambda, with the
output cells in explicit reduced form (`innerOutCells`) — computing the default output
projection runs the whole region monad (a `List.append` whnf storm). -/
instance innerElab (B : FixedBaseData) (windows : Vector (FExpr Fp) 85)
    (config : Config) (offset : ℕ) :
    ElaboratedRegionCircuit Fp unit InnerOut
      (fun _ : Var unit Fp => innerRegion B config offset windows) where
  output := fun _ self => innerOutCells config offset self
  output_eq := by
    intro _ self
    rw [innerOutCells, innerRegion_output]

/-- Reduce the witness tables' `getElem!` at the hint digit (`hintWindowVal < 8`). -/
private theorem ofFn8_get_hint (f : Fin 8 → Fp) (env : Placed ProverEnvironment Fp)
    (windows : Vector (FExpr Fp) 85) (w : ℕ) :
    (Vector.ofFn f)[hintWindowVal env windows w]!
      = f ⟨hintWindowVal env windows w, Nat.mod_lt _ (by norm_num)⟩ := by
  have hlt : hintWindowVal env windows w < 8 := Nat.mod_lt _ (by norm_num)
  rw [getElem!_pos (Vector.ofFn f) (hintWindowVal env windows w) (by simpa using hlt)]
  rw [Vector.getElem_ofFn]

set_option linter.all false in
/-- The honest per-window point values: the chain's witness programs put the
window-table coordinates and `u` values at each window row, at the HINT digits. -/
private theorem fw_windows_honest (B : FixedBase) (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (windows : Vector (FExpr Fp) 85)
    (hWchain : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.windowChain cfg.superConfig (processWindowH B.toData cfg windows) offset
        85).operations self)) :
    ∀ w : Fin 85,
      env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Orchard.Ecc.MulFixed.windowPoint B.point w.val
            (hintWindowVal env windows w.val)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Orchard.Ecc.MulFixed.windowPoint B.point w.val
            (hintWindowVal env windows w.val)).y ∧
      env.env.advice cfg.superConfig.u
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = B.u w.val (hintWindowVal env windows w.val) := by
  simp only [MulFixed.windowChain, processWindowH, circuit_norm, mul_one,
    xPWitH, yPWitH, uWitH] at hWchain
  obtain ⟨hx0, hy0, hu0, hx1, hy1, hu1, _hAW1, hLoopW, hx84, hy84, hu84⟩ := hWchain
  intro w
  rcases w with ⟨wv, hwv⟩
  simp only []
  rcases Nat.eq_zero_or_pos wv with rfl | hpos
  · rw [show offset + 0 = offset from by omega]
    rw [hx0, hy0, hu0, ofFn8_get_hint _ env windows 0, ofFn8_get_hint _ env windows 0,
      ofFn8_get_hint _ env windows 0]
    exact ⟨rfl, rfl, rfl⟩
  rcases Nat.lt_or_ge wv 2 with h1 | h2
  · rw [show wv = 1 from by omega]
    rw [hx1, hy1, hu1, ofFn8_get_hint _ env windows 1, ofFn8_get_hint _ env windows 1,
      ofFn8_get_hint _ env windows 1]
    exact ⟨rfl, rfl, rfl⟩
  rcases Nat.lt_or_ge wv 84 with h84 | h84
  · obtain ⟨hxw, hyw, huw, -⟩ := hLoopW ⟨wv - 2, by omega⟩
    rw [show offset + 2 + (wv - 2) = offset + wv from by omega,
      show wv - 2 + 2 = wv from by omega] at hxw hyw huw
    rw [hxw, hyw, huw, ofFn8_get_hint _ env windows wv, ofFn8_get_hint _ env windows wv,
      ofFn8_get_hint _ env windows wv]
    exact ⟨rfl, rfl, rfl⟩
  · rw [show wv = 84 from by omega]
    rw [hx84, hy84, hu84, ofFn8_get_hint _ env windows 84,
      ofFn8_get_hint _ env windows 84, ofFn8_get_hint _ env windows 84]
    exact ⟨rfl, rfl, rfl⟩

set_option linter.all false in
/-- Completeness of the window chain (standalone): the incomplete additions' constraints
from their completeness leaves on the honest ladder, plus the honest exit values. -/
private theorem fw_completeness_chain (B : FixedBase) (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (windows : Vector (FExpr Fp) 85)
    (hWchain : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.windowChain cfg.superConfig (processWindowH B.toData cfg windows) offset
        85).operations self))
    (hXPeq : cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP)
    (hYPeq : cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((MulFixed.windowChain cfg.superConfig (processWindowH B.toData cfg windows) offset
        85).operations self) ∧
    (env.env.advice cfg.superConfig.addIncompleteConfig.xQR
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Orchard.Ecc.MulFixed.partialSum (fun t => hintWindowVal env windows t) 83
          • B.point).x ∧
     env.env.advice cfg.superConfig.addIncompleteConfig.yQR
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Orchard.Ecc.MulFixed.partialSum (fun t => hintWindowVal env windows t) 83
          • B.point).y ∧
     env.env.advice cfg.superConfig.addConfig.xP
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Orchard.Ecc.MulFixed.windowPoint B.point 84 (hintWindowVal env windows 84)).x ∧
     env.env.advice cfg.superConfig.addConfig.yP
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Orchard.Ecc.MulFixed.windowPoint B.point 84 (hintWindowVal env windows 84)).y) := by
  have hPW := fw_windows_honest B cfg offset self env windows hWchain
  have hks_lt : ∀ t, hintWindowVal env windows t < 8 :=
    fun t => Nat.mod_lt _ (by norm_num)
  -- the addinc chunk witnesses
  simp only [MulFixed.windowChain, processWindowH, circuit_norm, mul_one] at hWchain
  obtain ⟨-, -, -, -, -, -, hAW1, hLoopW, -, -, -⟩ := hWchain
  -- per-chunk derived statements (Spec under Assumptions)
  have hD1 := Halo2.SubcircuitRw.region_completeness_derived_placed
    AddIncomplete.add cfg.superConfig.addIncompleteConfig (offset + 1) self env
    ⟨⟨AssignedCell.of self (offset + 1) cfg.superConfig.addConfig.xP,
      AssignedCell.of self (offset + 1) cfg.superConfig.addConfig.yP⟩,
     ⟨AssignedCell.of self offset cfg.superConfig.addConfig.xP,
      AssignedCell.of self offset cfg.superConfig.addConfig.yP⟩⟩ hAW1
  simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
    addinc_proverAssumptions_eq, MulFixed.addinc_output_cells, circuit_norm] at hD1
  have hLoopD := fun (i : Fin 82) => by
    have h := Halo2.SubcircuitRw.region_completeness_derived_placed
      AddIncomplete.add cfg.superConfig.addIncompleteConfig (offset + 2 + i.val) self env
      ⟨⟨AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addConfig.xP,
        AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addConfig.yP⟩,
       ⟨AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addIncompleteConfig.xQR,
        AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addIncompleteConfig.yQR⟩⟩
      ((hLoopW i).2.2.2)
    simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
      addinc_proverAssumptions_eq, MulFixed.addinc_output_cells, circuit_norm] at h
    exact h
  -- the honest ladder (shared)
  have hLadder := MulFixed.chain_ladder B.point B.onCurve 85 (by norm_num)
    (by norm_num) (fun t => hintWindowVal env windows t) hks_lt
    (fun w => env.env.advice cfg.superConfig.addConfig.xP
      ((env.place self + (offset + w) : ℕ) : ℤ))
    (fun w => env.env.advice cfg.superConfig.addConfig.yP
      ((env.place self + (offset + w) : ℕ) : ℤ))
    (fun j => if j = 0 then
        env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + offset : ℕ) : ℤ)
      else
        env.env.advice cfg.superConfig.addIncompleteConfig.xQR
          ((env.place self + (offset + j + 1) : ℕ) : ℤ))
    (fun j => if j = 0 then
        env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + offset : ℕ) : ℤ)
      else
        env.env.advice cfg.superConfig.addIncompleteConfig.yQR
          ((env.place self + (offset + j + 1) : ℕ) : ℤ))
    (fun w hw => by
      obtain ⟨hx, hy, -⟩ := hPW ⟨w, by omega⟩
      rw [MulFixed.windowPoint_lower B.point (by omega) (hks_lt _)] at hx hy
      exact ⟨hx, hy⟩)
    ⟨if_pos rfl, if_pos rfl⟩
    (by
      intro j hj1 hj83 hass
      obtain ⟨hOnP, hOnQ, hne⟩ := hass
      dsimp only at hOnP hOnQ hne ⊢
      rw [if_neg (by omega : ¬j = 0), if_neg (by omega : ¬j = 0)]
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · have hj : j = 1 := by omega
        subst hj
        obtain ⟨⟨-, hOut⟩, -⟩ := hD1 ⟨hOnP, hOnQ, hne⟩
        exact hOut
      · have h := hLoopD ⟨j - 2, by omega⟩
        rw [show offset + 2 + (j - 2) = offset + j from by omega] at h
        rw [if_neg (by omega : ¬j - 1 = 0), if_neg (by omega : ¬j - 1 = 0),
          show offset + (j - 1) + 1 = offset + j from by omega] at hOnQ
        rw [if_neg (by omega : ¬j - 1 = 0),
          show offset + (j - 1) + 1 = offset + j from by omega] at hne
        rw [if_neg (by omega : ¬j - 1 = 0), if_neg (by omega : ¬j - 1 = 0),
          show offset + (j - 1) + 1 = offset + j from by omega]
        obtain ⟨⟨-, hOut⟩, -⟩ := h ⟨hOnP, hOnQ, hne⟩
        exact hOut)
  have hInv : ∀ j : ℕ, 1 ≤ j → j ≤ 83 →
      env.env.advice cfg.superConfig.addIncompleteConfig.xQR
          ((env.place self + (offset + j + 1) : ℕ) : ℤ)
        = (Orchard.Ecc.MulFixed.partialSum (fun t => hintWindowVal env windows t) j
            • B.point).x ∧
      env.env.advice cfg.superConfig.addIncompleteConfig.yQR
          ((env.place self + (offset + j + 1) : ℕ) : ℤ)
        = (Orchard.Ecc.MulFixed.partialSum (fun t => hintWindowVal env windows t) j
            • B.point).y := by
    intro j hj1 hj83
    have h := hLadder j hj83
    dsimp only at h
    rw [if_neg (by omega : ¬j = 0), if_neg (by omega : ¬j = 0)] at h
    exact h
  have hHonest : env.env.advice cfg.superConfig.addIncompleteConfig.xQR
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Orchard.Ecc.MulFixed.partialSum (fun t => hintWindowVal env windows t) 83
          • B.point).x ∧
      env.env.advice cfg.superConfig.addIncompleteConfig.yQR
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Orchard.Ecc.MulFixed.partialSum (fun t => hintWindowVal env windows t) 83
          • B.point).y ∧
      env.env.advice cfg.superConfig.addConfig.xP
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Orchard.Ecc.MulFixed.windowPoint B.point 84 (hintWindowVal env windows 84)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Orchard.Ecc.MulFixed.windowPoint B.point 84 (hintWindowVal env windows 84)).y := by
    have h83 := hInv 83 (by norm_num) le_rfl
    rw [show offset + 83 + 1 = offset + 84 from by omega] at h83
    obtain ⟨hx84', hy84', -⟩ := hPW ⟨84, by norm_num⟩
    rw [show ((⟨84, by norm_num⟩ : Fin 85) : ℕ) = 84 from rfl] at hx84' hy84'
    exact ⟨h83.1, h83.2, hx84', hy84'⟩
  refine And.intro ?_ hHonest
  simp only [MulFixed.windowChain, processWindowH, circuit_norm, mul_one]
  have hC1 := Halo2.SubcircuitRw.region_completeness_leaf_placed
    AddIncomplete.add cfg.superConfig.addIncompleteConfig (offset + 1) self env
    ⟨⟨AssignedCell.of self (offset + 1) cfg.superConfig.addConfig.xP,
      AssignedCell.of self (offset + 1) cfg.superConfig.addConfig.yP⟩,
     ⟨AssignedCell.of self offset cfg.superConfig.addConfig.xP,
      AssignedCell.of self offset cfg.superConfig.addConfig.yP⟩⟩ hAW1
  simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
    addinc_proverAssumptions_eq, MulFixed.addinc_output_cells, circuit_norm] at hC1
  constructor
  · -- first addition: window-1 point + window-0 point, honest values
    obtain ⟨hp1x, hp1y, -⟩ := hPW ⟨1, by norm_num⟩
    obtain ⟨hp0x, hp0y, -⟩ := hPW ⟨0, by norm_num⟩
    rw [show ((⟨1, by norm_num⟩ : Fin 85) : ℕ) = 1 from rfl] at hp1x hp1y
    rw [show ((⟨0, by norm_num⟩ : Fin 85) : ℕ) = 0 from rfl,
      show offset + 0 = offset from by omega] at hp0x hp0y
    obtain ⟨t1, ht1_def⟩ : ∃ t : ℕ, t = (Orchard.Ecc.MulFixed.windowScalar 1
      (hintWindowVal env windows 1)).val := ⟨_, rfl⟩
    obtain ⟨s0, hs0_def⟩ : ∃ t : ℕ, t = (Orchard.Ecc.MulFixed.windowScalar 0
      (hintWindowVal env windows 0)).val := ⟨_, rfl⟩
    have ht1 : t1 = (hintWindowVal env windows 1 + 2) * 8 ^ 1 := by
      rw [ht1_def]
      exact Orchard.Ecc.MulFixed.windowScalar_val (by norm_num) (hks_lt 1)
    have hs0 : s0 = (hintWindowVal env windows 0 + 2) * 8 ^ 0 := by
      rw [hs0_def]
      exact Orchard.Ecc.MulFixed.windowScalar_val (by norm_num) (hks_lt 0)
    have hwp1 : Orchard.Ecc.MulFixed.windowPoint B.point 1
        (hintWindowVal env windows 1) = t1 • B.point := by rw [ht1_def]; rfl
    have hwp0 : Orchard.Ecc.MulFixed.windowPoint B.point 0
        (hintWindowVal env windows 0) = s0 • B.point := by rw [hs0_def]; rfl
    rw [hwp1] at hp1x hp1y
    rw [hwp0] at hp0x hp0y
    obtain ⟨hbb1, hbb2, hbb3⟩ := MulFixed.base_bounds (hks_lt 0) (hks_lt 1)
    rw [← hs0] at hbb1 hbb2 hbb3
    rw [← ht1] at hbb2 hbb3
    exact hC1 ⟨by
        rw [hp1x, hp1y]
        exact MulFixed.point_eta_onCurve
          (by rw [← hwp1]; exact B.windowPoint_onCurve (hks_lt 1)),
      by
        rw [hp0x, hp0y]
        exact MulFixed.point_eta_onCurve
          (by rw [← hwp0]; exact B.windowPoint_onCurve (hks_lt 0)),
      by
        rw [hp1x, hp0x]
        exact B.nsmul_x_ne hbb1 hbb2 hbb3⟩
  · -- loop chunk i: window-(i+2) point + honest accumulator [partialSum (i+1)]·B
    intro i
    have hC := Halo2.SubcircuitRw.region_completeness_leaf_placed
      AddIncomplete.add cfg.superConfig.addIncompleteConfig (offset + 2 + i.val) self env
      ⟨⟨AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addConfig.xP,
        AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addConfig.yP⟩,
       ⟨AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addIncompleteConfig.xQR,
        AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addIncompleteConfig.yQR⟩⟩
      ((hLoopW i).2.2.2)
    simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
      addinc_proverAssumptions_eq, MulFixed.addinc_output_cells, circuit_norm] at hC
    obtain ⟨hpx, hpy, -⟩ := hPW ⟨i.val + 2, by omega⟩
    rw [show ((⟨i.val + 2, by omega⟩ : Fin 85) : ℕ) = i.val + 2 from rfl,
      show offset + (i.val + 2) = offset + 2 + i.val from by omega] at hpx hpy
    have hih := hInv (i.val + 1) (by omega) (by omega)
    rw [show offset + (i.val + 1) + 1 = offset + 2 + i.val from by omega] at hih
    obtain ⟨t, ht_def⟩ : ∃ t : ℕ,
        t = (Orchard.Ecc.MulFixed.windowScalar (i.val + 2)
          (hintWindowVal env windows (i.val + 2))).val := ⟨_, rfl⟩
    obtain ⟨S, hS_def⟩ : ∃ S : ℕ,
        S = Orchard.Ecc.MulFixed.partialSum
          (fun t => hintWindowVal env windows t) (i.val + 1) := ⟨_, rfl⟩
    have hval : t = (hintWindowVal env windows (i.val + 2) + 2) * 8 ^ (i.val + 2) := by
      rw [ht_def]
      exact Orchard.Ecc.MulFixed.windowScalar_val (by omega) (hks_lt _)
    have hwp : Orchard.Ecc.MulFixed.windowPoint B.point (i.val + 2)
        (hintWindowVal env windows (i.val + 2)) = t • B.point := by
      rw [ht_def]; rfl
    rw [hwp] at hpx hpy
    rw [← hS_def] at hih
    have hS_lt : S < 2 * 8 ^ (i.val + 2) := by
      rw [hS_def]
      exact Orchard.Ecc.MulFixed.partialSum_lt _ _ (fun _ _ => hks_lt _)
    have hS_pos : 0 < S := by
      rw [hS_def]; exact Orchard.Ecc.MulFixed.partialSum_pos _ _
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ :=
      MulFixed.step_bounds (hks_lt (i.val + 2)) hS_lt hS_pos (by omega)
    rw [← hval] at hb1 hb2 hb3 hb5
    exact hC ⟨by
        rw [hpx, hpy]
        exact MulFixed.point_eta_onCurve (B.nsmul_onCurve hb1 hb3),
      by
        rw [hih.1, hih.2]
        exact MulFixed.point_eta_onCurve (B.nsmul_onCurve hS_pos hb4),
      by
        rw [hpx, hih.1]
        exact B.nsmul_x_ne hS_pos hb2 (by omega)⟩

set_option linter.all false in
/-- Completeness of the gate/fixed rows (standalone): the fixed-cell witness equations
pin the Lagrange columns, and the gate holds at the honest window digits — for BOTH
enable sites (the witness loop and the fixed-constants loop share the same per-row gate
equations; the latter's are proven and the former's extracted). Needs the window cells
pinned to the hint digits (`hWin` — the honest-prover `< 8` guarantee, threaded from
`ProverAssumptions`). -/
private theorem fw_completeness_fixed (B : FixedBase) (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (windows : Vector (FExpr Fp) 85)
    (hWfix : RegionOperations.ExtendsWitnesses env.place self env.env
      ((fixedConstantsLoop (fullWidthGate cfg) B.toData cfg.superConfig offset
        85).operations self))
    (hWchain : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.windowChain cfg.superConfig (processWindowH B.toData cfg windows) offset
        85).operations self))
    (hWin : ∀ w : Fin 85, env.env.advice cfg.superConfig.window
        ((env.place self + (offset + w.val) : ℕ) : ℤ)
      = ((hintWindowVal env windows w.val : ℕ) : Fp)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((witnessScalarLoop cfg windows offset).operations self) ∧
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((fixedConstantsLoop (fullWidthGate cfg) B.toData cfg.superConfig offset
        85).operations self) := by
  have hPW := fw_windows_honest B cfg offset self env windows hWchain
  simp only [MulFixed.fixedConstantsLoop, MulFixed.fixedConstantsWindow, circuit_norm,
    mul_one] at hWfix
  constructor
  · -- the witness loop's 85 gate enables
    simp only [witnessScalarLoop, fullWidthGate, MulFixed.coordsCheck,
      MulFixed.eval_interpolatedX,
      Halo2.Ironwood.DecomposeRunningSum.eval_rangeCheckExpr,
      circuit_norm, mul_one, one_mul]
    intro i
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hZf⟩ := hWfix i
    simp only [show B.toData.params = B.params from rfl] at hL0 hL1 hL2 hL3 hL4 hL5
    simp only [show B.toData.params = B.params from rfl] at hL6 hL7 hZf
    obtain ⟨hpx, hpy, hpu⟩ := hPW i
    have hdig : hintWindowVal env windows i.val < 8 := Nat.mod_lt _ (by norm_num)
    have hxi : (Orchard.Ecc.MulFixed.windowPoint B.point i.val
          (hintWindowVal env windows i.val)).x
        = Orchard.Ecc.MulFixed.interpolate (B.params i.val)
            ((hintWindowVal env windows i.val : ℕ) : Fp) :=
      (B.interpolate_eq i.val i.isLt _ hdig).symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- check x
      rw [hWin i, hpx, hxi, sub_eq_zero]
      symm
      apply MulFixed.interpolate_congr_params <;>
        simp only [MulFixed.readParams, circuit_norm, add_zero] <;>
        first
        | exact hL0.symm | exact hL1.symm | exact hL2.symm | exact hL3.symm
        | exact hL4.symm | exact hL5.symm | exact hL6.symm | exact hL7.symm
    · -- check y (u² = y_p + z)
      rw [hpu, hpy, hZf]
      have huu := B.u_mul_u i.val i.isLt _ hdig
      linear_combination huu
    · -- on-curve
      rw [hpx, hpy]
      have hoc := B.windowPoint_onCurve (w := i.val) hdig
      unfold Orchard.Point.OnCurve at hoc
      linear_combination hoc
    · -- window range check
      rw [hWin i]
      exact (Orchard.Utilities.RunningSum.rangeCheckPoly_eq_zero_iff 8 _).mpr
        ((Halo2.Ironwood.DecomposeRunningSum.inRange_iff_exists_lt 8 (by norm_num) _).mpr
          ⟨hintWindowVal env windows i.val, hdig, rfl⟩)
  · -- the fixed-constants loop: the same gate equations + the fixed-cell clauses
    simp only [MulFixed.fixedConstantsLoop, MulFixed.fixedConstantsWindow,
      fullWidthGate, MulFixed.coordsCheck, MulFixed.eval_interpolatedX,
      Halo2.Ironwood.DecomposeRunningSum.eval_rangeCheckExpr,
      circuit_norm, mul_one, one_mul]
    intro i
    obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hZf⟩ := hWfix i
    simp only [show B.toData.params = B.params from rfl] at hL0 hL1 hL2 hL3 hL4 hL5
    simp only [show B.toData.params = B.params from rfl] at hL6 hL7 hZf
    obtain ⟨hpx, hpy, hpu⟩ := hPW i
    have hdig : hintWindowVal env windows i.val < 8 := Nat.mod_lt _ (by norm_num)
    have hxi : (Orchard.Ecc.MulFixed.windowPoint B.point i.val
          (hintWindowVal env windows i.val)).x
        = Orchard.Ecc.MulFixed.interpolate (B.params i.val)
            ((hintWindowVal env windows i.val : ℕ) : Fp) :=
      (B.interpolate_eq i.val i.isLt _ hdig).symm
    refine ⟨⟨?_, ?_, ?_, ?_⟩, hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hZf⟩
    · -- check x
      rw [hWin i, hpx, hxi, sub_eq_zero]
      symm
      apply MulFixed.interpolate_congr_params <;>
        simp only [MulFixed.readParams, circuit_norm, add_zero] <;>
        first
        | exact hL0.symm | exact hL1.symm | exact hL2.symm | exact hL3.symm
        | exact hL4.symm | exact hL5.symm | exact hL6.symm | exact hL7.symm
    · -- check y (u² = y_p + z)
      rw [hpu, hpy, hZf]
      have huu := B.u_mul_u i.val i.isLt _ hdig
      linear_combination huu
    · -- on-curve
      rw [hpx, hpy]
      have hoc := B.windowPoint_onCurve (w := i.val) hdig
      unfold Orchard.Point.OnCurve at hoc
      linear_combination hoc
    · -- window range check
      rw [hWin i]
      exact (Orchard.Utilities.RunningSum.rangeCheckPoly_eq_zero_iff 8 _).mpr
        ((Halo2.Ironwood.DecomposeRunningSum.inRange_iff_exists_lt 8 (by norm_num) _).mpr
          ⟨hintWindowVal env windows i.val, hdig, rfl⟩)

/-- The elaborated output projection, reduced (`rfl` via `innerElab`). -/
private theorem innerElab_output (B : FixedBaseData) (windows : Vector (FExpr Fp) 85)
    (config : Config) (offset : ℕ) (input : Var unit Fp) (self : RegionIndex) :
    ElaboratedRegionCircuit.output
        (fun _ : Var unit Fp => innerRegion B config offset windows) input self
      = innerOutCells config offset self := rfl

set_option linter.all false in
/-- The inner region's soundness, standalone (own declaration budget). -/
private theorem fw_inner_soundness (B : FixedBase) (windows : Vector (FExpr Fp) 85)
    (cfg : Config) (offset : ℕ) :
    FormalRegionCircuit.Soundness (Input := unit) (Output := InnerOut)
      (fun _ : Var unit Fp => innerRegion B.toData cfg offset windows)
      (fun _ self env => eval env (windowCells cfg offset self))
      (InnerEnvAssumptions cfg) (fun _ => True) (InnerSpec B) := by
  -- the Mul.lean recipe: contract defs only in the list, targeted peels after
  circuit_proof_start [InnerSpec, InnerEnvAssumptions, InnerProverAssumptions]
  obtain ⟨env, rfl, rfl⟩ :
      ∃ pe : Placed Environment Fp, pe.place = place ∧ pe.env = env :=
    ⟨⟨place, env⟩, rfl, rfl⟩
  simp only [innerRegion, RegionCircuit.operations_bind,
    RegionOperations.constraints_append] at hc
  obtain ⟨-, hFixed, hChain, -⟩ := hc
  rw [ElaboratedRegionCircuit.output_eq, innerRegion_output] at h_output
  provable_type_simp
  obtain ⟨⟨hOax, hOay⟩, hOmx, hOmy⟩ := h_output
  obtain ⟨hXPeq, hYPeq⟩ := _hE
  -- ── the per-row gate + Lagrange-fixed rows ──
  simp only [MulFixed.fixedConstantsLoop, MulFixed.fixedConstantsWindow,
    fullWidthGate, MulFixed.coordsCheck, MulFixed.eval_interpolatedX,
    Halo2.Ironwood.DecomposeRunningSum.eval_rangeCheckExpr,
    circuit_norm, mul_one, one_mul] at hFixed
  -- ── the 3-bit digits, from the per-row window range checks ──
  have hdig : ∀ w : Fin 85, ∃ k : ℕ, k < 8 ∧
      env.env.advice cfg.superConfig.window
        ((env.place self + (offset + w.val) : ℕ) : ℤ) = ((k : ℕ) : Fp) := by
    intro w
    obtain ⟨⟨-, -, -, hRange⟩, -⟩ := hFixed w
    exact (Halo2.Ironwood.DecomposeRunningSum.inRange_iff_exists_lt 8 (by norm_num) _).mp
      ((Orchard.Utilities.RunningSum.rangeCheckPoly_eq_zero_iff 8 _).mp hRange)
  choose kf hkf_lt hkf_eq using hdig
  obtain ⟨ks, hks_def⟩ : ∃ ks : ℕ → ℕ,
      ks = fun t => if h : t < 85 then kf ⟨t, h⟩ else 0 := ⟨_, rfl⟩
  have hks_lt : ∀ t, ks t < 8 := by
    intro t
    rw [hks_def]
    dsimp only
    split
    · exact hkf_lt _
    · norm_num
  have hkeq : ∀ w : Fin 85, env.env.advice cfg.superConfig.window
      ((env.place self + (offset + w.val) : ℕ) : ℤ) = ((ks w.val : ℕ) : Fp) := by
    intro w
    rw [hks_def]
    dsimp only
    rw [dif_pos w.isLt]
    exact hkf_eq w
  -- ── the per-row window points (the coords rows) ──
  have hWP : ∀ w : Fin 85,
      env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Orchard.Ecc.MulFixed.windowPoint B.point w.val (ks w.val)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Orchard.Ecc.MulFixed.windowPoint B.point w.val (ks w.val)).y := by
    intro w
    have hRow := hFixed w
    obtain ⟨⟨hIx, hUy, hCrv, -⟩, hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hZf⟩ := hRow
    simp only [show B.toData.params = B.params from rfl]
      at hL0 hL1 hL2 hL3 hL4 hL5 hL6 hL7 hZf
    rw [hkeq w] at hIx
    have hxP : env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = Orchard.Ecc.MulFixed.interpolate (B.params w.val)
            ((ks w.val : ℕ) : Fp) := by
      rw [← sub_eq_zero.mp hIx]
      apply MulFixed.interpolate_congr_params <;>
        simp only [MulFixed.readParams, circuit_norm, add_zero] <;>
        first
        | exact hL0 | exact hL1 | exact hL2 | exact hL3
        | exact hL4 | exact hL5 | exact hL6 | exact hL7
    have hspec : Orchard.Ecc.MulFixed.Coords.Spec (B.params w.val)
        { window := ((ks w.val : ℕ) : Fp),
          xP := env.env.advice cfg.superConfig.addConfig.xP
            ((env.place self + (offset + w.val) : ℕ) : ℤ),
          yP := env.env.advice cfg.superConfig.addConfig.yP
            ((env.place self + (offset + w.val) : ℕ) : ℤ),
          u := env.env.advice cfg.superConfig.u
            ((env.place self + (offset + w.val) : ℕ) : ℤ) } := by
      refine ⟨hxP, ?_, ?_⟩
      · rw [← hZf]; linear_combination hUy
      · linear_combination hCrv
    have hcw := B.coords_eq_windowPoint (w := w.val) (k := ks w.val)
      (by omega) (hks_lt _) rfl hspec
    dsimp only at hcw
    exact hcw
  refine ⟨ks, fun w _ => hks_lt w, ?_, ?_, ?_⟩
  · -- the window cells hold the digits
    intro w
    simp only [windowCells, circuit_norm, Vector.getElem_ofFn, AssignedCell.eval,
      AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
      Environment.get_advice]
    exact hkeq w
  · -- acc = [partialSum ks 83]·B  (the window-chain ladder)
    simp only [MulFixed.windowChain, processWindowH, circuit_norm,
      RegionCircuit.operations_bind, RegionOperations.constraints_append] at hChain
    obtain ⟨hA1, hALoop⟩ := hChain
    subcircuit_rw at hA1
    simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
      MulFixed.addinc_output_cells, circuit_norm] at hA1
    have hLoopS := fun (i : Fin 82) => by
      have h := hALoop i
      subcircuit_rw at h
      simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
        MulFixed.addinc_output_cells, circuit_norm, mul_one] at h
      exact h
    clear hALoop
    -- ── the shared ladder, at this region's reads ──
    have hLadder := MulFixed.chain_ladder B.point B.onCurve 85 (by norm_num)
      (by norm_num) ks hks_lt
      (fun w => env.env.advice cfg.superConfig.addConfig.xP
        ((env.place self + (offset + w) : ℕ) : ℤ))
      (fun w => env.env.advice cfg.superConfig.addConfig.yP
        ((env.place self + (offset + w) : ℕ) : ℤ))
      (fun j => if j = 0 then
          env.env.advice cfg.superConfig.addConfig.xP
            ((env.place self + offset : ℕ) : ℤ)
        else
          env.env.advice cfg.superConfig.addIncompleteConfig.xQR
            ((env.place self + (offset + j + 1) : ℕ) : ℤ))
      (fun j => if j = 0 then
          env.env.advice cfg.superConfig.addConfig.yP
            ((env.place self + offset : ℕ) : ℤ)
        else
          env.env.advice cfg.superConfig.addIncompleteConfig.yQR
            ((env.place self + (offset + j + 1) : ℕ) : ℤ))
      (fun w hw => by
        obtain ⟨hx, hy⟩ := hWP ⟨w, by omega⟩
        rw [MulFixed.windowPoint_lower B.point (by omega) (hks_lt _)] at hx hy
        exact ⟨hx, hy⟩)
      ⟨if_pos rfl, if_pos rfl⟩
      (by
        intro j hj1 hj83 hass
        obtain ⟨hOnP, hOnQ, hne⟩ := hass
        dsimp only at hOnP hOnQ hne ⊢
        rw [if_neg (by omega : ¬j = 0), if_neg (by omega : ¬j = 0)]
        rcases Nat.lt_or_ge j 2 with hj2 | hj2
        · -- j = 1: the explicit first chunk (window 1 + window 0)
          have hj : j = 1 := by omega
          subst hj
          obtain ⟨-, hOut⟩ := hA1 ⟨hOnP, hOnQ, hne⟩
          exact hOut
        · -- j ≥ 2: loop chunk j − 2
          have h := hLoopS ⟨j - 2, by omega⟩
          rw [show offset + 2 + (j - 2) = offset + j from by omega] at h
          rw [if_neg (by omega : ¬j - 1 = 0), if_neg (by omega : ¬j - 1 = 0),
            show offset + (j - 1) + 1 = offset + j from by omega] at hOnQ
          rw [if_neg (by omega : ¬j - 1 = 0),
            show offset + (j - 1) + 1 = offset + j from by omega] at hne
          rw [if_neg (by omega : ¬j - 1 = 0), if_neg (by omega : ¬j - 1 = 0),
            show offset + (j - 1) + 1 = offset + j from by omega]
          obtain ⟨-, hOut⟩ := h ⟨hOnP, hOnQ, hne⟩
          exact hOut)
    have hI83 := hLadder 83 (by norm_num)
    dsimp only at hI83
    rw [if_neg (by norm_num : ¬(83 : ℕ) = 0), if_neg (by norm_num : ¬(83 : ℕ) = 0),
      show offset + 83 + 1 = offset + 84 from by omega] at hI83
    rw [← hOax, ← hOay]
    rcases hP : Orchard.Ecc.MulFixed.partialSum ks 83 • B.point with ⟨px, py⟩
    rw [hP] at hI83
    rw [hI83.1, hI83.2]
  · -- mulB = windowPoint 84 k₈₄  (the MSB coords row)
    obtain ⟨hwx, hwy⟩ := hWP ⟨84, by norm_num⟩
    rw [← hOmx, ← hOmy]
    rcases hW : Orchard.Ecc.MulFixed.windowPoint B.point 84 (ks 84) with ⟨wx, wy⟩
    rw [show ((⟨84, by norm_num⟩ : Fin 85) : ℕ) = 84 from rfl, hW] at hwx hwy
    rw [hwx, hwy]

set_option linter.all false in
/-- The inner region's completeness, standalone (own declaration budget). -/
private theorem fw_inner_completeness (B : FixedBase) (windows : Vector (FExpr Fp) 85)
    (cfg : Config) (offset : ℕ) :
    FormalRegionCircuit.Completeness (Input := unit) (Output := InnerOut)
      (fun _ : Var unit Fp => innerRegion B.toData cfg offset windows)
      (fun _ self env => eval env (windowCells cfg offset self))
      (InnerEnvAssumptions cfg) (fun _ => True) InnerProverAssumptions
      (InnerProverSpec B) := by
  circuit_proof_start [InnerSpec, InnerEnvAssumptions, InnerProverAssumptions,
    InnerProverSpec]
  obtain ⟨env, rfl, rfl⟩ :
      ∃ pe : Placed ProverEnvironment Fp, pe.place = place ∧ pe.env = env :=
    ⟨⟨place, env⟩, rfl, rfl⟩
  simp only [innerRegion, RegionCircuit.operations_bind,
    RegionOperations.constraints_append, RegionOperations.extendsWitnesses_append]
    at hwit ⊢
  obtain ⟨hWwsl, hWfix, hWchain, -⟩ := hwit
  obtain ⟨hXPeq, hYPeq⟩ := _hE
  -- the honest `< 8` bound, landed on the advice reads
  simp only [windowCells, Vector.getElem_ofFn, AssignedCell.of_cell,
    Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column, Environment.get_advice]
    at hPA
  -- the window cells hold the hint digits (the witness loop's assign clauses).
  -- NB `have hW := hWwsl` (a chunk-typed copy) whnf-storms; peel in place.
  simp only [witnessScalarLoop, circuit_norm, mul_one] at hWwsl
  have hWin : ∀ w : Fin 85, env.env.advice cfg.superConfig.window
      ((env.place self + (offset + w.val) : ℕ) : ℤ)
    = ((hintWindowVal env windows w.val : ℕ) : Fp) := by
    intro w
    have hclause := hWwsl w
    simp only [hintWindowVal]
    rw [hclause, Nat.mod_eq_of_lt (by rw [← hclause]; exact hPA w)]
    exact (ZMod.natCast_zmod_val _).symm
  refine And.intro (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))) ?_
  · with_reducible
      exact (fw_completeness_fixed B cfg offset self env windows hWfix hWchain hWin).1
  · with_reducible
      exact (fw_completeness_fixed B cfg offset self env windows hWfix hWchain hWin).2
  · with_reducible
      exact (fw_completeness_chain B cfg offset self env windows hWchain
        hXPeq hYPeq).1
  · rw [RegionCircuit.operations_pure]
    exact trivial
  · -- the honest-prover contract (`InnerProverSpec`)
    rw [ElaboratedRegionCircuit.output_eq, innerRegion_output] at h_output
    provable_type_simp
    obtain ⟨⟨hOax, hOay⟩, hOmx, hOmy⟩ := h_output
    have hws : ∀ t : ℕ, t < 85 →
        ZMod.val (@getElem! (Vector Fp 85) ℕ Fp _ _ _
          (eval (⟨env.place, env.env.toEnvironment⟩ : Placed Environment Fp)
            (windowCells cfg offset self)) t)
        = hintWindowVal env windows t := by
      intro t ht
      rw [getElem!_pos _ t (by simpa using ht)]
      simp only [windowCells, circuit_norm, Vector.getElem_ofFn, AssignedCell.eval,
        AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
        Environment.get_advice]
      rw [hWin ⟨t, ht⟩]
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
      exact lt_of_lt_of_le (Nat.mod_lt _ (by norm_num))
        (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    have hax := (fw_completeness_chain B cfg offset self env windows hWchain
      hXPeq hYPeq).2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← hOax, hax.1,
        MulFixed.partialSum_congr 83 (fun t ht => hws t (by omega))]
    · rw [← hOay, hax.2.1,
        MulFixed.partialSum_congr 83 (fun t ht => hws t (by omega))]
    · rw [← hOmx, hax.2.2.1, hws 84 (by norm_num)]
    · rw [← hOmy, hax.2.2.2, hws 84 (by norm_num)]

set_option linter.constructorNameAsVariable false in
/-- The inner-region bundle: region 1 with the extractor-form contract. -/
def inner (B : FixedBase) (windows : Vector (FExpr Fp) 85) :
    FormalRegionCircuit Fp Config Config unit InnerOut where
  configure := pure

  synthesize cfg offset _ := innerRegion B.toData cfg offset windows

  Assumptions _ := True

  EnvAssumptions := InnerEnvAssumptions

  Witness := fields 85
  extract cfg offset _ self env := eval env (windowCells cfg offset self)

  Spec := InnerSpec B

  ProverAssumptions := InnerProverAssumptions

  ProverSpec := InnerProverSpec B

  soundness := fun cfg offset => fw_inner_soundness B windows cfg offset

  completeness := fun cfg offset => fw_inner_completeness B windows cfg offset

/-! ## The gadget bundle (`FixedPoint::mul`, `full_width.rs::assign`)

Extractor form per the requirements doc: `Witness` carries the window cells AND the
scalar they encode; `Spec` is literally `output = s • B`. -/

open CompElliptic.Fields.Pasta (Fq PALLAS_BASE_CARD) in
/-- The scalar read off the 85 window cells (the constructive extractor). -/
def windowsScalar (ws : Vector Fp 85) : CompElliptic.Fields.Pasta.Fq :=
  ((∑ w ∈ Finset.range 85, (ws[w]!).val * 8 ^ w : ℕ) : CompElliptic.Fields.Pasta.Fq)

/-- The top-level extraction data: the window cells and the scalar they encode
(a named def keeps the pair opaque during proof setup). -/
def fwExtract (cfg : Config) (i₀ : RegionIndex) (env : Placed Environment Fp) :
    Vector Fp 85 × CompElliptic.Fields.Pasta.Fq :=
  let ws := eval env (windowCells cfg 0 i₀)
  (ws, windowsScalar ws)

/-- Env-level preconditions: the `EccChip` wiring asserts the inner region consumes. -/
def EnvAssumptions (cfg : Config) (_ : Placed Environment Fp) : Prop :=
  cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP ∧
  cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP

/-- The region count of `synthesize`: inner mul + complete addition. -/
private theorem synthesize_regionCount (B : FixedBaseData) (cfg : Config)
    (windows : Vector (FExpr Fp) 85) (i : RegionIndex) :
    Operations.regionCount ((synthesize B cfg windows).operations i) = 2 := by
  simp only [synthesize, circuit_norm, operations_assignRegion, Operations.regionCount]

seal innerRegion in
set_option linter.constructorNameAsVariable false in
/-- Rust `FixedPoint::mul` (`full_width.rs::assign`): `[s]B` for the full-width scalar
the witnessed windows encode. -/
def circuit (B : FixedBase) (windows : Vector (FExpr Fp) 85) :
    FormalCircuit Fp MulFixed.Config Config unit Point where
  name := "fixed-base mul (full width)"

  configure := configure

  synthesize cfg _ := synthesize B.toData cfg windows

  elaborated cfg :=
    { output := fun _ i => (synthesize B.toData cfg windows).output i
      regionCount := fun _ => 2
      output_eq := by intro _ _; rfl
      regionCount_eq := fun _ i => (synthesize_regionCount B.toData cfg windows i).symm }

  EnvAssumptions := EnvAssumptions

  Assumptions _ := True

  Witness := fun F => Vector F 85 × CompElliptic.Fields.Pasta.Fq
  extract cfg _ i₀ env := fwExtract cfg i₀ env

  Spec _ output s := output = (s.2 • B : Point Fp)

  ProverAssumptions _ s _ := ∀ w : Fin 85, (s.1[w.val]).val < 8

  ProverSpec _ _ _ _ := True

  soundness := by
    circuit_proof_start
    obtain ⟨env, rfl, rfl⟩ :
        ∃ pe : Placed Environment Fp, pe.place = place ∧ pe.env = env :=
      ⟨⟨place, env⟩, rfl, rfl⟩
    simp only [synthesize, circuit_norm] at hc
    obtain ⟨hInner, hAdd⟩ := hc
    -- region 1: the inner windowed mul (whole-region bundle). The `change` pre-betas
    -- the chunk spelling: the raw application's expected-type check unfolds
    -- `innerRegion` instead of beta-reducing the synthesize lambda (16s whnf storm).
    change RegionOperations.Constraints env.place i₀ env.env
      (((fun _ : Var unit Fp => innerRegion B.toData cfg 0 windows)
        input_var).operations i₀) at hInner
    have hIS : InnerSpec B (eval env input_var)
        (eval env (innerOutCells cfg 0 i₀))
        (eval env (windowCells cfg 0 i₀)) :=
      fw_inner_soundness B windows cfg 0 i₀ env input_var _hE trivial hInner
    simp only [InnerSpec, innerOutCells, windowCells, circuit_norm] at hIS
    obtain ⟨ks, hks_lt', hws, hAcc, hMulB⟩ := hIS
    -- ── region 2: the complete addition `mul_b + acc` ──
    subcircuit_rw at hAdd
    simp only [addc_spec_eq, addc_assumptions_eq, addc_envAssumptions_eq,
      innerRegion_output_mulB, innerRegion_output_acc, Nat.zero_add, circuit_norm]
      at hAdd
    -- ── the honest scalars, opaque ──
    obtain ⟨t84, ht84_def⟩ : ∃ t : ℕ,
        t = (Orchard.Ecc.MulFixed.windowScalar 84 (ks 84)).val := ⟨_, rfl⟩
    have hwp84 : Orchard.Ecc.MulFixed.windowPoint B.point 84 (ks 84) = t84 • B.point := by
      rw [ht84_def]; rfl
    obtain ⟨S83, hS83_def⟩ : ∃ S : ℕ, S = Orchard.Ecc.MulFixed.partialSum ks 83 := ⟨_, rfl⟩
    have hS83_lt : S83 < 2 * 8 ^ 84 := by
      rw [hS83_def]
      exact Orchard.Ecc.MulFixed.partialSum_lt _ 83 (fun j hj => hks_lt' j (by omega))
    have hS83_pos : 0 < S83 := by
      rw [hS83_def]
      exact Orchard.Ecc.MulFixed.partialSum_pos _ _
    have hS83_card : S83 < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD :=
      Orchard.Ecc.MulFixed.BaseFieldElem.RunningSumMul.inv_lt_card hS83_lt (by norm_num)
    have hOnP : (t84 • B.point).OnCurve := by
      rw [← hwp84]
      exact B.windowPoint_onCurve (hks_lt' 84 (by norm_num))
    have hOnQ : (S83 • B.point).OnCurve := B.nsmul_onCurve hS83_pos hS83_card
    obtain ⟨-, hOutEq⟩ := hAdd ⟨by rw [hMulB, hwp84]; exact Or.inl hOnP,
      by rw [hAcc, ← hS83_def]; exact Or.inl hOnQ⟩
    rw [hMulB, hAcc, hwp84, ← hS83_def,
      show (⟨env.place, env.env⟩ : Placed Environment Fp) = env from rfl] at hOutEq
    simp only [synthesize, circuit_norm] at h_output
    rw [FormalRegionCircuit.output_call] at h_output
    simp only [innerRegion_output_mulB, innerRegion_output_acc, Nat.zero_add,
      circuit_norm] at h_output
    rw [h_output] at hOutEq
    rw [Orchard.Point.nsmul_add_nsmul B.onCurve] at hOutEq
    -- ── the extracted scalar is the digit sum ──
    have hchain : (t84 + S83) • B.point
        = (((∑ w ∈ Finset.range 85, ks w * 8 ^ w : ℕ) :
            CompElliptic.Fields.Pasta.Fq)).val • B.point := by
      rw [ht84_def, hS83_def, ← Orchard.Ecc.MulFixed.FixedBase.add_natCast_val_nsmul,
        Orchard.Ecc.MulFixed.BaseFieldElem.RunningSumMul.windowScalar_partialSum]
    have hsum : windowsScalar
        (eval (⟨env.place, env.env⟩ : Placed Environment Fp) (windowCells cfg 0 i₀))
        = ((∑ w ∈ Finset.range 85, ks w * 8 ^ w : ℕ) :
            CompElliptic.Fields.Pasta.Fq) := by
      unfold windowsScalar
      refine congrArg Nat.cast (Finset.sum_congr rfl ?_)
      intro w hw
      have hwlt : w < 85 := Finset.mem_range.mp hw
      rw [getElem!_pos _ w (by simpa using hwlt)]
      simp only [windowCells, circuit_norm, Vector.getElem_ofFn, AssignedCell.eval,
        AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
        Environment.get_advice, Nat.zero_add]
      rw [hws ⟨w, hwlt⟩, ZMod.val_natCast,
        Nat.mod_eq_of_lt (lt_of_lt_of_le (hks_lt' w hwlt)
          (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]))]
    show ({ x := output_x, y := output_y } : Point Fp)
      = ((fwExtract cfg i₀ ⟨env.place, env.env⟩).2 • B : Point Fp)
    simp only [fwExtract]
    rw [hsum, hOutEq, hchain]
    exact (MulFixed.point_eta _).symm

  completeness := by
    circuit_proof_start
    obtain ⟨env, rfl, rfl⟩ :
        ∃ pe : Placed ProverEnvironment Fp, pe.place = place ∧ pe.env = env :=
      ⟨⟨place, env⟩, rfl, rfl⟩
    simp only [synthesize, circuit_norm] at hwit ⊢
    obtain ⟨hWInner, hWAdd⟩ := hwit
    change RegionOperations.ExtendsWitnesses env.place i₀ env.env
      (((fun _ : Var unit Fp => innerRegion B.toData cfg 0 windows)
        input_var).operations i₀) at hWInner
    simp only [fwExtract] at hPA
    have hIC := fw_inner_completeness B windows cfg 0 i₀ env input_var hWInner _hE
      trivial hPA
    refine And.intro ?_ ?_
    · with_reducible exact hIC.1
    · -- the complete addition on the honest exit points
      have hPS := hIC.2
      rw [ElaboratedRegionCircuit.output_eq, innerRegion_output] at hPS
      simp only [InnerProverSpec, circuit_norm] at hPS
      obtain ⟨hax, hay, hmx, hmy⟩ := hPS
      -- the digit bounds, in the `getElem!` spelling the honest facts use
      have hkv : ∀ t : ℕ, t < 85 →
          (@getElem! (Vector Fp 85) ℕ Fp _ _ _
            (eval env.toEnvironment (windowCells cfg 0 i₀)) t).val < 8 := by
        intro t ht
        rw [getElem!_pos _ t (by simpa using ht)]
        exact hPA ⟨t, ht⟩
      have hC := Halo2.SubcircuitRw.region_completeness_leaf_placed Add.add
        cfg.superConfig.addConfig 0 (i₀ + 1) env
        ⟨((innerRegion B.toData cfg 0 windows).output i₀).mulB,
         ((innerRegion B.toData cfg 0 windows).output i₀).acc⟩ hWAdd
      simp only [addc_assumptions_eq, addc_envAssumptions_eq,
        addc_proverAssumptions_eq, innerRegion_output_mulB, innerRegion_output_acc,
        Nat.zero_add, circuit_norm] at hC
      simp only [innerRegion_output_mulB, innerRegion_output_acc, Nat.zero_add]
      refine hC ⟨?_, ?_⟩
      · -- mulB honest: window-84 point on curve
        have hOn : (Orchard.Ecc.MulFixed.windowPoint B.point 84
            (@getElem! (Vector Fp 85) ℕ Fp _ _ _
              (eval env.toEnvironment (windowCells cfg 0 i₀)) 84).val).OnCurve :=
          B.windowPoint_onCurve (hkv 84 (by norm_num))
        rcases hWp : Orchard.Ecc.MulFixed.windowPoint B.point 84
            (@getElem! (Vector Fp 85) ℕ Fp _ _ _
              (eval env.toEnvironment (windowCells cfg 0 i₀)) 84).val with ⟨wx, wy⟩
        rw [hWp] at hOn hmx hmy
        rw [hmx, hmy]
        exact Or.inl hOn
      · -- acc honest: partialSum point on curve
        have hOn : ((Orchard.Ecc.MulFixed.partialSum
            (fun t => (@getElem! (Vector Fp 85) ℕ Fp _ _ _
              (eval env.toEnvironment (windowCells cfg 0 i₀)) t).val) 83)
              • B.point).OnCurve :=
          B.nsmul_onCurve (Orchard.Ecc.MulFixed.partialSum_pos _ _)
            (Orchard.Ecc.MulFixed.BaseFieldElem.RunningSumMul.inv_lt_card
              (Orchard.Ecc.MulFixed.partialSum_lt _ 83 (fun j hj => hkv j (by omega)))
              (by norm_num))
        rcases hSp : Orchard.Ecc.MulFixed.partialSum
            (fun t => (@getElem! (Vector Fp 85) ℕ Fp _ _ _
              (eval env.toEnvironment (windowCells cfg 0 i₀)) t).val) 83
            • B.point with ⟨sx, sy⟩
        rw [hSp] at hOn hax hay
        rw [hax, hay]
        exact Or.inl hOn

end Halo2.Ironwood.Ecc.MulFixed.FullWidth
