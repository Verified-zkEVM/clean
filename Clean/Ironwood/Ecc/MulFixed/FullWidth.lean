import Clean.Ironwood.Ecc.MulFixed

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

/-- The elaborated-metadata instance for the inner region's synthesize lambda (the
bundle's default `{}`), local so the proofs can name the output. -/
instance innerElab (B : FixedBaseData) (windows : Vector (FExpr Fp) 85)
    (config : Config) (offset : ℕ) :
    ElaboratedRegionCircuit Fp unit InnerOut
      (fun _ : Var unit Fp => innerRegion B config offset windows) := {}

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

  soundness := by
    -- the Mul.lean recipe: contract defs only in the list, targeted peels after
    circuit_proof_start [InnerSpec, InnerEnvAssumptions, InnerProverAssumptions]
    obtain ⟨env, rfl, rfl⟩ :
        ∃ pe : Placed Environment Fp, pe.place = place ∧ pe.env = env :=
      ⟨⟨place, env⟩, rfl, rfl⟩
    simp only [innerRegion, RegionCircuit.operations_bind,
      RegionOperations.constraints_append] at hc
    obtain ⟨-, hFixed, hChain, -⟩ := hc
    rw [innerRegion_output] at h_output
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
      have hLadder := MulFixed.chain_ladder B ks hks_lt
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
        (fun w hw => hWP ⟨w, hw⟩)
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
      have hI83 := hLadder 83 le_rfl
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

  completeness := by sorry

end Halo2.Ironwood.Ecc.MulFixed.FullWidth
