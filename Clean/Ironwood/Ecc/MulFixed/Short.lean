import Clean.Ironwood.Ecc.MulFixed
import Clean.Ironwood.Ecc.MulFixed.ShortTheorems
import Clean.Ironwood.Ecc.MulFixed.BaseFieldElemTheorems

/-!
Fixed-base scalar multiplication by a short *signed* exponent: `output = [sign · magnitude] B`
with `|magnitude| < 2^64` (`L_SCALAR_SHORT = 64`, decomposed into `NUM_WINDOWS_SHORT = 22`
3-bit windows, the same windowing as the shared `MulFixed`). The last window's bit `z_21` and
the sign are checked by the `q_mul_fixed_short` gate, which also conditionally negates the
accumulated `y`-coordinate to fold in the sign.

Reference: `halo2_gadgets/src/ecc/chip/mul_fixed/short.rs`.
-/

-- The variable-name style linter whnf-walks chunk-typed statements below; disabled
-- file-wide (as in the sibling wrappers).
set_option linter.constructorNameAsVariable false

namespace Halo2.Ironwood.Ecc.MulFixed.Short

open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Ecc.MulFixed
  (coordsGate fixedConstantsLoop processWindow windowChain FixedBaseData)
open Halo2.Ironwood.DecomposeRunningSum (copyDecompose rangeCheckExpr)
open Halo2.Ironwood (Point)
open Halo2.Ironwood.Ecc.MulFixed.Short (FixedBase)
open CompElliptic.Fields.Pasta (Fq PALLAS_BASE_CARD PALLAS_SCALAR_CARD)

/-- The data of a proven short fixed base (window tables for the 22 short windows). -/
def _root_.Halo2.Ironwood.Ecc.MulFixed.Short.FixedBase.toData (B : FixedBase) :
    FixedBaseData :=
  { params := B.params, point := B.point, u := B.u }

structure Config where
  -- Selector used for fixed-base scalar mul with short signed exponent.
  qMulFixedShort : Selector
  -- The shared fixed-base mul config.
  superConfig : MulFixed.Config

/-- The "Short fixed-base mul gate", in the Rust constraint order (matches the compiled
AST). -/
def shortGate (cfg : Config) : Gate Fp where
  name := "Short fixed-base mul gate"
  selector := cfg.qMulFixedShort
  constraints :=
    let yP : Expression Fp Query := queryAdvice cfg.superConfig.addConfig.yP 0
    let yA : Expression Fp Query := queryAdvice cfg.superConfig.addConfig.yQR 0
    -- z_21 = k_21, copied into the `u` column
    let lastWindow : Expression Fp Query := queryAdvice cfg.superConfig.u 0
    let sign : Expression Fp Query := queryAdvice cfg.superConfig.window 0
    -- bool_check(last_window) = range_check(last_window, 2)
    let lastWindowCheck := rangeCheckExpr 2 lastWindow
    -- sign² − 1
    let signCheck := sign * sign - Expression.const (1 : Fp)
    -- (y_p − y_a)·(y_p + y_a)  (redundant, kept verbatim — VK data)
    let yCheck := (yP - yA) * (yP + yA)
    -- sign·y_p − y_a
    let negationCheck := sign * yP - yA
    Constraints.withSelector cfg.qMulFixedShort
      [ ("last_window_check", lastWindowCheck),
        ("sign_check", signCheck),
        ("y_check", yCheck),
        ("negation_check", negationCheck) ]

/-- Allocate the `q_mul_fixed_short` selector and register the gate. -/
def configure (superConfig : MulFixed.Config) : Configure Fp Config := do
  let qMulFixedShort ← selector
  let cfg : Config := { qMulFixedShort, superConfig }
  createGate (shortGate cfg)
  return cfg

structure Inputs (F : Type) where
  -- The unsigned magnitude, already assigned.
  magnitude : F
  -- The sign, already assigned (constrained to ±1 by the gate).
  sign : F
deriving ProvableStruct

/-- The conditionally-negated final `y` witness: `sign = −1 ? −y : y` over the sign cell
and the magnitude-mul `y` cell. -/
def yVarWit (sign yMag : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[if readCell env sign = -1 then -(readCell env yMag) else readCell env yMag]

structure InnerOut (F : Type) where
  -- The exit accumulator after windows 0..20.
  acc : Point F
  -- The MSB (window 21) table point.
  mulB : Point F
  -- The running sums; `z_21` feeds the sign row's last-window check.
  zs : Vector F 23
deriving ProvableStruct

/-- Region 1, "Short fixed-base mul (incomplete addition)": the strict 22-window
running-sum decomposition of the magnitude, then the shared inner body (fixed constants
with the running-sum coords toggle; the window chain). -/
def innerRegion (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (magnitude : AssignedCell Fp) :
    RegionCircuit Fp (InnerOut (AssignedCell Fp)) := do
  -- strict copy_decompose, 64 bits in 22 windows
  let zsOut ← (copyDecompose 3 22).call cfg.superConfig.runningSumConfig offset
    ⟨magnitude⟩
  -- assign the fixed constants, with the running-sum coords gate as toggle
  fixedConstantsLoop (coordsGate cfg.superConfig) B cfg.superConfig offset 22
  -- the window chain over the magnitude cell
  let r ← windowChain cfg.superConfig
    (processWindow B (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point) cfg.superConfig
      magnitude) offset 22
  return { acc := r.1, mulB := r.2, zs := zsOut.zs }

/-- Region 2, "Short fixed-base mul (most significant word)": the complete addition at
offset 0, then the sign row at offset 1. Returns the result point (`magnitude_mul.x`,
conditionally-negated `y`). -/
def mswRegion (cfg : Config) (acc mulB : Point (AssignedCell Fp))
    (sign z21 : AssignedCell Fp) : RegionCircuit Fp (Point (AssignedCell Fp)) := do
  -- [magnitude]B by complete addition
  let magnitudeMul ← Add.add.call cfg.superConfig.addConfig 0 ⟨mulB, acc⟩
  -- offset 1: copy sign into `window`
  let _s ← copyAdvice sign cfg.superConfig.window 1
  -- copy z_21 into `u`
  let _z ← copyAdvice z21 cfg.superConfig.u 1
  -- enable the short gate
  (shortGate cfg).enable 1
  -- witness the conditionally-negated y into `add.y_p`
  let yVar ← assignAdvice cfg.superConfig.addConfig.yP 1 (yVarWit sign magnitudeMul.y)
  return { x := magnitudeMul.x, y := yVar }

/-! ## The inner-region bundle

BFE-shaped contracts at 22 windows: the strict 66-bit decomposition, the lower-window
ladder (windows 0..20), and the short MSB (`Short.windowPoint 21`). -/

/-- The inner region's output cells, reduced (the explicit `elaborated` output). -/
def innerOutCells (cfg : Config) (offset : ℕ) (self : RegionIndex) :
    Var InnerOut Fp where
  acc := { x := AssignedCell.of self (offset + 21)
             cfg.superConfig.addIncompleteConfig.xQR,
           y := AssignedCell.of self (offset + 21)
             cfg.superConfig.addIncompleteConfig.yQR }
  mulB := { x := AssignedCell.of self (offset + 21) cfg.superConfig.addConfig.xP,
            y := AssignedCell.of self (offset + 21) cfg.superConfig.addConfig.yP }
  zs := Vector.ofFn (fun j => AssignedCell.of self (offset + j.val)
    cfg.superConfig.runningSumConfig.z)

private theorem innerRegion_output_zs (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (magnitude : AssignedCell Fp) (self : RegionIndex) :
    ((innerRegion B cfg offset magnitude).output self).zs
      = Vector.ofFn (fun j => AssignedCell.of self (offset + j.val)
          cfg.superConfig.runningSumConfig.z) := by
  show (((copyDecompose 3 22).call cfg.superConfig.runningSumConfig offset
      { alpha := magnitude }).output self).zs = _
  rw [FormalRegionCircuit.output_call,
    Halo2.Ironwood.DecomposeRunningSum.copyDecompose_output]

private theorem innerRegion_output_acc (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (magnitude : AssignedCell Fp) (self : RegionIndex) :
    ((innerRegion B cfg offset magnitude).output self).acc
      = { x := AssignedCell.of self (offset + 21)
            cfg.superConfig.addIncompleteConfig.xQR,
          y := AssignedCell.of self (offset + 21)
            cfg.superConfig.addIncompleteConfig.yQR } := by
  simp only [innerRegion, MulFixed.windowChain, circuit_norm]

private theorem innerRegion_output_mulB (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (magnitude : AssignedCell Fp) (self : RegionIndex) :
    ((innerRegion B cfg offset magnitude).output self).mulB
      = { x := AssignedCell.of self (offset + 21) cfg.superConfig.addConfig.xP,
          y := AssignedCell.of self (offset + 21) cfg.superConfig.addConfig.yP } := by
  simp only [innerRegion, MulFixed.windowChain, MulFixed.processWindow, circuit_norm]

/-- The whole inner-region output as a cell literal. -/
private theorem innerRegion_output (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (magnitude : AssignedCell Fp) (self : RegionIndex) :
    (innerRegion B cfg offset magnitude).output self = innerOutCells cfg offset self := by
  rw [innerOutCells, ← innerRegion_output_acc, ← innerRegion_output_mulB,
    ← innerRegion_output_zs]

derive_contract_bridges dec := Halo2.Ironwood.DecomposeRunningSum.copyDecompose 3 22
derive_contract_bridges addinc := Halo2.Ironwood.Ecc.AddIncomplete.add
derive_contract_bridges addc := Halo2.Ironwood.Ecc.Add.add

/-- Lower windows' short table point as a plain scalar multiple. -/
theorem shortWindowPoint_lower (point : Point Fp) {w k : ℕ} (hw : w < 21) (hk : k < 8) :
    Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint point w k
      = (((k + 2) * 8 ^ w : ℕ) • point) := by
  unfold Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint
  rw [Halo2.Ironwood.Ecc.MulFixed.Short.windowScalar_val hw hk]

/-- The shared-config assumptions the inner proofs consume. -/
def InnerEnvAssumptions (cfg : Config) (_ : Placed Environment Fp) : Prop :=
  cfg.superConfig.runningSumConfig.z = cfg.superConfig.window ∧
  cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP ∧
  cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP

/-- The inner bundle's soundness contract, split at the region boundary. -/
def InnerSpec (B : FixedBase)
    (input : Value Halo2.Ironwood.DecomposeRunningSum.Inputs Fp)
    (out : Value InnerOut Fp) (_ : unit Fp) : Prop :=
  ∃ ks : ℕ → ℕ, (∀ w, w < 22 → ks w < 8) ∧
    (let V := ∑ j ∈ Finset.range 22, ks j * 8 ^ j
    input.alpha = (V : Fp) ∧
    out.acc = { x := ((Halo2.Ironwood.Ecc.MulFixed.partialSum ks 20) • B.point).x,
                y := ((Halo2.Ironwood.Ecc.MulFixed.partialSum ks 20) • B.point).y } ∧
    out.mulB = Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point 21 (ks 21) ∧
    ∀ w : Fin 23, out.zs[w.val] = ((V / 2 ^ (3 * w.val) : ℕ) : Fp))

/-- Honest-prover precondition: the magnitude fits the strict 66-bit decomposition. -/
def InnerProverAssumptions
    (input : ProverValue Halo2.Ironwood.DecomposeRunningSum.Inputs Fp)
    (_ : unit Fp) (_ : ProverHint Fp) : Prop :=
  input.alpha.val < 2 ^ 66

/-- Honest-prover postcondition: the exit cells at the magnitude's own digits, plus the
running sums. -/
def InnerProverSpec (B : FixedBase)
    (input : ProverValue Halo2.Ironwood.DecomposeRunningSum.Inputs Fp)
    (out : ProverValue InnerOut Fp) (_ : unit Fp) (_ : ProverHint Fp) : Prop :=
  out.acc.x = (Halo2.Ironwood.Ecc.MulFixed.partialSum
      (fun t => input.alpha.val / 2 ^ (3 * t) % 8) 20 • B.point).x ∧
  out.acc.y = (Halo2.Ironwood.Ecc.MulFixed.partialSum
      (fun t => input.alpha.val / 2 ^ (3 * t) % 8) 20 • B.point).y ∧
  out.mulB.x = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point 21
      (input.alpha.val / 2 ^ (3 * 21) % 8)).x ∧
  out.mulB.y = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point 21
      (input.alpha.val / 2 ^ (3 * 21) % 8)).y ∧
  ∀ w : Fin 23, out.zs[w.val] = ((input.alpha.val / 2 ^ (3 * w.val) : ℕ) : Fp)

/-- The elaborated-metadata instance, with the output cells in explicit reduced form. -/
instance innerElab (B : FixedBaseData) (config : Config) (offset : ℕ) :
    ElaboratedRegionCircuit Fp Halo2.Ironwood.DecomposeRunningSum.Inputs InnerOut
      (fun input : Var Halo2.Ironwood.DecomposeRunningSum.Inputs Fp =>
        innerRegion B config offset input.alpha) where
  output := fun _ self => innerOutCells config offset self
  output_eq := by
    intro _ self
    rw [innerRegion_output]

set_option linter.all false in
/-- The inner region's soundness, standalone (own declaration budget). -/
private theorem short_inner_soundness (B : FixedBase) (cfg : Config) (offset : ℕ) :
    FormalRegionCircuit.Soundness
      (Input := Halo2.Ironwood.DecomposeRunningSum.Inputs) (Output := InnerOut)
      (fun input : Var Halo2.Ironwood.DecomposeRunningSum.Inputs Fp =>
        innerRegion B.toData cfg offset input.alpha)
      (fun _ _ _ => default)
      (InnerEnvAssumptions cfg) (fun _ => True) (InnerSpec B) := by
  circuit_proof_start [InnerSpec, InnerEnvAssumptions, InnerProverAssumptions]
  obtain ⟨env, rfl, rfl⟩ :
      ∃ pe : Placed Environment Fp, pe.place = place ∧ pe.env = env :=
    ⟨⟨place, env⟩, rfl, rfl⟩
  obtain ⟨hDec, hFixed, hChain⟩ := hc
  -- circuit_proof_start consumed the copyDecompose chunk into its contract (assumptions `True`);
  -- discharge and unfold to the running-sum decomposition.
  simp only [dec_spec_eq, dec_assumptions_eq, dec_envAssumptions_eq] at hDec
  -- circuit_proof_start unfolded `innerRegion` in `h_output`; it is defeq to the reduced cells.
  change ProvableStruct.eval env.place env.env (innerOutCells cfg offset self)
    = { acc := output_acc, mulB := output_mulB, zs := output_zs } at h_output
  simp only [innerOutCells] at h_output
  provable_type_simp
  simp only [Halo2.Ironwood.DecomposeRunningSum.copyDecompose_output, circuit_norm] at hDec
  obtain ⟨V, hVlt, hAlphaV, hZs⟩ := hDec
  obtain ⟨⟨hOax, hOay⟩, ⟨hOmx, hOmy⟩, hOzs⟩ := h_output
  -- ── the digit sequence and its reconstruction ──
  have hVlt' : V < 8 ^ 22 := by
    have : (2 : ℕ) ^ (3 * 22) = 8 ^ 22 := by rw [pow_mul]; norm_num
    omega
  have hSum : (∑ j ∈ Finset.range 22, V / 2 ^ (3 * j) % 8 * 8 ^ j) = V := by
    have hstep : ∀ j, V / 2 ^ (3 * j) % 8 * 8 ^ j = V / 8 ^ j % 8 * 8 ^ j := by
      intro j
      rw [pow_mul]
      norm_num
    calc (∑ j ∈ Finset.range 22, V / 2 ^ (3 * j) % 8 * 8 ^ j)
        = ∑ j ∈ Finset.range 22, V / 8 ^ j % 8 * 8 ^ j :=
          Finset.sum_congr rfl (fun j _ => hstep j)
      _ = V % 8 ^ 22 := Halo2.Ironwood.Ecc.MulFixed.sum_base8 V 22
      _ = V := Nat.mod_eq_of_lt hVlt'
  -- ── the per-row window points (the coords rows) ──
  simp only [MulFixed.fixedConstantsLoop, MulFixed.fixedConstantsWindow,
    MulFixed.coordsGate, MulFixed.coordsCheck, MulFixed.eval_interpolatedX,
    circuit_norm, mul_one, one_mul] at hFixed
  obtain ⟨hZW, hXPeq, hYPeq⟩ := _hE
  rw [hZW] at hZs
  have hWP : ∀ w : Fin 22,
      env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point w.val
            (V / 2 ^ (3 * w.val) % 8)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point w.val
            (V / 2 ^ (3 * w.val) % 8)).y := by
    intro w
    have hRow := hFixed w
    obtain ⟨hGate, hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hZf⟩ := hRow
    obtain ⟨hIx, hUy, hCrv⟩ := hGate
    simp only [show B.toData.params = B.params from rfl]
      at hL0 hL1 hL2 hL3 hL4 hL5 hL6 hL7 hZf
    have hz0 := hZs ⟨w.val, by omega⟩
    have hz1 := hZs ⟨w.val + 1, by omega⟩
    have hword :
        env.env.advice cfg.superConfig.window
            ((env.place self + (offset + w.val) : ℕ) : ℤ)
          - env.env.advice cfg.superConfig.window
              ((env.place self + (offset + w.val + 1) : ℕ) : ℤ)
            * ((MulFixed.H : ℕ) : Fp)
        = ((V / 2 ^ (3 * w.val) % 8 : ℕ) : Fp) := by
      rw [show offset + w.val + 1 = offset + (w.val + 1) from by omega, hz0, hz1]
      have hsw := Halo2.Ironwood.DecomposeRunningSum.shift_word_eq 3 V w.val
      norm_num [MulFixed.H] at hsw ⊢
      exact hsw
    rw [hword] at hIx
    have hxP : env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = Halo2.Ironwood.Ecc.MulFixed.interpolate (B.params w.val)
            ((V / 2 ^ (3 * w.val) % 8 : ℕ) : Fp) := by
      rw [← sub_eq_zero.mp hIx]
      apply MulFixed.interpolate_congr_params <;>
        simp only [MulFixed.readParams, circuit_norm, add_zero] <;>
        first
        | exact hL0 | exact hL1 | exact hL2 | exact hL3
        | exact hL4 | exact hL5 | exact hL6 | exact hL7
    have hspec : Halo2.Ironwood.Ecc.MulFixed.Coords.Spec (B.params w.val)
        { window := ((V / 2 ^ (3 * w.val) % 8 : ℕ) : Fp),
          xP := env.env.advice cfg.superConfig.addConfig.xP
            ((env.place self + (offset + w.val) : ℕ) : ℤ),
          yP := env.env.advice cfg.superConfig.addConfig.yP
            ((env.place self + (offset + w.val) : ℕ) : ℤ),
          u := env.env.advice cfg.superConfig.u
            ((env.place self + (offset + w.val) : ℕ) : ℤ) } := by
      refine ⟨hxP, ?_, ?_⟩
      · rw [← hZf]; linear_combination hUy
      · linear_combination hCrv
    have hcw := B.coords_eq_windowPoint (w := w.val) (k := V / 2 ^ (3 * w.val) % 8)
      (by omega) (Nat.mod_lt _ (by norm_num)) rfl hspec
    dsimp only at hcw
    exact hcw
  refine ⟨fun w => V / 2 ^ (3 * w) % 8,
    fun w _ => Nat.mod_lt _ (by norm_num), ?_, ?_, ?_, ?_⟩
  · -- magnitude = ↑V (the digit sum)
    rw [hSum]; exact hAlphaV
  · -- acc = [partialSum ks 20]·B  (the window-chain ladder)
    simp only [MulFixed.windowChain, MulFixed.processWindow, circuit_norm,
      RegionCircuit.operations_bind, RegionOperations.constraints_append] at hChain
    obtain ⟨hA1, hALoop⟩ := hChain
    subcircuit_rw at hA1
    simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
      MulFixed.addinc_output_cells, circuit_norm] at hA1
    have hLoopS := fun (i : Fin 19) => by
      have h := hALoop i
      subcircuit_rw at h
      simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
        MulFixed.addinc_output_cells, circuit_norm, mul_one] at h
      exact h
    clear hALoop
    have hks_lt : ∀ t, V / 2 ^ (3 * t) % 8 < 8 := fun t => Nat.mod_lt _ (by norm_num)
    have hLadder := MulFixed.chain_ladder B.point B.onCurve 22 (by norm_num)
      (by norm_num) (fun t => V / 2 ^ (3 * t) % 8) hks_lt
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
        rw [shortWindowPoint_lower B.point (by omega) (hks_lt _)] at hx hy
        exact ⟨hx, hy⟩)
      ⟨if_pos rfl, if_pos rfl⟩
      (by
        intro j hj1 hj20 hass
        obtain ⟨hOnP, hOnQ, hne⟩ := hass
        dsimp only at hOnP hOnQ hne ⊢
        rw [if_neg (by omega : ¬j = 0), if_neg (by omega : ¬j = 0)]
        rcases Nat.lt_or_ge j 2 with hj2 | hj2
        · have hj : j = 1 := by omega
          subst hj
          obtain ⟨-, hOut⟩ := hA1 ⟨hOnP, hOnQ, hne⟩
          exact hOut
        · have h := hLoopS ⟨j - 2, by omega⟩
          rw [show offset + 2 + (j - 2) = offset + j from by omega] at h
          rw [if_neg (by omega : ¬j - 1 = 0), if_neg (by omega : ¬j - 1 = 0),
            show offset + (j - 1) + 1 = offset + j from by omega] at hOnQ
          rw [if_neg (by omega : ¬j - 1 = 0),
            show offset + (j - 1) + 1 = offset + j from by omega] at hne
          rw [if_neg (by omega : ¬j - 1 = 0), if_neg (by omega : ¬j - 1 = 0),
            show offset + (j - 1) + 1 = offset + j from by omega]
          obtain ⟨-, hOut⟩ := h ⟨hOnP, hOnQ, hne⟩
          exact hOut)
    have hI20 := hLadder 20 (by norm_num)
    dsimp only at hI20
    rw [if_neg (by norm_num : ¬(20 : ℕ) = 0), if_neg (by norm_num : ¬(20 : ℕ) = 0),
      show offset + 20 + 1 = offset + 21 from by omega] at hI20
    rw [← hOax, ← hOay]
    rcases hP : Halo2.Ironwood.Ecc.MulFixed.partialSum (fun t => V / 2 ^ (3 * t) % 8) 20
        • B.point with ⟨px, py⟩
    rw [hP] at hI20
    rw [hI20.1, hI20.2]
  · -- mulB = the short MSB window point
    obtain ⟨hwx, hwy⟩ := hWP ⟨21, by norm_num⟩
    rw [← hOmx, ← hOmy]
    rcases hW : Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point 21 (V / 2 ^ (3 * 21) % 8)
      with ⟨wx, wy⟩
    rw [show ((⟨21, by norm_num⟩ : Fin 22) : ℕ) = 21 from rfl, hW] at hwx hwy
    rw [hwx, hwy]
  · -- the running sums are the shifts of the digit sum
    intro w
    rw [hSum, ← congrArg (fun v => v[w.val]'w.isLt) hOzs]
    simp only [circuit_norm, hZW]
    exact hZs w

set_option linter.all false in
/-- The honest per-window point values (shared by the fixed-rows and chain completeness
halves): the chain's witness programs put the window-table coordinates and `u` values at
each window row. -/
private theorem short_windows_honest (B : FixedBase) (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (input_var_alpha : AssignedCell Fp) (input_alpha : Fp)
    (h_input : env.env.get input_var_alpha.cell.column
      ((env.place input_var_alpha.cell.regionIndex
        + input_var_alpha.cell.rowOffset : ℕ) : ℤ) = input_alpha)
    (hWchain : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.windowChain cfg.superConfig
        (MulFixed.processWindow B.toData (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.toData.point) cfg.superConfig input_var_alpha) offset
        22).operations self)) :
    ∀ w : Fin 22,
      env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point w.val
            (input_alpha.val / 2 ^ (3 * w.val) % 8)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point w.val
            (input_alpha.val / 2 ^ (3 * w.val) % 8)).y ∧
      env.env.advice cfg.superConfig.u
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = B.u w.val (input_alpha.val / 2 ^ (3 * w.val) % 8) := by
  simp only [MulFixed.windowChain, MulFixed.processWindow, circuit_norm, mul_one,
    MulFixed.xPWit, MulFixed.yPWit, MulFixed.uWit] at hWchain
  obtain ⟨hx0, hy0, hu0, hx1, hy1, hu1, _hAW1, hLoopW, hx21, hy21, hu21⟩ := hWchain
  have hread : readCell env input_var_alpha = input_alpha := h_input
  have hPW : ∀ w : Fin 22,
      env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point w.val
            (input_alpha.val / 2 ^ (3 * w.val) % 8)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point w.val
            (input_alpha.val / 2 ^ (3 * w.val) % 8)).y ∧
      env.env.advice cfg.superConfig.u
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = B.u w.val (input_alpha.val / 2 ^ (3 * w.val) % 8) := by
    intro w
    rcases w with ⟨wv, hwv⟩
    simp only []
    rcases Nat.eq_zero_or_pos wv with rfl | hpos
    · rw [show offset + 0 = offset from by omega]
      rw [hx0, hy0, hu0,
        ofFn8_get_windowVal _ env input_var_alpha 0 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 0 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 0 input_alpha hread]
      exact ⟨rfl, rfl, rfl⟩
    rcases Nat.lt_or_ge wv 2 with h1 | h2
    · rw [show wv = 1 from by omega]
      rw [hx1, hy1, hu1,
        ofFn8_get_windowVal _ env input_var_alpha 1 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 1 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 1 input_alpha hread]
      exact ⟨rfl, rfl, rfl⟩
    rcases Nat.lt_or_ge wv 21 with h84 | h84
    · obtain ⟨hxw, hyw, huw, -⟩ := hLoopW ⟨wv - 2, by omega⟩
      rw [show offset + 2 + (wv - 2) = offset + wv from by omega,
        show wv - 2 + 2 = wv from by omega] at hxw hyw huw
      rw [hxw, hyw, huw,
        ofFn8_get_windowVal _ env input_var_alpha wv input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha wv input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha wv input_alpha hread]
      exact ⟨rfl, rfl, rfl⟩
    · rw [show wv = 21 from by omega]
      rw [hx21, hy21, hu21,
        ofFn8_get_windowVal _ env input_var_alpha 21 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 21 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 21 input_alpha hread]
      exact ⟨rfl, rfl, rfl⟩
  exact hPW

set_option linter.all false in
/-- Completeness of the window chain (standalone): each incomplete addition's
constraints from its completeness leaf, on the honest partialSum ladder. -/
private theorem short_completeness_chain (B : FixedBase) (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (input_var_alpha : AssignedCell Fp) (input_alpha : Fp)
    (h_input : env.env.get input_var_alpha.cell.column
      ((env.place input_var_alpha.cell.regionIndex
        + input_var_alpha.cell.rowOffset : ℕ) : ℤ) = input_alpha)
    (hWfix : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.fixedConstantsLoop (MulFixed.coordsGate cfg.superConfig) B.toData
        cfg.superConfig offset 22).operations self))
    (hWchain : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.windowChain cfg.superConfig
        (MulFixed.processWindow B.toData (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.toData.point) cfg.superConfig input_var_alpha) offset
        22).operations self))
    (hZW : cfg.superConfig.runningSumConfig.z = cfg.superConfig.window)
    (hXPeq : cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP)
    (hYPeq : cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP)
    (hZs : ∀ w : Fin 23, env.env.advice cfg.superConfig.window
        ((env.place self + (offset + w.val) : ℕ) : ℤ)
      = ((input_alpha.val / 2 ^ (3 * w.val) : ℕ) : Fp)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((MulFixed.windowChain cfg.superConfig
        (MulFixed.processWindow B.toData (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.toData.point) cfg.superConfig input_var_alpha) offset
        22).operations self) ∧
    (env.env.advice cfg.superConfig.addIncompleteConfig.xQR
        ((env.place self + (offset + 21) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.partialSum
          (fun t => input_alpha.val / 2 ^ (3 * t) % 8) 20 • B.point).x ∧
     env.env.advice cfg.superConfig.addIncompleteConfig.yQR
        ((env.place self + (offset + 21) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.partialSum
          (fun t => input_alpha.val / 2 ^ (3 * t) % 8) 20 • B.point).y ∧
     env.env.advice cfg.superConfig.addConfig.xP
        ((env.place self + (offset + 21) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point 21
          (input_alpha.val / 2 ^ (3 * 21) % 8)).x ∧
     env.env.advice cfg.superConfig.addConfig.yP
        ((env.place self + (offset + 21) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point 21
          (input_alpha.val / 2 ^ (3 * 21) % 8)).y) := by
  have hPW := short_windows_honest B cfg offset self env input_var_alpha input_alpha
    h_input hWchain
  have hks_lt : ∀ t, input_alpha.val / 2 ^ (3 * t) % 8 < 8 :=
    fun t => Nat.mod_lt _ (by norm_num)
  -- the addinc chunk witnesses
  simp only [MulFixed.windowChain, MulFixed.processWindow, circuit_norm, mul_one] at hWchain
  obtain ⟨-, -, -, -, -, -, hAW1, hLoopW, -, -, -⟩ := hWchain
  -- per-chunk derived statements (Spec under Assumptions) and leaf constraints
  have hD1 := Halo2.SubcircuitRw.region_completeness_derived_placed
    AddIncomplete.add cfg.superConfig.addIncompleteConfig (offset + 1) self env
    ⟨⟨AssignedCell.of self (offset + 1) cfg.superConfig.addConfig.xP,
      AssignedCell.of self (offset + 1) cfg.superConfig.addConfig.yP⟩,
     ⟨AssignedCell.of self offset cfg.superConfig.addConfig.xP,
      AssignedCell.of self offset cfg.superConfig.addConfig.yP⟩⟩ hAW1
  simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
    addinc_proverAssumptions_eq, MulFixed.addinc_output_cells, circuit_norm] at hD1
  have hLoopD := fun (i : Fin 19) => by
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
  -- honest accumulator invariant via the shared ladder (`MulFixed.chain_ladder`)
  have hLadder := MulFixed.chain_ladder B.point B.onCurve 22 (by norm_num)
    (by norm_num) (fun t => input_alpha.val / 2 ^ (3 * t) % 8) hks_lt
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
      rw [shortWindowPoint_lower B.point (by omega) (hks_lt _)] at hx hy
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
        obtain ⟨⟨-, hOut⟩, -⟩ := hD1 ⟨hOnP, hOnQ, hne⟩
        exact hOut
      · -- j ≥ 2: loop chunk j − 2
        have h := hLoopD ⟨j - 2, by omega⟩
        rw [show offset + 2 + (j - 2) = offset + j from by omega] at h
        rw [if_neg (by omega : ¬j - 1 = 0), if_neg (by omega : ¬j - 1 = 0),
          show offset + (j - 1) + 1 = offset + j from by omega] at hOnQ
        rw [if_neg (by omega : ¬j - 1 = 0),
          show offset + (j - 1) + 1 = offset + j from by omega] at hne
        rw [if_neg (by omega : ¬j - 1 = 0), if_neg (by omega : ¬j - 1 = 0),
          show offset + (j - 1) + 1 = offset + j from by omega]
        obtain ⟨⟨-, hOut⟩, -⟩ := h ⟨hOnP, hOnQ, hne⟩
        exact hOut)
  -- the invariant in the downstream row spelling
  have hInv : ∀ j : ℕ, 1 ≤ j → j ≤ 20 →
      env.env.advice cfg.superConfig.addIncompleteConfig.xQR
          ((env.place self + (offset + j + 1) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.partialSum
            (fun t => input_alpha.val / 2 ^ (3 * t) % 8) j • B.point).x ∧
      env.env.advice cfg.superConfig.addIncompleteConfig.yQR
          ((env.place self + (offset + j + 1) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.partialSum
            (fun t => input_alpha.val / 2 ^ (3 * t) % 8) j • B.point).y := by
    intro j hj1 hj83
    have h := hLadder j hj83
    dsimp only at h
    rw [if_neg (by omega : ¬j = 0), if_neg (by omega : ¬j = 0)] at h
    exact h
  have hHonest : env.env.advice cfg.superConfig.addIncompleteConfig.xQR
        ((env.place self + (offset + 21) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.partialSum
          (fun t => input_alpha.val / 2 ^ (3 * t) % 8) 20 • B.point).x ∧
      env.env.advice cfg.superConfig.addIncompleteConfig.yQR
        ((env.place self + (offset + 21) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.partialSum
          (fun t => input_alpha.val / 2 ^ (3 * t) % 8) 20 • B.point).y ∧
      env.env.advice cfg.superConfig.addConfig.xP
        ((env.place self + (offset + 21) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point 21
          (input_alpha.val / 2 ^ (3 * 21) % 8)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
        ((env.place self + (offset + 21) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point 21
          (input_alpha.val / 2 ^ (3 * 21) % 8)).y := by
    have h83 := hInv 20 (by norm_num) le_rfl
    rw [show offset + 20 + 1 = offset + 21 from by omega] at h83
    obtain ⟨hx21, hy21, -⟩ := hPW ⟨21, by norm_num⟩
    rw [show ((⟨21, by norm_num⟩ : Fin 22) : ℕ) = 21 from rfl] at hx21 hy21
    exact ⟨h83.1, h83.2, hx21, hy21⟩
  refine And.intro ?_ hHonest
  simp only [MulFixed.windowChain, MulFixed.processWindow, circuit_norm, mul_one]
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
    rw [show ((⟨1, by norm_num⟩ : Fin 22) : ℕ) = 1 from rfl] at hp1x hp1y
    rw [show ((⟨0, by norm_num⟩ : Fin 22) : ℕ) = 0 from rfl,
      show offset + 0 = offset from by omega] at hp0x hp0y
    obtain ⟨t1, ht1_def⟩ : ∃ t : ℕ, t = (Halo2.Ironwood.Ecc.MulFixed.Short.windowScalar 1
      (input_alpha.val / 2 ^ (3 * 1) % 8)).val := ⟨_, rfl⟩
    obtain ⟨s0, hs0_def⟩ : ∃ t : ℕ, t = (Halo2.Ironwood.Ecc.MulFixed.Short.windowScalar 0
      (input_alpha.val / 2 ^ (3 * 0) % 8)).val := ⟨_, rfl⟩
    have ht1 : t1 = (input_alpha.val / 2 ^ (3 * 1) % 8 + 2) * 8 ^ 1 := by
      rw [ht1_def]
      exact Halo2.Ironwood.Ecc.MulFixed.Short.windowScalar_val (by norm_num) (hks_lt 1)
    have hs0 : s0 = (input_alpha.val / 2 ^ (3 * 0) % 8 + 2) * 8 ^ 0 := by
      rw [hs0_def]
      exact Halo2.Ironwood.Ecc.MulFixed.Short.windowScalar_val (by norm_num) (hks_lt 0)
    have hwp1 : Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point 1
        (input_alpha.val / 2 ^ (3 * 1) % 8) = t1 • B.point := by rw [ht1_def]; rfl
    have hwp0 : Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point 0
        (input_alpha.val / 2 ^ (3 * 0) % 8) = s0 • B.point := by rw [hs0_def]; rfl
    rw [hwp1] at hp1x hp1y
    rw [hwp0] at hp0x hp0y
    obtain ⟨hbb1, hbb2, hbb3⟩ := base_bounds (hks_lt 0) (hks_lt 1)
    rw [← hs0] at hbb1 hbb2 hbb3
    rw [← ht1] at hbb2 hbb3
    exact hC1 ⟨by
        rw [hp1x, hp1y]
        exact point_eta_onCurve (by rw [← hwp1]; exact B.windowPoint_onCurve (hks_lt 1)),
      by
        rw [hp0x, hp0y]
        exact point_eta_onCurve (by rw [← hwp0]; exact B.windowPoint_onCurve (hks_lt 0)),
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
    rw [show ((⟨i.val + 2, by omega⟩ : Fin 22) : ℕ) = i.val + 2 from rfl,
      show offset + (i.val + 2) = offset + 2 + i.val from by omega] at hpx hpy
    have hih := hInv (i.val + 1) (by omega) (by omega)
    rw [show offset + (i.val + 1) + 1 = offset + 2 + i.val from by omega] at hih
    obtain ⟨t, ht_def⟩ : ∃ t : ℕ,
        t = (Halo2.Ironwood.Ecc.MulFixed.Short.windowScalar (i.val + 2)
          (input_alpha.val / 2 ^ (3 * (i.val + 2)) % 8)).val := ⟨_, rfl⟩
    obtain ⟨S, hS_def⟩ : ∃ S : ℕ,
        S = Halo2.Ironwood.Ecc.MulFixed.partialSum
          (fun t => input_alpha.val / 2 ^ (3 * t) % 8) (i.val + 1) := ⟨_, rfl⟩
    have hval : t = (input_alpha.val / 2 ^ (3 * (i.val + 2)) % 8 + 2) * 8 ^ (i.val + 2) := by
      rw [ht_def]
      exact Halo2.Ironwood.Ecc.MulFixed.Short.windowScalar_val (by omega) (hks_lt _)
    have hwp : Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point (i.val + 2)
        (input_alpha.val / 2 ^ (3 * (i.val + 2)) % 8) = t • B.point := by
      rw [ht_def]; rfl
    rw [hwp] at hpx hpy
    rw [← hS_def] at hih
    have hS_lt : S < 2 * 8 ^ (i.val + 2) := by
      rw [hS_def]
      exact Halo2.Ironwood.Ecc.MulFixed.partialSum_lt _ _ (fun _ _ => hks_lt _)
    have hS_pos : 0 < S := by
      rw [hS_def]; exact Halo2.Ironwood.Ecc.MulFixed.partialSum_pos _ _
    obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ :=
      step_bounds (hks_lt (i.val + 2)) hS_lt hS_pos (by omega)
    rw [← hval] at hb1 hb2 hb3 hb5
    exact hC ⟨by
        rw [hpx, hpy]
        exact point_eta_onCurve (B.nsmul_onCurve hb1 hb3),
      by
        rw [hih.1, hih.2]
        exact point_eta_onCurve (B.nsmul_onCurve hS_pos hb4),
      by
        rw [hpx, hih.1]
        exact B.nsmul_x_ne hS_pos hb2 (by omega)⟩

set_option linter.all false in
/-- Completeness of the fixed-constants rows (standalone — per-declaration budget):
the witness equations pin the fixed cells and the honest advice values; the coords
gate holds by the fixed-base invariants at the honest digits. -/
private theorem short_completeness_fixed (B : FixedBase) (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (input_var_alpha : AssignedCell Fp) (input_alpha : Fp)
    (h_input : env.env.get input_var_alpha.cell.column
      ((env.place input_var_alpha.cell.regionIndex
        + input_var_alpha.cell.rowOffset : ℕ) : ℤ) = input_alpha)
    (hWfix : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.fixedConstantsLoop (MulFixed.coordsGate cfg.superConfig) B.toData
        cfg.superConfig offset 22).operations self))
    (hWchain : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.windowChain cfg.superConfig
        (MulFixed.processWindow B.toData (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.toData.point) cfg.superConfig input_var_alpha) offset
        22).operations self))
    (hZW : cfg.superConfig.runningSumConfig.z = cfg.superConfig.window)
    (hXPeq : cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP)
    (hYPeq : cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP)
    (hZs : ∀ w : Fin 23, env.env.advice cfg.superConfig.window
        ((env.place self + (offset + w.val) : ℕ) : ℤ)
      = ((input_alpha.val / 2 ^ (3 * w.val) : ℕ) : Fp)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((MulFixed.fixedConstantsLoop (MulFixed.coordsGate cfg.superConfig) B.toData
        cfg.superConfig offset 22).operations self) := by
  simp only [MulFixed.fixedConstantsLoop, MulFixed.fixedConstantsWindow,
    MulFixed.coordsGate, MulFixed.coordsCheck, MulFixed.eval_interpolatedX,
    circuit_norm, mul_one, one_mul]
  -- the fixed-cell witness equations (the loop's `assignFixed` clauses)
  simp only [MulFixed.fixedConstantsLoop, MulFixed.fixedConstantsWindow, circuit_norm,
    mul_one] at hWfix
  intro i
  obtain ⟨hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hZf⟩ := hWfix i
  refine ⟨?_, hL0, hL1, hL2, hL3, hL4, hL5, hL6, hL7, hZf⟩
  -- the coords gate on the honest window point
  simp only [MulFixed.windowChain, MulFixed.processWindow, circuit_norm, mul_one,
    MulFixed.xPWit, MulFixed.yPWit, MulFixed.uWit] at hWchain
  obtain ⟨hx0, hy0, hu0, hx1, hy1, hu1, _hAW1, hLoopW, hx21, hy21, hu21⟩ := hWchain
  have hread : readCell env input_var_alpha = input_alpha := h_input
  have hPW : ∀ w : Fin 22,
      env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point w.val
            (input_alpha.val / 2 ^ (3 * w.val) % 8)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point w.val
            (input_alpha.val / 2 ^ (3 * w.val) % 8)).y ∧
      env.env.advice cfg.superConfig.u
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = B.u w.val (input_alpha.val / 2 ^ (3 * w.val) % 8) := by
    intro w
    rcases w with ⟨wv, hwv⟩
    simp only []
    rcases Nat.eq_zero_or_pos wv with rfl | hpos
    · rw [show offset + 0 = offset from by omega]
      rw [hx0, hy0, hu0,
        ofFn8_get_windowVal _ env input_var_alpha 0 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 0 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 0 input_alpha hread]
      exact ⟨rfl, rfl, rfl⟩
    rcases Nat.lt_or_ge wv 2 with h1 | h2
    · rw [show wv = 1 from by omega]
      rw [hx1, hy1, hu1,
        ofFn8_get_windowVal _ env input_var_alpha 1 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 1 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 1 input_alpha hread]
      exact ⟨rfl, rfl, rfl⟩
    rcases Nat.lt_or_ge wv 21 with h84 | h84
    · obtain ⟨hxw, hyw, huw, -⟩ := hLoopW ⟨wv - 2, by omega⟩
      rw [show offset + 2 + (wv - 2) = offset + wv from by omega,
        show wv - 2 + 2 = wv from by omega] at hxw hyw huw
      rw [hxw, hyw, huw,
        ofFn8_get_windowVal _ env input_var_alpha wv input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha wv input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha wv input_alpha hread]
      exact ⟨rfl, rfl, rfl⟩
    · rw [show wv = 21 from by omega]
      rw [hx21, hy21, hu21,
        ofFn8_get_windowVal _ env input_var_alpha 21 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 21 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 21 input_alpha hread]
      exact ⟨rfl, rfl, rfl⟩
  -- the three gate equations at row i, from the invariants at the honest digit
  simp only [show B.toData.params = B.params from rfl] at hL0 hL1 hL2 hL3 hL4 hL5 hL6
  simp only [show B.toData.params = B.params from rfl] at hL7 hZf
  obtain ⟨hpx, hpy, hpu⟩ := hPW i
  have hz0 := hZs ⟨i.val, by omega⟩
  have hz1 := hZs ⟨i.val + 1, by omega⟩
  have hdig : input_alpha.val / 2 ^ (3 * i.val) % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hword : env.env.advice cfg.superConfig.window
        ((env.place self + (offset + i.val) : ℕ) : ℤ)
      - env.env.advice cfg.superConfig.window
          ((env.place self + (offset + i.val + 1) : ℕ) : ℤ)
        * ((MulFixed.H : ℕ) : Fp)
      = ((input_alpha.val / 2 ^ (3 * i.val) % 8 : ℕ) : Fp) := by
    rw [show offset + i.val + 1 = offset + (i.val + 1) from by omega, hz0, hz1]
    have hsw := Halo2.Ironwood.DecomposeRunningSum.shift_word_eq 3 input_alpha.val i.val
    norm_num [MulFixed.H] at hsw ⊢
    exact hsw
  refine ⟨?_, ?_, ?_⟩
  · -- check x
    rw [hword, hpx]
    have hcongr : Halo2.Ironwood.Ecc.MulFixed.interpolate
        (MulFixed.readParams cfg.superConfig
          (Query.eval env.env.toEnvironment
            (fun j => if j = cfg.superConfig.runningSumConfig.qRangeCheck.index then 1
              else 0)
            ((env.place self + (offset + i.val) : ℕ) : ℤ)))
        ((input_alpha.val / 2 ^ (3 * i.val) % 8 : ℕ) : Fp)
        = Halo2.Ironwood.Ecc.MulFixed.interpolate (B.params i.val)
            ((input_alpha.val / 2 ^ (3 * i.val) % 8 : ℕ) : Fp) := by
      apply MulFixed.interpolate_congr_params <;>
        simp only [MulFixed.readParams, circuit_norm, add_zero] <;>
        first
        | exact hL0 | exact hL1 | exact hL2 | exact hL3
        | exact hL4 | exact hL5 | exact hL6 | exact hL7
    rw [hcongr, B.interpolate_eq i.val i.isLt _ hdig]
    exact sub_self _
  · -- check y
    rw [hpu, hpy, hZf]
    have huu := B.u_mul_u i.val i.isLt _ hdig
    linear_combination huu
  · -- on-curve
    rw [hpx, hpy]
    have hoc := B.windowPoint_onCurve (w := i.val) hdig
    unfold Halo2.Ironwood.Point.OnCurve at hoc
    linear_combination hoc

set_option linter.all false in
/-- The decompose child's completeness products (standalone): its constraints chunk and
the honest running-sum values. -/
private theorem short_completeness_dec (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (input_var_alpha : AssignedCell Fp) (input_alpha : Fp)
    (h_input : env.env.get input_var_alpha.cell.column
      ((env.place input_var_alpha.cell.regionIndex
        + input_var_alpha.cell.rowOffset : ℕ) : ℤ) = input_alpha)
    (hPA : input_alpha.val < 2 ^ 66)
    (hWdec : RegionOperations.ExtendsWitnesses env.place self env.env
      (((Halo2.Ironwood.DecomposeRunningSum.copyDecompose 3 22).call
        cfg.superConfig.runningSumConfig offset
        { alpha := input_var_alpha }).operations self)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      (((Halo2.Ironwood.DecomposeRunningSum.copyDecompose 3 22).call
        cfg.superConfig.runningSumConfig offset
        { alpha := input_var_alpha }).operations self) ∧
    ∀ w : Fin 23, env.env.advice cfg.superConfig.runningSumConfig.z
        ((env.place self + (offset + w.val) : ℕ) : ℤ)
      = ((input_alpha.val / 2 ^ (3 * w.val) : ℕ) : Fp) := by
  have hDecC := Halo2.SubcircuitRw.region_completeness_leaf_placed
    (Halo2.Ironwood.DecomposeRunningSum.copyDecompose 3 22)
    cfg.superConfig.runningSumConfig offset self env { alpha := input_var_alpha } hWdec
  have hDecS := Halo2.SubcircuitRw.region_completeness_derived_placed
    (Halo2.Ironwood.DecomposeRunningSum.copyDecompose 3 22)
    cfg.superConfig.runningSumConfig offset self env { alpha := input_var_alpha } hWdec
  simp only [dec_spec_eq, dec_assumptions_eq, dec_envAssumptions_eq,
    dec_proverAssumptions_eq, dec_proverSpec_eq,
    Halo2.Ironwood.DecomposeRunningSum.copyDecompose_output, circuit_norm]
    at hDecC hDecS
  have hPA' : (env.env.get input_var_alpha.cell.column
      ((env.place input_var_alpha.cell.regionIndex
        + input_var_alpha.cell.rowOffset : ℕ) : ℤ)).val < 2 ^ (3 * 22) := by
    rw [h_input]
    exact lt_of_lt_of_le hPA (by norm_num)
  refine And.intro (hDecC hPA') ?_
  have hZs := (hDecS hPA').2
  simp only [h_input] at hZs
  exact hZs

set_option linter.all false in
/-- The inner region's completeness, standalone (own declaration budget). -/
private theorem short_inner_completeness (B : FixedBase) (cfg : Config) (offset : ℕ) :
    FormalRegionCircuit.Completeness
      (Input := Halo2.Ironwood.DecomposeRunningSum.Inputs) (Output := InnerOut)
      (fun input : Var Halo2.Ironwood.DecomposeRunningSum.Inputs Fp =>
        innerRegion B.toData cfg offset input.alpha)
      (fun _ _ _ => default)
      (InnerEnvAssumptions cfg) (fun _ => True) InnerProverAssumptions
      (InnerProverSpec B) := by
    circuit_proof_start
    obtain ⟨env, rfl, rfl⟩ :
        ∃ pe : Placed ProverEnvironment Fp, pe.place = place ∧ pe.env = env :=
      ⟨⟨place, env⟩, rfl, rfl⟩
    obtain ⟨hWdec, hWfix, hWchain⟩ := hwit
    obtain ⟨hZW, hXPeq, hYPeq⟩ := _hE
    have hDC := short_completeness_dec cfg offset self env input_var_alpha input_alpha
      h_input hPA hWdec
    have hZs : ∀ w : Fin 23, env.env.advice cfg.superConfig.window
        ((env.place self + (offset + w.val) : ℕ) : ℤ)
      = ((input_alpha.val / 2 ^ (3 * w.val) : ℕ) : Fp) := by
      rw [← hZW]
      exact hDC.2
    -- circuit_proof_start consumed the copyDecompose chunk (completeness mode), so the goal opens
    -- with the child's preconditions (EnvA/A vacuous, PA = the magnitude bound) rather than its
    -- constraints, and the trailing `pure` region auto-discharged.
    refine And.intro (And.intro ⟨trivial, trivial, hPA⟩ (And.intro ?_ ?_)) ?_
    · with_reducible
        exact short_completeness_fixed B cfg offset self env input_var_alpha
          input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs
    · with_reducible
        exact (short_completeness_chain B cfg offset self env input_var_alpha
          input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs).1
    · -- the honest-prover contract (`InnerProverSpec`)
      simp only [InnerProverSpec]
      change ProvableStruct.eval env.place env.env.toEnvironment (innerOutCells cfg offset self)
        = _ at h_output
      simp only [innerOutCells] at h_output
      provable_type_simp
      obtain ⟨⟨hOax, hOay⟩, ⟨hOmx, hOmy⟩, hOzs⟩ := h_output
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [← hOax]
        with_reducible exact (short_completeness_chain B cfg offset self env
          input_var_alpha input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs).2.1
      · rw [← hOay]
        with_reducible exact (short_completeness_chain B cfg offset self env
          input_var_alpha input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs).2.2.1
      · rw [← hOmx]
        with_reducible exact (short_completeness_chain B cfg offset self env
          input_var_alpha input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs).2.2.2.1
      · rw [← hOmy]
        with_reducible exact (short_completeness_chain B cfg offset self env
          input_var_alpha input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs).2.2.2.2
      · intro w
        rw [← congrArg (fun v => v[w.val]'w.isLt) hOzs]
        simp only [circuit_norm]
        exact hDC.2 w

/-- The inner-region bundle. -/
def inner (B : FixedBase) : FormalRegionCircuit Fp Config Config
    Halo2.Ironwood.DecomposeRunningSum.Inputs InnerOut where
  configure := pure
  synthesize cfg offset input := innerRegion B.toData cfg offset input.alpha
  Assumptions _ := True
  EnvAssumptions := InnerEnvAssumptions
  Spec := InnerSpec B
  ProverAssumptions := InnerProverAssumptions
  ProverSpec := InnerProverSpec B
  soundness := fun cfg offset => short_inner_soundness B cfg offset
  completeness := fun cfg offset => short_inner_completeness B cfg offset

/-- The two regions of `assign`. Returns the result point `[sign·magnitude]B`. -/
def synthesize (B : FixedBaseData) (cfg : Config) (input : Inputs (AssignedCell Fp)) :
    Circuit Fp (Var Point Fp) := do
  let inn ←
    assignRegion "Short fixed-base mul (incomplete addition)"
      (innerRegion B cfg 0 input.magnitude)
  assignRegion "Short fixed-base mul (most significant word)"
    (mswRegion cfg inn.acc inn.mulB input.sign inn.zs[21])

/-! ## The gadget bundle -/

/-- The conditionally-negated `y` witness value (single-element vector, `rfl` tail). -/
private theorem yVarWit_eval (env : Placed ProverEnvironment Fp)
    (sign yMag : AssignedCell Fp) :
    ((yVarWit sign yMag).eval env)[0]
      = if readCell env sign = -1 then -(readCell env yMag) else readCell env yMag := by
  simp only [yVarWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- The complete-addition child's output cells through the `call` wrapper (`rfl`). -/
private theorem addc_call_out (cfgA : Add.Config) (row : ℕ)
    (input : Var Add.Inputs Fp) (self : RegionIndex) :
    (Add.add.call cfgA row input).output self
      = { x := AssignedCell.of self (row + 1) cfgA.xQR,
          y := AssignedCell.of self (row + 1) cfgA.yQR } :=
  (FormalRegionCircuit.output_call Add.add cfgA row input self).trans rfl

/-- The complete-addition child's output cells (`rfl`). -/
private theorem addc_output_cells (cfgA : Add.Config) (row : ℕ)
    (input : Var Add.Inputs Fp) (self : RegionIndex) :
    Add.add.output cfgA row input self
      = { x := AssignedCell.of self (row + 1) cfgA.xQR,
          y := AssignedCell.of self (row + 1) cfgA.yQR } := rfl

/-- The msw region's output cells: the add result's `x` and the conditionally-negated
`y` (`rfl`-walk). -/
private theorem mswRegion_output (cfg : Config) (acc mulB : Point (AssignedCell Fp))
    (sign z21 : AssignedCell Fp) (self : RegionIndex) :
    (mswRegion cfg acc mulB sign z21).output self
      = { x := AssignedCell.of self 1 cfg.superConfig.addConfig.xQR,
          y := AssignedCell.of self 1 cfg.superConfig.addConfig.yP } := by
  simp only [mswRegion, circuit_norm, RegionCircuit.output_bind, RegionCircuit.output_pure,
    FormalRegionCircuit.output_call', addc_output_cells]

/-- Env-level preconditions: the `EccChip` wiring asserts the inner region consumes. -/
def EnvAssumptions (cfg : Config) (env : Placed Environment Fp) : Prop :=
  InnerEnvAssumptions cfg env

/-- The gadget's semantic contract: the output is the fixed base scaled by the signed
short exponent. -/
def Spec (B : FixedBase) (input : Inputs Fp) (output : Point Fp) : Prop :=
  input.magnitude.val < 2 ^ 64 ∧
    ((input.sign = 1 ∧ output = (input.magnitude.val : Fq) • B) ∨
      (input.sign = -1 ∧ output = ((-(input.magnitude.val : Fq)) : Fq) • B))

/-- The region count of `synthesize`: inner mul + most significant word. -/
private theorem synthesize_regionCount (B : FixedBaseData) (cfg : Config)
    (input : Inputs (AssignedCell Fp)) (i : RegionIndex) :
    Operations.regionCount ((synthesize B cfg input).operations i) = 2 := by
  simp only [synthesize, circuit_norm, operations_assignRegion, Operations.regionCount]

seal innerRegion in
set_option linter.constructorNameAsVariable false in
/-- `[sign·magnitude]B`. -/
def circuit (B : FixedBase) : FormalCircuit Fp MulFixed.Config Config Inputs Point where
  name := "fixed-base mul (short signed)"

  configure := configure

  synthesize cfg input := synthesize B.toData cfg input

  elaborated cfg :=
    { output := fun input i => (synthesize B.toData cfg input).output i
      regionCount := fun _ => 2
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i => (synthesize_regionCount B.toData cfg input i).symm }

  EnvAssumptions := EnvAssumptions

  Assumptions _ := True

  Spec input output _ := Spec B input output

  ProverAssumptions input _ _ :=
    input.magnitude.val < 2 ^ 64 ∧ (input.sign = 1 ∨ input.sign = -1)

  ProverSpec _ _ _ _ := True

  soundness := by
    circuit_proof_start
    obtain ⟨env, rfl, rfl⟩ :
        ∃ pe : Placed Environment Fp, pe.place = place ∧ pe.env = env :=
      ⟨⟨place, env⟩, rfl, rfl⟩
    simp only [synthesize, circuit_norm] at hc
    obtain ⟨hInner, hMsw⟩ := hc
    simp only [mswRegion, shortGate,
      Halo2.Ironwood.DecomposeRunningSum.eval_rangeCheckExpr, innerRegion_output_zs,
      Vector.getElem_ofFn, circuit_norm, mul_one, one_mul] at hMsw
    obtain ⟨hAddC, hCpSign, hCpZ21, hBool, hSignSq, _hYchk, hNeg⟩ := hMsw
    obtain ⟨hIMag, hISign⟩ := h_input
    -- ── region 1: the inner windowed mul ──
    have hIS := short_inner_soundness B cfg 0 i₀ env ⟨input_var_magnitude⟩ _hE trivial
      hInner
    rw [ElaboratedRegionCircuit.output_eq] at hIS
    dsimp only at hIS
    simp only [innerRegion_output, innerOutCells, InnerSpec, circuit_norm] at hIS
    obtain ⟨ks, hks_lt', hMag, hAcc, hMulB, hZs⟩ := hIS
    -- ── the complete addition `mul_b + acc` ──
    subcircuit_rw at hAddC
    simp only [addc_spec_eq, addc_assumptions_eq, addc_envAssumptions_eq,
      innerRegion_output_mulB, innerRegion_output_acc, Nat.zero_add, circuit_norm]
      at hAddC
    obtain ⟨t21, ht21_def⟩ : ∃ t : ℕ,
        t = (Halo2.Ironwood.Ecc.MulFixed.Short.windowScalar 21 (ks 21)).val := ⟨_, rfl⟩
    have hwp21 : Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point 21 (ks 21)
        = t21 • B.point := by rw [ht21_def]; rfl
    obtain ⟨S20, hS20_def⟩ : ∃ S : ℕ, S = Halo2.Ironwood.Ecc.MulFixed.partialSum ks 20 :=
      ⟨_, rfl⟩
    have hS20_lt : S20 < 2 * 8 ^ 21 := by
      rw [hS20_def]
      exact Halo2.Ironwood.Ecc.MulFixed.partialSum_lt _ 20 (fun j hj => hks_lt' j (by omega))
    have hS20_pos : 0 < S20 := by
      rw [hS20_def]
      exact Halo2.Ironwood.Ecc.MulFixed.partialSum_pos _ _
    have hS20_card : S20 < PALLAS_SCALAR_CARD :=
      Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.RunningSumMul.inv_lt_card hS20_lt (by norm_num)
    have hOnP : (t21 • B.point).OnCurve := by
      rw [← hwp21]
      exact B.windowPoint_onCurve (hks_lt' 21 (by norm_num))
    have hOnQ : (S20 • B.point).OnCurve :=
      Halo2.Ironwood.Point.nsmul_onCurve B.onCurve hS20_pos hS20_card
    obtain ⟨-, hOutEq⟩ := hAddC ⟨by rw [hMulB, hwp21]; exact Or.inl hOnP,
      by rw [hAcc, ← hS20_def]; exact Or.inl hOnQ⟩
    rw [hMulB, hAcc, hwp21, ← hS20_def,
      show (⟨env.place, env.env⟩ : Placed Environment Fp) = env from rfl] at hOutEq
    rw [Halo2.Ironwood.Point.nsmul_add_nsmul B.onCurve] at hOutEq
    -- the add output cells, as reads
    rw [show Add.add.output cfg.superConfig.addConfig 0
        ⟨{ x := AssignedCell.of i₀ 21 cfg.superConfig.addConfig.xP,
           y := AssignedCell.of i₀ 21 cfg.superConfig.addConfig.yP },
         { x := AssignedCell.of i₀ 21 cfg.superConfig.addIncompleteConfig.xQR,
           y := AssignedCell.of i₀ 21 cfg.superConfig.addIncompleteConfig.yQR }⟩ (i₀ + 1)
        = { x := AssignedCell.of (i₀ + 1) 1 cfg.superConfig.addConfig.xQR,
            y := AssignedCell.of (i₀ + 1) 1 cfg.superConfig.addConfig.yQR }
      from rfl] at hOutEq
    simp only [circuit_norm, AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
      Cell.of_rowOffset, Cell.of_column, Environment.get_advice] at hOutEq
    -- the circuit's output cells
    simp only [synthesize, circuit_norm, mswRegion_output] at h_output
    obtain ⟨hOx, hOy⟩ := h_output
    -- ── V is a 64-bit magnitude (the last-window bool check) ──
    have hz21 := hZs ⟨21, by norm_num⟩
    rw [show ((⟨21, by norm_num⟩ : Fin 23) : ℕ) = 21 from rfl] at hz21
    rw [hz21] at hCpZ21
    obtain ⟨b, hb_lt, hb_eq⟩ :=
      (Halo2.Ironwood.DecomposeRunningSum.inRange_iff_exists_lt 2 (by norm_num) _).mp
        ((Halo2.Ironwood.Utilities.RunningSum.rangeCheckPoly_eq_zero_iff 2 _).mp hBool)
    rw [hCpZ21] at hb_eq
    obtain ⟨V, hV_def⟩ : ∃ v : ℕ, v = ∑ j ∈ Finset.range 22, ks j * 8 ^ j := ⟨_, rfl⟩
    have hVlt : V < 8 ^ 22 := by
      rw [hV_def]
      exact Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.RunningSumMul.sum_lt_of_windows hks_lt'
    have hdig21 : V / 2 ^ 63 = b := by
      apply Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.RunningSumMul.natCast_inj_of_lt_8
        (by rw [show (2:ℕ) ^ 63 = 8 ^ 21 from by norm_num]
            rw [show (8:ℕ) ^ 22 = 8 ^ 21 * 8 from by ring] at hVlt
            exact Nat.div_lt_of_lt_mul (by omega))
        (by omega)
      rw [← hb_eq, ← hV_def, show (2:ℕ) ^ 63 = 2 ^ (3 * 21) from by norm_num]
    have hV64 : V < 2 ^ 64 := by
      have : V / 2 ^ 63 ≤ 1 := by omega
      omega
    -- ── the sign facts ──
    rw [hISign] at hCpSign
    rw [hCpSign] at hSignSq hNeg
    have hsign : input_sign = 1 ∨ input_sign = -1 := by
      rcases mul_eq_zero.mp (show (input_sign - 1) * (input_sign + 1) = 0 from by
        linear_combination hSignSq) with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    -- ── assemble the signed spec ──
    have hchain : (t21 + S20) • B.point = ((V : Fq)).val • B.point := by
      rw [ht21_def, hS20_def,
        ← Halo2.Ironwood.Ecc.MulFixed.Short.FixedBase.add_natCast_val_nsmul, hV_def,
        Halo2.Ironwood.Ecc.MulFixed.Short.windowScalar_partialSum]
    rw [hchain] at hOutEq
    obtain ⟨yMag, hyMag_def⟩ : ∃ ym : Fp, ym = env.env.advice cfg.superConfig.addConfig.yQR
        ((env.place (i₀ + 1) + 1 : ℕ) : ℤ) := ⟨_, rfl⟩
    rw [← hyMag_def] at hOutEq
    have hmulEq : ({ x := output_x, y := yMag } : Point Fp)
        = ((V : Fq) • B : Point Fp) := by
      rw [← hOx]
      rw [show (((V : Fq)) • B : Point Fp)
          = { x := (((V : Fq)).val • B.point).x, y := (((V : Fq)).val • B.point).y }
        from rfl, ← hOutEq]
    have hyeq : input_sign * output_y = yMag := by
      rw [hyMag_def, ← hOy]
      linear_combination hNeg
    have hsigned := Halo2.Ironwood.Ecc.MulFixed.Short.signed_output_spec B
      (sign := input_sign) (ySigned := output_y) hmulEq
      (fun hs => by rw [← hyeq, hs, one_mul])
      (fun hs => by rw [← hyeq, hs]; ring)
    -- TODO this is a bridge from the spec the proof originally used, to a more direct one
    -- refactor to prove this more naturally
    let output : Point Fp := { x := output_x, y := output_y }
    suffices ∃ m : ℕ, m < 2 ^ 64 ∧ input_magnitude = (m : Fp) ∧
    ((input_sign = 1 ∧ output = ((m : Fq) • B : Point Fp)) ∨
      (input_sign = -1 ∧ output = (((-(m : Fq)) : Fq) • B : Point Fp))) by
      simp only [output] at this
      obtain ⟨V, hV64, hV_def, hsign⟩ := this
      have hmag : input_magnitude.val = V := by
        rw [hV_def, ZMod.val_natCast_of_lt]
        linarith
      subst hmag
      simp only [Spec, hV64, hsign]
      simp
    refine ⟨V, hV64, ?_, ?_⟩
    · rw [← hIMag, hMag, hV_def]
    · rcases hsign with hs | hs
      · exact Or.inl ⟨hs, hsigned.1 hs⟩
      · exact Or.inr ⟨hs, hsigned.2 hs⟩

  completeness := by
    circuit_proof_start
    obtain ⟨env, rfl, rfl⟩ :
        ∃ pe : Placed ProverEnvironment Fp, pe.place = place ∧ pe.env = env :=
      ⟨⟨place, env⟩, rfl, rfl⟩
    simp only [synthesize, circuit_norm] at hwit ⊢
    obtain ⟨hWInner, hWMsw⟩ := hwit
    obtain ⟨hIMag, hISign⟩ := h_input
    obtain ⟨hMag64, hSignPM⟩ := hPA
    have hIC := short_inner_completeness B cfg 0 i₀ env ⟨input_var_magnitude⟩ hWInner
      _hE trivial (by
        show ZMod.val (eval env (⟨input_var_magnitude⟩ :
          Var Halo2.Ironwood.DecomposeRunningSum.Inputs Fp)).alpha < 2 ^ 66
        have h : (eval env (⟨input_var_magnitude⟩ :
            Var Halo2.Ironwood.DecomposeRunningSum.Inputs Fp)).alpha
            = input_magnitude := by
          simp only [circuit_norm, AssignedCell.eval]
          exact hIMag
        rw [h]
        exact lt_of_lt_of_le hMag64 (by norm_num))
    have hPS := hIC.2
    rw [ElaboratedRegionCircuit.output_eq] at hPS
    dsimp only at hPS
    simp only [innerRegion_output, innerOutCells, InnerProverSpec, circuit_norm] at hPS
    obtain ⟨hax, hay, hmx, hmy, hzs⟩ := hPS
    have hks_lt : ∀ t : ℕ, input_magnitude.val / 2 ^ (3 * t) % 8 < 8 :=
      fun t => Nat.mod_lt _ (by norm_num)
    -- the honest facts are over the magnitude READ; land them on `input_magnitude`
    rw [hIMag] at hax hay hmx hmy
    refine And.intro ?_ ?_
    · exact hIC.1
    · -- the msw region: the addition leaf + the sign row on honest values
      simp only [mswRegion, shortGate,
        Halo2.Ironwood.DecomposeRunningSum.eval_rangeCheckExpr, innerRegion_output_zs,
        Vector.getElem_ofFn, circuit_norm, mul_one, one_mul] at hWMsw ⊢
      obtain ⟨hWAdd, hWSign, hWZ21, hWyVar⟩ := hWMsw
      have hC := Halo2.SubcircuitRw.region_completeness_leaf_placed Add.add
        cfg.superConfig.addConfig 0 (i₀ + 1) env
        ⟨((innerRegion B.toData cfg 0 input_var_magnitude).output i₀).mulB,
         ((innerRegion B.toData cfg 0 input_var_magnitude).output i₀).acc⟩ hWAdd
      simp only [addc_assumptions_eq, addc_envAssumptions_eq,
        addc_proverAssumptions_eq, innerRegion_output_mulB, innerRegion_output_acc,
        Nat.zero_add, circuit_norm] at hC
      -- honest values at the sign row
      rw [yVarWit_eval, addc_call_out] at hWyVar
      simp only [readCell, AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
        Cell.of_rowOffset, Cell.of_column, Environment.get_advice,
        Nat.zero_add] at hWyVar
      rw [hISign] at hWyVar
      have h2ne : (2 : Fp) ≠ 0 := by
        have h : ((2 : ℕ) : Fp) ≠ 0 := by
          rw [Ne, ZMod.natCast_eq_zero_iff]
          intro hdvd
          have := Nat.le_of_dvd (by norm_num) hdvd
          norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD] at this
        simpa using h
      have hone_ne : ¬(1 : Fp) = -1 := fun h => h2ne (by linear_combination h)
      refine ⟨?_, hWSign, hWZ21, ?_, ?_, ?_, ?_⟩
      · -- the complete addition on the honest exit points
        simp only [innerRegion_output_mulB, innerRegion_output_acc, Nat.zero_add]
        refine hC ⟨?_, ?_⟩
        · have hOn : (Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point 21
              (input_magnitude.val / 2 ^ (3 * 21) % 8)).OnCurve :=
            B.windowPoint_onCurve (hks_lt 21)
          rcases hWp : Halo2.Ironwood.Ecc.MulFixed.Short.windowPoint B.point 21
              (input_magnitude.val / 2 ^ (3 * 21) % 8) with ⟨wx, wy⟩
          rw [hWp] at hOn hmx hmy
          rw [hmx, hmy]
          exact Or.inl hOn
        · have hOn : ((Halo2.Ironwood.Ecc.MulFixed.partialSum
              (fun t => input_magnitude.val / 2 ^ (3 * t) % 8) 20) • B.point).OnCurve :=
            Halo2.Ironwood.Point.nsmul_onCurve B.onCurve
              (Halo2.Ironwood.Ecc.MulFixed.partialSum_pos _ _)
              (Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.RunningSumMul.inv_lt_card
                (Halo2.Ironwood.Ecc.MulFixed.partialSum_lt _ 20 (fun j _ => hks_lt j))
                (by norm_num))
          rcases hSp : Halo2.Ironwood.Ecc.MulFixed.partialSum
              (fun t => input_magnitude.val / 2 ^ (3 * t) % 8) 20 • B.point
            with ⟨sx, sy⟩
          rw [hSp] at hOn hax hay
          rw [hax, hay]
          exact Or.inl hOn
      · -- last-window bool check on the honest running sum
        have hz21 := hzs ⟨21, by norm_num⟩
        rw [show ((⟨21, by norm_num⟩ : Fin 23) : ℕ) = 21 from rfl, hIMag] at hz21
        rw [hWZ21, hz21]
        have hb : input_magnitude.val / 2 ^ (3 * 21) < 2 := by
          have : (2:ℕ) ^ (3 * 21) = 2 ^ 63 := by norm_num
          omega
        exact (Halo2.Ironwood.Utilities.RunningSum.rangeCheckPoly_eq_zero_iff 2 _).mpr
          ((Halo2.Ironwood.DecomposeRunningSum.inRange_iff_exists_lt 2 (by norm_num)
            _).mpr ⟨input_magnitude.val / 2 ^ (3 * 21), hb, rfl⟩)
      · -- sign check
        rw [hWSign, hISign]
        rcases hSignPM with hs | hs <;> rw [hs] <;> ring
      · -- y check
        rcases hSignPM with hs | hs
        · rw [hs, if_neg hone_ne] at hWyVar
          rw [hWyVar]
          ring
        · rw [hs, if_pos rfl] at hWyVar
          rw [hWyVar]
          ring
      · -- negation check
        rw [hWSign, hISign]
        rcases hSignPM with hs | hs
        · rw [hs, if_neg hone_ne] at hWyVar
          rw [hWyVar, hs]
          ring
        · rw [hs, if_pos rfl] at hWyVar
          rw [hWyVar, hs]
          ring

derive_contract_bridges circuit (B : FixedBase) := circuit B

end Halo2.Ironwood.Ecc.MulFixed.Short
