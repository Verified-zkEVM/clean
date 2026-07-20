import Clean.Ironwood.Ecc.MulFixed
import Clean.Ironwood.Utilities.LookupRangeCheck
import Clean.Ironwood.Ecc.MulFixed.BaseFieldElemTheorems

/-!
Fixed-base scalar multiplication by a base-field element α (`FixedPointBaseField::mul`),
the NullifierK path of the Orchard circuit: the strict 85-window running-sum
decomposition of α feeds the shared incomplete-addition window chain, a complete
addition closes the last window, and a canonicity gate proves `0 ≤ α < p` (the Pallas
base-field modulus) — so the result is exactly `[α]B`, embedded into the scalar field.

Reference: `halo2_gadgets/src/ecc/chip/mul_fixed/base_field_elem.rs`.
-/

-- The variable-name style linter whnf-walks the chunk-typed hypothesis statements of
-- the completeness helper theorems below and times out; disabled file-wide.
set_option linter.constructorNameAsVariable false

namespace Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem

open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Ecc.MulFixed (coordsGate fixedConstantsLoop processWindow)
open Halo2.Ironwood.DecomposeRunningSum (copyDecompose rangeCheckExpr)
open Halo2.Ironwood (Point pallasB tP)
open Halo2.Ironwood.Ecc.MulFixed (FixedBase)
open Halo2.Ironwood.Ecc.MulFixed (FixedBaseData)
open CompElliptic.Fields.Pasta (Fq PALLAS_BASE_CARD PALLAS_SCALAR_CARD)

structure Config where
  -- Selector for the canonicity-checks gate.
  qMulFixedBaseField : Selector
  -- The three advice columns used for canonicity checks.
  canonAdvices : Fin 3 → Column .advice
  -- Lookup config for the 13-word range check on α₀'.
  lookupConfig : LookupRangeCheck.Config 10
  -- The shared fixed-base multiplication config.
  superConfig : MulFixed.Config

/-! ## The canonicity-checks gate

Cell layout, relative to the gate row (selector enabled at region offset 1):

    | canon_advices[0]   | canon_advices[1] | canon_advices[2] |
    ------------------------------------------------------------
    | α                  |                  | z_84_alpha       |   ← prev
    | α_0_prime          | α_1              | α_2              |   ← cur
    | z_13_alpha_0_prime | z_44_alpha       | z_43_alpha       |   ← next
-/

/-- The "Canonicity checks" gate, the exact Rust AST (constraint order: the four
`canon_checks`, the three `decomposition_checks`, then the `alpha_0_prime check`).
`range_check`/`bool_check` are the shared halo2 fold (`rangeCheckExpr`). -/
def canonGate (cfg : Config) : Gate Fp where
  name := "Canonicity checks"
  selector := cfg.qMulFixedBaseField
  constraints :=
    let alpha : Expression Fp Query := queryAdvice (cfg.canonAdvices 0) (-1)
    let z84Alpha : Expression Fp Query := queryAdvice (cfg.canonAdvices 2) (-1)
    -- α_0 is derived, not witnessed: α − z_84·2^252 (scale on the right)
    let alpha0 := alpha - z84Alpha * (((2 ^ 252 : ℕ) : Fp) : Expression Fp Query)
    let alpha1 : Expression Fp Query := queryAdvice (cfg.canonAdvices 1) 0
    let alpha2 : Expression Fp Query := queryAdvice (cfg.canonAdvices 2) 0
    let alpha0Prime : Expression Fp Query := queryAdvice (cfg.canonAdvices 0) 0
    let z13Alpha0Prime : Expression Fp Query := queryAdvice (cfg.canonAdvices 0) 1
    let z44Alpha : Expression Fp Query := queryAdvice (cfg.canonAdvices 1) 1
    let z43Alpha : Expression Fp Query := queryAdvice (cfg.canonAdvices 2) 1
    -- decomposition checks
    let alpha1RangeCheck := rangeCheckExpr 4 alpha1
    let alpha2RangeCheck := rangeCheckExpr 2 alpha2
    let z84AlphaCheck :=
      z84Alpha - (alpha1 + alpha2 * (((1 <<< 2 : ℕ) : Fp) : Expression Fp Query))
    -- α_0_prime = α_0 + 2^130 − t_p
    let alpha0PrimeCheck :=
      alpha0Prime - (alpha0 + (((2 ^ 130 : ℕ) : Fp) : Expression Fp Query)
        - ((tP : Fp) : Expression Fp Query))
    -- canonicity checks for MSB = 1
    -- Rust multiplies by an `Expression::Constant` here (a `Product` node, unlike the
    -- `Scaled` field-mul used everywhere else in this gate) — `mulConstant` keeps the
    -- erased AST byte-identical (VK matching).
    let alpha0Hi120 :=
      z44Alpha - Expression.mulConstant z84Alpha ((2 ^ 120 : ℕ) : Fp)
    let a43 := z43Alpha - z44Alpha * (((8 : ℕ) : Fp) : Expression Fp Query)
    Constraints.withSelector cfg.qMulFixedBaseField
      [ ("MSB = 1 => alpha_1 = 0", alpha2 * alpha1),
        ("MSB = 1 => alpha_0_hi_120 = 0", alpha2 * alpha0Hi120),
        ("MSB = 1 => a_43 = 0 or 1", alpha2 * rangeCheckExpr 2 a43),
        ("MSB = 1 => z_13_alpha_0_prime = 0", alpha2 * z13Alpha0Prime),
        ("alpha_1_range_check", alpha1RangeCheck),
        ("alpha_2_range_check", alpha2RangeCheck),
        ("z_84_alpha_check", z84AlphaCheck),
        ("alpha_0_prime check", alpha0PrimeCheck) ]

/-- Enable equality on the three canon advices, allocate a fresh selector, register the
canonicity gate. (The canon-advice/incomplete-addition column deconfliction assert holds
by construction at the `EccChip` wiring: canon = advices 6/7/8, add_incomplete =
advices 0..3.) -/
def configure (canonAdvices : Fin 3 → Column .advice)
    (lookupConfig : LookupRangeCheck.Config 10) (superConfig : MulFixed.Config) :
    Configure Fp Config := do
  enableEquality (canonAdvices 0)
  enableEquality (canonAdvices 1)
  enableEquality (canonAdvices 2)
  let qMulFixedBaseField ← selector
  let cfg : Config := { qMulFixedBaseField, canonAdvices, lookupConfig, superConfig }
  createGate (canonGate cfg)
  return cfg

/-! ## Synthesize -/

structure InnerOut (F : Type) where
  -- The exit accumulator after windows 0..83.
  acc : Point F
  -- The MSB window (84) point.
  mulB : Point F
  -- The running sums (`z_0 = α`; `z_43/z_44/z_84` feed the canonicity check).
  zs : Vector F 86
deriving ProvableStruct

/-- Region 1, "Base-field elem fixed-base mul (incomplete addition)": the strict
running-sum decomposition of α (85 3-bit windows over 255 bits), the fixed constants,
the window-0 accumulator, the incomplete-addition loop over windows 1..83, and the most
significant window 84. -/
def innerRegion (B : FixedBaseData) (cfg : Config) (offset : ℕ) (alpha : AssignedCell Fp) :
    RegionCircuit Fp (InnerOut (AssignedCell Fp)) := do
  -- scalar decomposition: strict `copy_decompose`
  let zsOut ← (copyDecompose 3 85).call cfg.superConfig.runningSumConfig offset ⟨alpha⟩
  -- `assign_fixed_constants`; the coords toggle is the running-sum selector's coords gate
  fixedConstantsLoop (coordsGate cfg.superConfig) B cfg.superConfig offset 85
  -- the shared window chain: init (window 0), incomplete additions (1..83), MSB (84)
  let r ← MulFixed.windowChain cfg.superConfig
    (processWindow B (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point) cfg.superConfig alpha)
    offset 85
  return { acc := r.1, mulB := r.2, zs := zsOut.zs }

/-- The honest `α₀' = (α − z_84·2^252) + 2^130 − t_p` witness, from the α and `z_84`
cells. -/
def alphaZeroPrimeWit (alpha z84 : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[readCell env alpha - readCell env z84 * ((2 ^ 252 : ℕ) : Fp)
      + ((2 ^ 130 : ℕ) : Fp) - tP]

/-- Rust `witness_check(value, 13, strict = false)`: the "Witness element" region —
witness `z_0` from the given program at offset 0, then the positional 13-round lookup
range check (no strict tail). Returns `(z_0, z_13)` — `α₀'` and its high tail, both
copied into the canonicity check. -/
def witnessCheck13 (cfg : LookupRangeCheck.Config 10) (w : WitgenIR Fp 1) :
    Circuit Fp (AssignedCell Fp × AssignedCell Fp) :=
  assignRegion "Witness element" (do
    let z0 ← assignAdvice cfg.runningSum 0 w
    let out ← (LookupRangeCheck.rangeCheckAt 10 13 false).call cfg 0 ()
    return (z0, out.zLast))

/-- The honest `α_1 = α[252..=253]` witness (`bitrange_subset`). -/
def alpha1Wit (alpha : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[(((readCell env alpha).val / 2 ^ 252 % 4 : ℕ) : Fp)]

/-- The honest `α_2 = α[254]` witness. -/
def alpha2Wit (alpha : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[(((readCell env alpha).val / 2 ^ 254 % 2 : ℕ) : Fp)]

/-- Region 4, "Canonicity checks": selector at offset 1, then the three-row copy/witness
block (see the gate's cell layout). -/
def canonicityRegion (cfg : Config) (alpha z84 alphaPrime z13 z44 z43 : AssignedCell Fp) :
    RegionCircuit Fp Unit := do
  (canonGate cfg).enable 1
  -- offset 0: α and its top three bits
  let _ ← copyAdvice alpha (cfg.canonAdvices 0) 0
  let _ ← copyAdvice z84 (cfg.canonAdvices 2) 0
  -- offset 1: α₀' (copied), α_1 and α_2 (witnessed)
  let _ ← copyAdvice alphaPrime (cfg.canonAdvices 0) 1
  let _a1 ← assignAdvice (cfg.canonAdvices 1) 1 (alpha1Wit alpha)
  let _a2 ← assignAdvice (cfg.canonAdvices 2) 1 (alpha2Wit alpha)
  -- offset 2: the three running sums
  let _ ← copyAdvice z13 (cfg.canonAdvices 0) 2
  let _ ← copyAdvice z44 (cfg.canonAdvices 1) 2
  let _ ← copyAdvice z43 (cfg.canonAdvices 2) 2
  return ()

/-! ## The inner-region bundle (proof boundary for region 1)

The bundle covers exactly the first region (up to but excluding the complete addition):
the Spec exposes `acc` (windows 0..83 accumulated) and `mul_b` (the MSB window point)
separately, plus the running sums; the parent's complete addition combines them via
`partialSum ks 83 + windowScalar 84 (ks 84) = V` in `Fq`. -/

/-! ### `innerRegion` output projections (lazy `rfl`/`simp` — the `mainRegion_output_*`
pattern; the loop bodies never force) -/

private theorem innerRegion_output_zs (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (alpha : AssignedCell Fp) (self : RegionIndex) :
    ((innerRegion B cfg offset alpha).output self).zs
      = Vector.ofFn (fun j => AssignedCell.of self (offset + j.val)
          cfg.superConfig.runningSumConfig.z) := by
  show (((copyDecompose 3 85).call cfg.superConfig.runningSumConfig offset
      { alpha := alpha }).output self).zs = _
  rw [FormalRegionCircuit.output_call,
    Halo2.Ironwood.DecomposeRunningSum.copyDecompose_output]

private theorem innerRegion_output_acc (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (alpha : AssignedCell Fp) (self : RegionIndex) :
    ((innerRegion B cfg offset alpha).output self).acc
      = { x := AssignedCell.of self (offset + 84) cfg.superConfig.addIncompleteConfig.xQR,
          y := AssignedCell.of self (offset + 84) cfg.superConfig.addIncompleteConfig.yQR } := by
  simp only [innerRegion, MulFixed.windowChain, circuit_norm]

private theorem innerRegion_output_mulB (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (alpha : AssignedCell Fp) (self : RegionIndex) :
    ((innerRegion B cfg offset alpha).output self).mulB
      = { x := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.xP,
          y := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.yP } := by
  simp only [innerRegion, MulFixed.windowChain, MulFixed.processWindow, circuit_norm]

/-- The whole inner-region output as a cell literal (assembled from the projections via
structure eta). -/
private theorem innerRegion_output (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (alpha : AssignedCell Fp) (self : RegionIndex) :
    (innerRegion B cfg offset alpha).output self
      = { acc := { x := AssignedCell.of self (offset + 84)
                     cfg.superConfig.addIncompleteConfig.xQR,
                   y := AssignedCell.of self (offset + 84)
                     cfg.superConfig.addIncompleteConfig.yQR },
          mulB := { x := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.xP,
                    y := AssignedCell.of self (offset + 84) cfg.superConfig.addConfig.yP },
          zs := Vector.ofFn (fun j => AssignedCell.of self (offset + j.val)
                  cfg.superConfig.runningSumConfig.z) } := by
  rw [← innerRegion_output_acc, ← innerRegion_output_mulB, ← innerRegion_output_zs]

-- contract bridges for the children consumed by the inner bundle
derive_contract_bridges dec := Halo2.Ironwood.DecomposeRunningSum.copyDecompose 3 85
derive_contract_bridges addinc := Halo2.Ironwood.Ecc.AddIncomplete.add

/-- The inner bundle's config facts: the `configure`-time asserts plus running-sum
column sharing. -/
def InnerEnvAssumptions (cfg : Config) (_ : Placed Environment Fp) : Prop :=
  cfg.superConfig.runningSumConfig.z = cfg.superConfig.window ∧
  cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP ∧
  cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP

/-- The inner bundle's soundness contract, split at the region boundary. -/
def InnerSpec (B : FixedBase)
    (input : Value Halo2.Ironwood.DecomposeRunningSum.Inputs Fp)
    (out : Value InnerOut Fp) (_ : unit Fp) : Prop :=
  ∃ ks : ℕ → ℕ, (∀ w, w < 85 → ks w < 8) ∧
    (let V := ∑ j ∈ Finset.range 85, ks j * 8 ^ j
    input.alpha = (V : Fp) ∧
    out.acc = { x := ((Halo2.Ironwood.Ecc.MulFixed.partialSum ks 83) • B.point).x,
                y := ((Halo2.Ironwood.Ecc.MulFixed.partialSum ks 83) • B.point).y } ∧
    out.mulB = Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point 84 (ks 84) ∧
    ∀ w : Fin 86, out.zs[w.val] = ((V / 2 ^ (3 * w.val) : ℕ) : Fp))

/-- Honest-prover precondition: α fits 255 bits (automatic at the Pallas instantiation). -/
def InnerProverAssumptions
    (input : ProverValue Halo2.Ironwood.DecomposeRunningSum.Inputs Fp)
    (_ : unit Fp) (_ : ProverHint Fp) : Prop :=
  input.alpha.val < 2 ^ 255

/-- Honest-prover postcondition: the exit cells hold the honest ladder values at α's own
digits, and the running sums hold α's 3-bit shifts — what the parent's completeness
needs to discharge the complete addition's assumptions and the canonicity gate. -/
def InnerProverSpec (B : FixedBase)
    (input : ProverValue Halo2.Ironwood.DecomposeRunningSum.Inputs Fp)
    (out : ProverValue InnerOut Fp) (_ : unit Fp) (_ : ProverHint Fp) : Prop :=
  out.acc.x = (Halo2.Ironwood.Ecc.MulFixed.partialSum
      (fun t => input.alpha.val / 2 ^ (3 * t) % 8) 83 • B.point).x ∧
  out.acc.y = (Halo2.Ironwood.Ecc.MulFixed.partialSum
      (fun t => input.alpha.val / 2 ^ (3 * t) % 8) 83 • B.point).y ∧
  out.mulB.x = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point 84
      (input.alpha.val / 2 ^ (3 * 84) % 8)).x ∧
  out.mulB.y = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point 84
      (input.alpha.val / 2 ^ (3 * 84) % 8)).y ∧
  ∀ w : Fin 86, out.zs[w.val] = ((input.alpha.val / 2 ^ (3 * w.val) : ℕ) : Fp)

/-- The elaborated-metadata instance for the inner region's synthesize lambda (the
bundle's default `{}`), local so the standalone proofs can state
`Soundness`/`Completeness` over it. -/
instance innerElab (B : FixedBaseData) (config : Config) (offset : ℕ) :
    ElaboratedRegionCircuit Fp Halo2.Ironwood.DecomposeRunningSum.Inputs InnerOut
      (fun input : Var Halo2.Ironwood.DecomposeRunningSum.Inputs Fp =>
        innerRegion B config offset input.alpha) := {}

set_option linter.all false in
/-- The honest per-window point values (shared by the fixed-rows and chain completeness
halves): the chain's witness programs put the window-table coordinates and `u` values at
each window row. -/
private theorem inner_windows_honest (B : FixedBase) (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (input_var_alpha : AssignedCell Fp) (input_alpha : Fp)
    (h_input : env.env.get input_var_alpha.cell.column
      ((env.place input_var_alpha.cell.regionIndex
        + input_var_alpha.cell.rowOffset : ℕ) : ℤ) = input_alpha)
    (hWchain : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.windowChain cfg.superConfig
        (MulFixed.processWindow B.toData (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.toData.point) cfg.superConfig input_var_alpha) offset
        85).operations self)) :
    ∀ w : Fin 85,
      env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point w.val
            (input_alpha.val / 2 ^ (3 * w.val) % 8)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point w.val
            (input_alpha.val / 2 ^ (3 * w.val) % 8)).y ∧
      env.env.advice cfg.superConfig.u
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = B.u w.val (input_alpha.val / 2 ^ (3 * w.val) % 8) := by
  simp only [MulFixed.windowChain, MulFixed.processWindow, circuit_norm, mul_one,
    MulFixed.xPWit, MulFixed.yPWit, MulFixed.uWit] at hWchain
  obtain ⟨hx0, hy0, hu0, hx1, hy1, hu1, _hAW1, hLoopW, hx84, hy84, hu84⟩ := hWchain
  have hread : readCell env input_var_alpha = input_alpha := h_input
  have hPW : ∀ w : Fin 85,
      env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point w.val
            (input_alpha.val / 2 ^ (3 * w.val) % 8)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point w.val
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
    rcases Nat.lt_or_ge wv 84 with h84 | h84
    · obtain ⟨hxw, hyw, huw, -⟩ := hLoopW ⟨wv - 2, by omega⟩
      rw [show offset + 2 + (wv - 2) = offset + wv from by omega,
        show wv - 2 + 2 = wv from by omega] at hxw hyw huw
      rw [hxw, hyw, huw,
        ofFn8_get_windowVal _ env input_var_alpha wv input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha wv input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha wv input_alpha hread]
      exact ⟨rfl, rfl, rfl⟩
    · rw [show wv = 84 from by omega]
      rw [hx84, hy84, hu84,
        ofFn8_get_windowVal _ env input_var_alpha 84 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 84 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 84 input_alpha hread]
      exact ⟨rfl, rfl, rfl⟩
  exact hPW

set_option linter.all false in
/-- Completeness of the window chain (standalone): each incomplete addition's
constraints from its completeness leaf, on the honest partialSum ladder. -/
private theorem inner_completeness_chain (B : FixedBase) (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (input_var_alpha : AssignedCell Fp) (input_alpha : Fp)
    (h_input : env.env.get input_var_alpha.cell.column
      ((env.place input_var_alpha.cell.regionIndex
        + input_var_alpha.cell.rowOffset : ℕ) : ℤ) = input_alpha)
    (hWfix : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.fixedConstantsLoop (MulFixed.coordsGate cfg.superConfig) B.toData
        cfg.superConfig offset 85).operations self))
    (hWchain : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.windowChain cfg.superConfig
        (MulFixed.processWindow B.toData (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.toData.point) cfg.superConfig input_var_alpha) offset
        85).operations self))
    (hZW : cfg.superConfig.runningSumConfig.z = cfg.superConfig.window)
    (hXPeq : cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP)
    (hYPeq : cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP)
    (hZs : ∀ w : Fin 86, env.env.advice cfg.superConfig.window
        ((env.place self + (offset + w.val) : ℕ) : ℤ)
      = ((input_alpha.val / 2 ^ (3 * w.val) : ℕ) : Fp)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((MulFixed.windowChain cfg.superConfig
        (MulFixed.processWindow B.toData (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.toData.point) cfg.superConfig input_var_alpha) offset
        85).operations self) ∧
    (env.env.advice cfg.superConfig.addIncompleteConfig.xQR
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.partialSum
          (fun t => input_alpha.val / 2 ^ (3 * t) % 8) 83 • B.point).x ∧
     env.env.advice cfg.superConfig.addIncompleteConfig.yQR
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.partialSum
          (fun t => input_alpha.val / 2 ^ (3 * t) % 8) 83 • B.point).y ∧
     env.env.advice cfg.superConfig.addConfig.xP
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point 84
          (input_alpha.val / 2 ^ (3 * 84) % 8)).x ∧
     env.env.advice cfg.superConfig.addConfig.yP
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point 84
          (input_alpha.val / 2 ^ (3 * 84) % 8)).y) := by
  have hPW := inner_windows_honest B cfg offset self env input_var_alpha input_alpha
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
  -- honest accumulator invariant via the shared ladder (`MulFixed.chain_ladder`)
  have hLadder := MulFixed.chain_ladder B.point B.onCurve 85 (by norm_num)
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
  have hInv : ∀ j : ℕ, 1 ≤ j → j ≤ 83 →
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
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.partialSum
          (fun t => input_alpha.val / 2 ^ (3 * t) % 8) 83 • B.point).x ∧
      env.env.advice cfg.superConfig.addIncompleteConfig.yQR
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.partialSum
          (fun t => input_alpha.val / 2 ^ (3 * t) % 8) 83 • B.point).y ∧
      env.env.advice cfg.superConfig.addConfig.xP
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point 84
          (input_alpha.val / 2 ^ (3 * 84) % 8)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
        ((env.place self + (offset + 84) : ℕ) : ℤ)
      = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point 84
          (input_alpha.val / 2 ^ (3 * 84) % 8)).y := by
    have h83 := hInv 83 (by norm_num) le_rfl
    rw [show offset + 83 + 1 = offset + 84 from by omega] at h83
    obtain ⟨hx84, hy84, -⟩ := hPW ⟨84, by norm_num⟩
    rw [show ((⟨84, by norm_num⟩ : Fin 85) : ℕ) = 84 from rfl] at hx84 hy84
    exact ⟨h83.1, h83.2, hx84, hy84⟩
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
    rw [show ((⟨1, by norm_num⟩ : Fin 85) : ℕ) = 1 from rfl] at hp1x hp1y
    rw [show ((⟨0, by norm_num⟩ : Fin 85) : ℕ) = 0 from rfl,
      show offset + 0 = offset from by omega] at hp0x hp0y
    obtain ⟨t1, ht1_def⟩ : ∃ t : ℕ, t = (Halo2.Ironwood.Ecc.MulFixed.windowScalar 1
      (input_alpha.val / 2 ^ (3 * 1) % 8)).val := ⟨_, rfl⟩
    obtain ⟨s0, hs0_def⟩ : ∃ t : ℕ, t = (Halo2.Ironwood.Ecc.MulFixed.windowScalar 0
      (input_alpha.val / 2 ^ (3 * 0) % 8)).val := ⟨_, rfl⟩
    have ht1 : t1 = (input_alpha.val / 2 ^ (3 * 1) % 8 + 2) * 8 ^ 1 := by
      rw [ht1_def]
      exact Halo2.Ironwood.Ecc.MulFixed.windowScalar_val (by norm_num) (hks_lt 1)
    have hs0 : s0 = (input_alpha.val / 2 ^ (3 * 0) % 8 + 2) * 8 ^ 0 := by
      rw [hs0_def]
      exact Halo2.Ironwood.Ecc.MulFixed.windowScalar_val (by norm_num) (hks_lt 0)
    have hwp1 : Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point 1
        (input_alpha.val / 2 ^ (3 * 1) % 8) = t1 • B.point := by rw [ht1_def]; rfl
    have hwp0 : Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point 0
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
    rw [show ((⟨i.val + 2, by omega⟩ : Fin 85) : ℕ) = i.val + 2 from rfl,
      show offset + (i.val + 2) = offset + 2 + i.val from by omega] at hpx hpy
    have hih := hInv (i.val + 1) (by omega) (by omega)
    rw [show offset + (i.val + 1) + 1 = offset + 2 + i.val from by omega] at hih
    obtain ⟨t, ht_def⟩ : ∃ t : ℕ,
        t = (Halo2.Ironwood.Ecc.MulFixed.windowScalar (i.val + 2)
          (input_alpha.val / 2 ^ (3 * (i.val + 2)) % 8)).val := ⟨_, rfl⟩
    obtain ⟨S, hS_def⟩ : ∃ S : ℕ,
        S = Halo2.Ironwood.Ecc.MulFixed.partialSum
          (fun t => input_alpha.val / 2 ^ (3 * t) % 8) (i.val + 1) := ⟨_, rfl⟩
    have hval : t = (input_alpha.val / 2 ^ (3 * (i.val + 2)) % 8 + 2) * 8 ^ (i.val + 2) := by
      rw [ht_def]
      exact Halo2.Ironwood.Ecc.MulFixed.windowScalar_val (by omega) (hks_lt _)
    have hwp : Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point (i.val + 2)
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
private theorem inner_completeness_fixed (B : FixedBase) (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (input_var_alpha : AssignedCell Fp) (input_alpha : Fp)
    (h_input : env.env.get input_var_alpha.cell.column
      ((env.place input_var_alpha.cell.regionIndex
        + input_var_alpha.cell.rowOffset : ℕ) : ℤ) = input_alpha)
    (hWfix : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.fixedConstantsLoop (MulFixed.coordsGate cfg.superConfig) B.toData
        cfg.superConfig offset 85).operations self))
    (hWchain : RegionOperations.ExtendsWitnesses env.place self env.env
      ((MulFixed.windowChain cfg.superConfig
        (MulFixed.processWindow B.toData (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.toData.point) cfg.superConfig input_var_alpha) offset
        85).operations self))
    (hZW : cfg.superConfig.runningSumConfig.z = cfg.superConfig.window)
    (hXPeq : cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP)
    (hYPeq : cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP)
    (hZs : ∀ w : Fin 86, env.env.advice cfg.superConfig.window
        ((env.place self + (offset + w.val) : ℕ) : ℤ)
      = ((input_alpha.val / 2 ^ (3 * w.val) : ℕ) : Fp)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((MulFixed.fixedConstantsLoop (MulFixed.coordsGate cfg.superConfig) B.toData
        cfg.superConfig offset 85).operations self) := by
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
  obtain ⟨hx0, hy0, hu0, hx1, hy1, hu1, _hAW1, hLoopW, hx84, hy84, hu84⟩ := hWchain
  have hread : readCell env input_var_alpha = input_alpha := h_input
  have hPW : ∀ w : Fin 85,
      env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point w.val
            (input_alpha.val / 2 ^ (3 * w.val) % 8)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point w.val
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
    rcases Nat.lt_or_ge wv 84 with h84 | h84
    · obtain ⟨hxw, hyw, huw, -⟩ := hLoopW ⟨wv - 2, by omega⟩
      rw [show offset + 2 + (wv - 2) = offset + wv from by omega,
        show wv - 2 + 2 = wv from by omega] at hxw hyw huw
      rw [hxw, hyw, huw,
        ofFn8_get_windowVal _ env input_var_alpha wv input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha wv input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha wv input_alpha hread]
      exact ⟨rfl, rfl, rfl⟩
    · rw [show wv = 84 from by omega]
      rw [hx84, hy84, hu84,
        ofFn8_get_windowVal _ env input_var_alpha 84 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 84 input_alpha hread,
        ofFn8_get_windowVal _ env input_var_alpha 84 input_alpha hread]
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
private theorem inner_completeness_dec (cfg : Config) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp)
    (input_var_alpha : AssignedCell Fp) (input_alpha : Fp)
    (h_input : env.env.get input_var_alpha.cell.column
      ((env.place input_var_alpha.cell.regionIndex
        + input_var_alpha.cell.rowOffset : ℕ) : ℤ) = input_alpha)
    (hPA : input_alpha.val < 2 ^ 255)
    (hWdec : RegionOperations.ExtendsWitnesses env.place self env.env
      (((Halo2.Ironwood.DecomposeRunningSum.copyDecompose 3 85).call
        cfg.superConfig.runningSumConfig offset
        { alpha := input_var_alpha }).operations self)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      (((Halo2.Ironwood.DecomposeRunningSum.copyDecompose 3 85).call
        cfg.superConfig.runningSumConfig offset
        { alpha := input_var_alpha }).operations self) ∧
    ∀ w : Fin 86, env.env.advice cfg.superConfig.runningSumConfig.z
        ((env.place self + (offset + w.val) : ℕ) : ℤ)
      = ((input_alpha.val / 2 ^ (3 * w.val) : ℕ) : Fp) := by
  have hDecC := Halo2.SubcircuitRw.region_completeness_leaf_placed
    (Halo2.Ironwood.DecomposeRunningSum.copyDecompose 3 85)
    cfg.superConfig.runningSumConfig offset self env { alpha := input_var_alpha } hWdec
  have hDecS := Halo2.SubcircuitRw.region_completeness_derived_placed
    (Halo2.Ironwood.DecomposeRunningSum.copyDecompose 3 85)
    cfg.superConfig.runningSumConfig offset self env { alpha := input_var_alpha } hWdec
  simp only [dec_spec_eq, dec_assumptions_eq, dec_envAssumptions_eq,
    dec_proverAssumptions_eq, dec_proverSpec_eq,
    Halo2.Ironwood.DecomposeRunningSum.copyDecompose_output, circuit_norm]
    at hDecC hDecS
  have hPA' : (env.env.get input_var_alpha.cell.column
      ((env.place input_var_alpha.cell.regionIndex
        + input_var_alpha.cell.rowOffset : ℕ) : ℤ)).val < 2 ^ (3 * 85) := by
    rw [h_input]
    exact lt_of_lt_of_le hPA (by norm_num)
  refine And.intro (hDecC hPA') ?_
  have hZs := (hDecS hPA').2
  simp only [h_input] at hZs
  exact hZs

/-- The inner bundle's completeness, standalone (its own declaration/heartbeat budget —
the shared-budget split). -/
private theorem inner_completeness (B : FixedBase) (cfg : Config) (offset : ℕ) :
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
    simp only [innerRegion, RegionCircuit.operations_bind,
      RegionOperations.constraints_append, RegionOperations.extendsWitnesses_append]
      at hwit ⊢
    obtain ⟨hWdec, hWfix, hWchain, -⟩ := hwit
    obtain ⟨hZW, hXPeq, hYPeq⟩ := _hE
    have hDC := inner_completeness_dec cfg offset self env input_var_alpha input_alpha
      h_input hPA hWdec
    have hZs : ∀ w : Fin 86, env.env.advice cfg.superConfig.window
        ((env.place self + (offset + w.val) : ℕ) : ℤ)
      = ((input_alpha.val / 2 ^ (3 * w.val) : ℕ) : Fp) := by
      rw [← hZW]
      exact hDC.2
    refine And.intro (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))) ?_
    · with_reducible exact hDC.1
    · with_reducible
        exact inner_completeness_fixed B cfg offset self env input_var_alpha
          input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs
    · with_reducible
        exact (inner_completeness_chain B cfg offset self env input_var_alpha
          input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs).1
    · rw [RegionCircuit.operations_pure]
      exact trivial
    · -- the honest-prover contract (`InnerProverSpec`)
      simp only [InnerProverSpec]
      rw [ElaboratedRegionCircuit.output_eq, innerRegion_output] at h_output
      provable_type_simp
      obtain ⟨⟨hOax, hOay⟩, ⟨hOmx, hOmy⟩, hOzs⟩ := h_output
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [← hOax]
        with_reducible exact (inner_completeness_chain B cfg offset self env
          input_var_alpha input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs).2.1
      · rw [← hOay]
        with_reducible exact (inner_completeness_chain B cfg offset self env
          input_var_alpha input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs).2.2.1
      · rw [← hOmx]
        with_reducible exact (inner_completeness_chain B cfg offset self env
          input_var_alpha input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs).2.2.2.1
      · rw [← hOmy]
        with_reducible exact (inner_completeness_chain B cfg offset self env
          input_var_alpha input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs).2.2.2.2
      · intro w
        rw [← congrArg (fun v => v[w.val]'w.isLt) hOzs]
        simp only [circuit_norm]
        exact hDC.2 w

set_option linter.constructorNameAsVariable false in
/-- The inner-region bundle: `innerRegion` with its soundness/completeness contract. -/
def inner (B : FixedBase) : FormalRegionCircuit Fp Config Config
    Halo2.Ironwood.DecomposeRunningSum.Inputs InnerOut where
  configure := pure

  synthesize cfg offset (input : Halo2.Ironwood.DecomposeRunningSum.Inputs
      (AssignedCell Fp)) :=
    innerRegion B.toData cfg offset input.alpha

  Assumptions _ := True

  EnvAssumptions := InnerEnvAssumptions

  Spec := InnerSpec B

  ProverAssumptions := InnerProverAssumptions

  soundness := by
    -- PROOF ARC recipe (per Mul.lean): NO structural unfolds in the list (innerRegion
    -- at h_output/goal whnf-cliffs); contract defs only.
    circuit_proof_start [InnerSpec, InnerEnvAssumptions, InnerProverAssumptions]
    obtain ⟨env, rfl, rfl⟩ :
        ∃ pe : Placed Environment Fp, pe.place = place ∧ pe.env = env :=
      ⟨⟨place, env⟩, rfl, rfl⟩
    simp only [innerRegion, RegionCircuit.operations_bind,
      RegionOperations.constraints_append] at hc
    obtain ⟨hDec, hFixed, hChain, -⟩ := hc
    subcircuit_rw at hDec
    simp only [dec_spec_eq, dec_assumptions_eq, dec_envAssumptions_eq] at hDec
    -- output projections (lazy)
    rw [ElaboratedRegionCircuit.output_eq, innerRegion_output] at h_output
    provable_type_simp
    -- the decompose spec, landed on cells
    simp only [Halo2.Ironwood.DecomposeRunningSum.copyDecompose_output, circuit_norm] at hDec
    obtain ⟨V, hVlt, hAlphaV, hZs⟩ := hDec
    obtain ⟨⟨hOax, hOay⟩, ⟨hOmx, hOmy⟩, hOzs⟩ := h_output
    -- ── the digit sequence and its reconstruction ──
    have hVlt' : V < 8 ^ 85 := by
      have : (2 : ℕ) ^ (3 * 85) = 8 ^ 85 := by rw [pow_mul]; norm_num
      omega
    have hSum : (∑ j ∈ Finset.range 85, V / 2 ^ (3 * j) % 8 * 8 ^ j) = V := by
      have hstep : ∀ j, V / 2 ^ (3 * j) % 8 * 8 ^ j = V / 8 ^ j % 8 * 8 ^ j := by
        intro j
        rw [pow_mul]
        norm_num
      calc (∑ j ∈ Finset.range 85, V / 2 ^ (3 * j) % 8 * 8 ^ j)
          = ∑ j ∈ Finset.range 85, V / 8 ^ j % 8 * 8 ^ j :=
            Finset.sum_congr rfl (fun j _ => hstep j)
        _ = V % 8 ^ 85 := Halo2.Ironwood.Ecc.MulFixed.sum_base8 V 85
        _ = V := Nat.mod_eq_of_lt hVlt'
    -- ── the per-row window points (the coords rows), generalized over the window ──
    simp only [MulFixed.fixedConstantsLoop, MulFixed.fixedConstantsWindow,
      MulFixed.coordsGate, MulFixed.coordsCheck, MulFixed.eval_interpolatedX,
      circuit_norm, mul_one, one_mul] at hFixed
    obtain ⟨hZW, hXPeq, hYPeq⟩ := _hE
    rw [hZW] at hZs
    have hWP : ∀ w : Fin 85,
        env.env.advice cfg.superConfig.addConfig.xP
            ((env.place self + (offset + w.val) : ℕ) : ℤ)
          = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point w.val (V / 2 ^ (3 * w.val) % 8)).x ∧
        env.env.advice cfg.superConfig.addConfig.yP
            ((env.place self + (offset + w.val) : ℕ) : ℤ)
          = (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point w.val (V / 2 ^ (3 * w.val) % 8)).y := by
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
    · -- α = ↑V (the digit sum)
      rw [hSum, ← h_input, hAlphaV]
    · -- acc = [partialSum ks 83]·B  (the window-chain ladder)
      simp only [MulFixed.windowChain, MulFixed.processWindow, circuit_norm,
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
      -- window points as nsmul, with scalar values
      have hks_lt : ∀ t, V / 2 ^ (3 * t) % 8 < 8 := fun t => Nat.mod_lt _ (by norm_num)
      -- ── the shared ladder (`MulFixed.chain_ladder`), at this region's reads ──
      have hLadder := MulFixed.chain_ladder B.point B.onCurve 85 (by norm_num)
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
      rcases hP : Halo2.Ironwood.Ecc.MulFixed.partialSum (fun t => V / 2 ^ (3 * t) % 8) 83
          • B.point with ⟨px, py⟩
      rw [hP] at hI83
      rw [hI83.1, hI83.2]
    · -- mulB = windowPoint 84 k₈₄  (the MSB coords row)
      obtain ⟨hwx, hwy⟩ := hWP ⟨84, by norm_num⟩
      rw [← hOmx, ← hOmy]
      rcases hW : Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point 84 (V / 2 ^ (3 * 84) % 8)
        with ⟨wx, wy⟩
      rw [show ((⟨84, by norm_num⟩ : Fin 85) : ℕ) = 84 from rfl, hW] at hwx hwy
      rw [hwx, hwy]
    · -- the running sums are the shifts of the digit sum
      intro w
      rw [hSum, ← congrArg (fun v => v[w.val]'w.isLt) hOzs]
      simp only [circuit_norm, hZW]
      exact hZs w

  completeness := fun cfg offset => inner_completeness B cfg offset

/-- The four layouter pieces in source order. Returns the result point `[α]B`. -/
def synthesize (B : FixedBaseData) (cfg : Config) (alpha : AssignedCell Fp) :
    Circuit Fp (Var Point Fp) := do
  -- 1. the incomplete-addition region
  let inn ←
    assignRegion "Base-field elem fixed-base mul (incomplete addition)"
      (innerRegion B cfg 0 alpha)
  let zs := inn.zs
  -- 2. the complete addition `mul_b + acc`
  let result ←
    assignRegion "Base-field elem fixed-base mul (complete addition)"
      (Add.add.call cfg.superConfig.addConfig 0 ⟨inn.mulB, inn.acc⟩)
  -- Rust binds `alpha := scalar.base_field_elem = running_sum[0]`: every downstream α
  -- reference — the canonicity copy AND the witness programs — uses the z_0 CELL, not
  -- the original α cell.
  let alphaZ0 := zs[0]
  -- 3. the 13-word lookup range check of α₀'
  let (alphaPrime, z13) ← witnessCheck13 cfg.lookupConfig (alphaZeroPrimeWit alphaZ0 zs[84])
  -- 4. the canonicity checks
  assignRegion "Canonicity checks"
    (canonicityRegion cfg alphaZ0 zs[84] alphaPrime z13 zs[44] zs[43])
  return result

/-! ## The gadget bundle (`FixedPointBaseField::mul`)

The layouter-level `FormalCircuit`: four regions (inner mul, complete addition, the
13-word witness check, the canonicity checks). -/

derive_contract_bridges addc := Halo2.Ironwood.Ecc.Add.add
derive_contract_bridges rca := Halo2.Ironwood.LookupRangeCheck.rangeCheckAt 10 13 false

/-- Env-level preconditions of the full gadget: the shared-config asserts consumed by the
inner region, the loaded 10-bit lookup table, and the lookup config's selector
distinctness (both consumed by the witness check). -/
def EnvAssumptions (cfg : Config) (env : Placed Environment Fp) : Prop :=
  InnerEnvAssumptions cfg env ∧
  LookupRangeCheck.TableLoaded 10 cfg.lookupConfig env.env ∧
  cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qRunning.index

/-- The gadget's semantic contract: the output is the fixed base scaled by the
base-field element α, embedded into the scalar field — full scalar multiplication,
canonical in α (that is what the canonicity checks buy). -/
def Spec (B : FixedBase) (alpha : Fp) (output : Point Fp) : Prop :=
  output = (alpha.val : Fq) • B

/-- The region count of `synthesize`: inner mul, complete addition, witness check,
canonicity checks. -/
private theorem synthesize_regionCount (B : FixedBaseData) (cfg : Config)
    (alpha : AssignedCell Fp) (i : RegionIndex) :
    Operations.regionCount ((synthesize B cfg alpha).operations i) = 4 := by
  simp only [synthesize, witnessCheck13, circuit_norm, operations_assignRegion,
    Operations.regionCount]

/-- The range-check chunk's output cells (positional `z0`/`z13`). -/
private theorem rca_output (cfgL : LookupRangeCheck.Config 10) (offset : ℕ)
    (self : RegionIndex) :
    (LookupRangeCheck.rangeCheckAt 10 13 false).output cfgL offset () self
      = { z0 := AssignedCell.of self offset cfgL.runningSum,
          zLast := AssignedCell.of self (offset + 13) cfgL.runningSum } := rfl

/-- The `zLast` output cell of the range-check chunk, through the `call` wrapper (the
`output_call` rewrite does not fire inside cell projections; this is its `rfl` fusion
with `rca_output`). -/
private theorem rca_call_zLast (cfgL : LookupRangeCheck.Config 10) (offset : ℕ)
    (self : RegionIndex) :
    (((LookupRangeCheck.rangeCheckAt 10 13 false).call cfgL offset ()).output self).zLast
      = AssignedCell.of self (offset + 13) cfgL.runningSum := by
  rw [FormalRegionCircuit.output_call, rca_output]

/-- The range-check chunk's extraction data: the positional element cell's value. -/
private theorem rca_extract (cfgL : LookupRangeCheck.Config 10) (offset : ℕ)
    (self : RegionIndex) (env : Placed Environment Fp) :
    (LookupRangeCheck.rangeCheckAt 10 13 false).extract cfgL offset () self env
      = env.env.advice cfgL.runningSum ((env.place self + offset : ℕ) : ℤ) := by
  show eval env (AssignedCell.of self offset cfgL.runningSum : Var field Fp) = _
  simp only [circuit_norm, AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice]

/-- The α₀' witness program's value (single-element vector, `rfl` tail). -/
private theorem alphaZeroPrimeWit_eval (env : Placed ProverEnvironment Fp)
    (alpha z84 : AssignedCell Fp) :
    ((alphaZeroPrimeWit alpha z84).eval env)[0]
      = readCell env alpha - readCell env z84 * ((2 ^ 252 : ℕ) : Fp)
        + ((2 ^ 130 : ℕ) : Fp) - tP := by
  simp only [alphaZeroPrimeWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- The eight canonicity-gate polynomial identities, value-level and context-free. -/
private theorem canon_gate_polys {row : Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.Gate.Input Fp}
    (hA1 : Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.Gate.IsAlpha1 row.alpha1)
    (hA2 : IsBool row.alpha2)
    (hDec : Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.Gate.DecomposesBaseFieldElem row)
    (hCanon : Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.Gate.CanonicalHighBit row) :
    row.alpha2 * row.alpha1 = 0 ∧
    row.alpha2 * (row.z44Alpha - row.z84Alpha * ((2 ^ 120 : ℕ) : Fp)) = 0 ∧
    row.alpha2 * Halo2.Ironwood.Utilities.RunningSum.rangeCheckPoly 2
      (row.z43Alpha - row.z44Alpha * 8) = 0 ∧
    row.alpha2 * row.z13Alpha0Prime = 0 ∧
    Halo2.Ironwood.Utilities.RunningSum.rangeCheckPoly 4 row.alpha1 = 0 ∧
    Halo2.Ironwood.Utilities.RunningSum.rangeCheckPoly 2 row.alpha2 = 0 ∧
    row.z84Alpha - (row.alpha1 + row.alpha2 * ((1 <<< 2 : ℕ) : Fp)) = 0 ∧
    row.alpha0Prime - (row.alpha - row.z84Alpha * ((2 ^ 252 : ℕ) : Fp)
      + ((2 ^ 130 : ℕ) : Fp) - tP) = 0 := by
  simp only [Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.Gate.IsAlpha1] at hA1
  simp only [IsBool] at hA2
  simp only [Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.Gate.CanonicalHighBit,
    Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.Gate.alpha0Hi120,
    Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.Gate.a43, IsBool] at hCanon
  obtain ⟨hDec84, hDecAP⟩ := hDec
  simp only [Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.Gate.alpha0] at hDecAP
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases hA2 with h0 | h1
    · rw [h0]; ring
    · rw [h1, (hCanon h1).1]; ring
  · rcases hA2 with h0 | h1
    · rw [h0]; ring
    · rw [h1, one_mul, show ((2 ^ 120 : ℕ) : Fp) = OfNat.ofNat (2 ^ 120) from by
        norm_num]
      exact (hCanon h1).2.1
  · rcases hA2 with h0 | h1
    · rw [h0]; ring
    · rw [h1, one_mul,
        Halo2.Ironwood.Utilities.RunningSum.rangeCheckPoly_eq_zero_iff,
        Halo2.Ironwood.DecomposeRunningSum.inRange_iff_exists_lt 2 (by norm_num)]
      rcases (hCanon h1).2.2.1 with hb0 | hb1
      · exact ⟨0, by norm_num, by rw [hb0]; norm_num⟩
      · exact ⟨1, by norm_num, by rw [hb1]; norm_num⟩
  · rcases hA2 with h0 | h1
    · rw [h0]; ring
    · rw [h1, (hCanon h1).2.2.2]; ring
  · rw [Halo2.Ironwood.Utilities.RunningSum.rangeCheckPoly_eq_zero_iff,
      Halo2.Ironwood.DecomposeRunningSum.inRange_iff_exists_lt 4 (by norm_num)]
    rcases hA1 with h | h | h | h
    · exact ⟨0, by norm_num, by rw [h]; norm_num⟩
    · exact ⟨1, by norm_num, by rw [h]; norm_num⟩
    · exact ⟨2, by norm_num, by rw [h]; norm_num⟩
    · exact ⟨3, by norm_num, by rw [h]; norm_num⟩
  · rw [Halo2.Ironwood.Utilities.RunningSum.rangeCheckPoly_eq_zero_iff,
      Halo2.Ironwood.DecomposeRunningSum.inRange_iff_exists_lt 2 (by norm_num)]
    rcases hA2 with h | h
    · exact ⟨0, by norm_num, by rw [h]; norm_num⟩
    · exact ⟨1, by norm_num, by rw [h]; norm_num⟩
  · rw [hDec84, show ((1 <<< 2 : ℕ) : Fp) = 4 from by norm_num [Nat.shiftLeft_eq]]
    ring
  · rw [hDecAP]
    push_cast [Halo2.Ironwood.tP]
    ring

/-- Rust `FixedPointBaseField::mul`: `[α]B` for a base-field element α, canonically. -/
def circuit (B : FixedBase) : FormalCircuit Fp
    ((Fin 3 → Column .advice) × LookupRangeCheck.Config 10 × MulFixed.Config)
    Config field Point where
  name := "fixed-base mul (base field elem)"

  configure := fun (canonAdvices, lookupConfig, superConfig) =>
    configure canonAdvices lookupConfig superConfig

  synthesize cfg alpha := synthesize B.toData cfg alpha

  elaborated cfg :=
    { output := fun alpha i => (synthesize B.toData cfg alpha).output i
      regionCount := fun _ => 4
      output_eq := by intro _ _; rfl
      regionCount_eq := fun alpha i => (synthesize_regionCount B.toData cfg alpha i).symm }

  EnvAssumptions := EnvAssumptions

  Assumptions _ := True

  Spec input output _ := Spec B input output

  ProverAssumptions _ _ _ := True

  ProverSpec _ _ _ _ := True

  soundness := by
    circuit_proof_start
    obtain ⟨env, rfl, rfl⟩ :
        ∃ pe : Placed Environment Fp, pe.place = place ∧ pe.env = env :=
      ⟨⟨place, env⟩, rfl, rfl⟩
    simp only [synthesize, witnessCheck13, circuit_norm] at hc
    obtain ⟨hInner, hAdd, hRC, hCanon⟩ := hc
    obtain ⟨hEI, hTable, hDistinct⟩ := _hE
    -- ── region 1: the inner windowed mul, consumed through the bundle's soundness ──
    have hIS := (inner B).soundness cfg 0 i₀ env ⟨input_var⟩ hEI trivial hInner
    have hIS' : InnerSpec B
        (eval env ({ alpha := input_var } :
          Var Halo2.Ironwood.DecomposeRunningSum.Inputs Fp))
        (eval env ((innerRegion B.toData cfg 0 input_var).output i₀)) () := hIS
    rw [innerRegion_output] at hIS'
    simp only [InnerSpec, circuit_norm] at hIS'
    obtain ⟨ks, hks_lt, hαV, hAcc, hMulB, hZs⟩ := hIS'
    -- ── region 2: the complete addition `mul_b + acc` ──
    subcircuit_rw at hAdd
    simp only [addc_spec_eq, addc_assumptions_eq, addc_envAssumptions_eq,
      innerRegion_output, circuit_norm] at hAdd
    simp only [synthesize, witnessCheck13, circuit_norm] at h_output
    -- ── region 3: the 13-word lookup range check of α₀' ──
    subcircuit_rw at hRC
    simp only [rca_spec_eq, rca_assumptions_eq, rca_envAssumptions_eq,
      circuit_norm] at hRC
    -- ── region 4: the canonicity checks (lazy zs-projection first) ──
    simp only [innerRegion_output_zs] at hCanon
    simp only [Vector.getElem_ofFn] at hCanon
    simp only [canonicityRegion, canonGate,
      Halo2.Ironwood.DecomposeRunningSum.eval_rangeCheckExpr,
      circuit_norm] at hCanon
    obtain ⟨⟨hG1, hG2, hG3, hG4, hG5, hG6, hG7, hG8⟩,
      hCpA, hCpZ84, hCpAP, hCpZ13, hCpZ44, hCpZ43⟩ := hCanon
    rw [rca_call_zLast] at hCpZ13
    simp only [AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
      Cell.of_column, Environment.get_advice, Nat.zero_add] at hCpZ13
    -- ── the range-check contract, landed on advice reads ──
    have hRCS := hRC ⟨hTable, hDistinct⟩
      ⟨by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD],
       by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]⟩
    simp only [rca_output, rca_extract, circuit_norm, AssignedCell.eval,
      AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
      Environment.get_advice] at hRCS
    obtain ⟨lo, hlo, htel⟩ := hRCS
    -- ── the running-sum cells feeding the canonicity gate, in `8^w` form ──
    set V := ∑ j ∈ Finset.range 85, ks j * 8 ^ j with hV
    have hz0V := hZs ⟨0, by norm_num⟩
    have hz84V := hZs ⟨84, by norm_num⟩
    have hz44V := hZs ⟨44, by norm_num⟩
    have hz43V := hZs ⟨43, by norm_num⟩
    rw [show ((⟨0, by norm_num⟩ : Fin 86) : ℕ) = 0 from rfl] at hz0V
    rw [show ((⟨84, by norm_num⟩ : Fin 86) : ℕ) = 84 from rfl,
      show (2:ℕ) ^ (3 * 84) = 8 ^ 84 from by rw [pow_mul]; norm_num] at hz84V
    rw [show ((⟨44, by norm_num⟩ : Fin 86) : ℕ) = 44 from rfl,
      show (2:ℕ) ^ (3 * 44) = 8 ^ 44 from by rw [pow_mul]; norm_num] at hz44V
    rw [show ((⟨43, by norm_num⟩ : Fin 86) : ℕ) = 43 from rfl,
      show (2:ℕ) ^ (3 * 43) = 8 ^ 43 from by rw [pow_mul]; norm_num] at hz43V
    simp only [Nat.add_zero, pow_zero, Nat.mul_zero, Nat.div_one] at hz0V
    rw [hz0V] at hCpA
    rw [hz84V] at hCpZ84
    rw [hz44V] at hCpZ44
    rw [hz43V] at hCpZ43
    -- ── the gate facts ──
    obtain ⟨a1n, ha1n_lt, ha1n⟩ :=
      (Halo2.Ironwood.DecomposeRunningSum.inRange_iff_exists_lt 4 (by norm_num) _).mp
        ((Halo2.Ironwood.Utilities.RunningSum.rangeCheckPoly_eq_zero_iff 4 _).mp hG5)
    obtain ⟨a2n, ha2n_lt, ha2n⟩ :=
      (Halo2.Ironwood.DecomposeRunningSum.inRange_iff_exists_lt 2 (by norm_num) _).mp
        ((Halo2.Ironwood.Utilities.RunningSum.rangeCheckPoly_eq_zero_iff 2 _).mp hG6)
    rw [sub_eq_zero] at hG7 hG8
    rw [hCpZ84, ha1n, ha2n,
      show ((1 <<< 2 : ℕ) : Fp) = ((4 : ℕ) : Fp) from by norm_num [Nat.shiftLeft_eq]] at hG7
    -- ── the crux: V is the canonical representative ──
    have hVlt : V < 8 ^ 85 :=
      Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.RunningSumMul.sum_lt_of_windows hks_lt
    set A0 : ℕ := V / 8 ^ 84 with hA0
    have hA0lt : A0 < 8 := by
      rw [hA0]
      rw [show (8 : ℕ) ^ 85 = 8 ^ 84 * 8 from by ring] at hVlt
      exact Nat.div_lt_of_lt_mul (by omega)
    set α0 : ℕ := V % 8 ^ 84 with hα0def
    have hα0lt : α0 < 2 ^ 252 := by
      rw [hα0def]
      exact lt_of_lt_of_le (Nat.mod_lt _ (by positivity)) (by norm_num)
    have hVsplit : V = α0 + A0 * 8 ^ 84 := by rw [hα0def, hA0]; omega
    have h884 : (8 : ℕ) ^ 84 = 2 ^ 252 := by norm_num
    have hVltp : V < PALLAS_BASE_CARD := by
      rw [Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.base_card_eq]
      rcases (by omega : a2n = 0 ∨ a2n = 1) with h20 | h21
      · -- α₂ = 0: the top window is a1n ≤ 3, so V < 2^254
        have hA0eq : A0 = a1n :=
          Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.RunningSumMul.natCast_inj_of_lt_8
            hA0lt (by omega) (by rw [hG7, h20]; norm_num)
        have hmul : A0 * 8 ^ 84 ≤ 3 * 2 ^ 252 := by
          rw [h884]
          exact Nat.mul_le_mul_right _ (by omega)
        rw [hVsplit]
        norm_num [Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.tPNat] at hα0lt ⊢
        omega
      · -- α₂ = 1: canonicity forces α0 < t_p
        rw [ha2n, h21] at hG1 hG2 hG4
        simp only [Nat.cast_one, one_mul] at hG1 hG2 hG4
        -- α₁ = 0, so the top window is exactly 4
        have ha1z : a1n = 0 :=
          Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.RunningSumMul.natCast_inj_of_lt_8
            (by omega) (by norm_num) (by rw [← ha1n, hG1]; norm_num)
        have hA04 : A0 = 4 :=
          Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.RunningSumMul.natCast_inj_of_lt_8
            hA0lt (by norm_num) (by rw [hG7, ha1z, h21]; norm_num)
        have hV254 : V = α0 + 2 ^ 254 := by
          rw [hVsplit, hA04, h884]
          norm_num
        -- `alpha0_hi_120 = 0` forces `α0 < 2^132`
        have h844 : (8 : ℕ) ^ 44 = 2 ^ 132 := by norm_num
        have hdiv44 : V / 8 ^ 44 = α0 / 2 ^ 132 + 2 ^ 122 := by
          rw [hV254, h844, show (2 : ℕ) ^ 254 = 2 ^ 122 * 2 ^ 132 from by ring,
            Nat.add_mul_div_right _ _ (by positivity)]
        rw [hCpZ44, hCpZ84, hdiv44, hA04] at hG2
        have hq0 : α0 / 2 ^ 132 = 0 := by
          have hcast : ((α0 / 2 ^ 132 : ℕ) : Fp) = 0 := by
            push_cast at hG2 ⊢
            linear_combination hG2
          have hlt : α0 / 2 ^ 132 < PALLAS_BASE_CARD := by
            have : α0 / 2 ^ 132 < 2 ^ 120 := Nat.div_lt_of_lt_mul
              (by rw [show 2 ^ 132 * 2 ^ 120 = 2 ^ 252 from by ring]; omega)
            rw [Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.base_card_eq]
            norm_num [Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.tPNat] at this ⊢
            omega
          exact Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ _).mp hcast) hlt
        have hα0lt132 : α0 < 2 ^ 132 := by
          rcases Nat.div_eq_zero_iff.mp hq0 with h | h
          · norm_num at h
          · exact h
        -- the 13-word lookup on α₀' forces α0 < t_p
        rw [hCpZ13] at hG4
        rw [hG4, mul_zero, _root_.add_zero] at htel
        rw [show (10 * 13 : ℕ) = 130 from by norm_num] at hlo
        rw [← hCpAP, hG8, hCpA, hCpZ84, hA04] at htel
        have hfield : (lo : Fp) = (α0 : Fp) + (2 : Fp) ^ 130
            - ((Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.tPNat : ℕ) : Fp) := by
          rw [← htel, hV254]
          push_cast [Halo2.Ironwood.tP, Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.tPNat]
          ring
        have hα0tp : α0 < Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.tPNat :=
          Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.alpha0_lt_tp hlo hα0lt132 hfield
        rw [hV254]
        omega
    have hinput : input = ((V : ℕ) : Fp) := by
      rw [← h_input]
      simp only [circuit_norm]
      exact hαV
    -- ── the output value: `mul_b + acc = [V]B` ──
    obtain ⟨t84, ht84_def⟩ : ∃ t : ℕ,
        t = (Halo2.Ironwood.Ecc.MulFixed.windowScalar 84 (ks 84)).val := ⟨_, rfl⟩
    have hwp84 : Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point 84 (ks 84) = t84 • B.point := by
      rw [ht84_def]; rfl
    obtain ⟨S83, hS83_def⟩ : ∃ S : ℕ, S = Halo2.Ironwood.Ecc.MulFixed.partialSum ks 83 := ⟨_, rfl⟩
    have hS83_lt : S83 < 2 * 8 ^ 84 := by
      rw [hS83_def]
      exact Halo2.Ironwood.Ecc.MulFixed.partialSum_lt _ 83 (fun j hj => hks_lt j (by omega))
    have hS83_pos : 0 < S83 := by
      rw [hS83_def]
      exact Halo2.Ironwood.Ecc.MulFixed.partialSum_pos _ _
    have hS83_card : S83 < PALLAS_SCALAR_CARD :=
      Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.RunningSumMul.inv_lt_card hS83_lt (by norm_num)
    have hOnP : (t84 • B.point).OnCurve := by
      rw [← hwp84]
      exact B.windowPoint_onCurve (hks_lt 84 (by norm_num))
    have hOnQ : (S83 • B.point).OnCurve := B.nsmul_onCurve hS83_pos hS83_card
    obtain ⟨-, hOutEq⟩ := hAdd ⟨by rw [hMulB, hwp84]; exact Or.inl hOnP,
      by rw [hAcc, ← hS83_def]; exact Or.inl hOnQ⟩
    rw [hMulB, hAcc, hwp84, ← hS83_def,
      show (⟨env.place, env.env⟩ : Placed Environment Fp) = env from rfl] at hOutEq
    simp only [innerRegion_output_mulB, innerRegion_output_acc, Nat.zero_add,
      circuit_norm] at h_output
    rw [FormalRegionCircuit.output_call] at h_output
    rw [h_output] at hOutEq
    rw [Halo2.Ironwood.Point.nsmul_add_nsmul B.onCurve] at hOutEq
    -- (t84 + S83) • B = [(V : Fq).val] • B = the Spec's scalar mul
    have hchain : (t84 + S83) • B.point = ((V : Fq)).val • B.point := by
      rw [ht84_def, hS83_def, ← Halo2.Ironwood.Ecc.MulFixed.FixedBase.add_natCast_val_nsmul,
        Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.RunningSumMul.windowScalar_partialSum]
    simp only [Spec]
    rw [hinput, ZMod.val_natCast, Nat.mod_eq_of_lt hVltp, hOutEq, hchain]
    exact (point_eta _).symm

  completeness := by
    circuit_proof_start
    obtain ⟨env, rfl, rfl⟩ :
        ∃ pe : Placed ProverEnvironment Fp, pe.place = place ∧ pe.env = env :=
      ⟨⟨place, env⟩, rfl, rfl⟩
    simp only [synthesize, witnessCheck13, circuit_norm] at hwit ⊢
    obtain ⟨hWInner, hWAdd, ⟨hWap, hWrc⟩, hWCanon⟩ := hwit
    obtain ⟨hEI, hTable, hDistinct⟩ := _hE
    -- every base-field element fits 255 bits (the inner honest-prover precondition)
    have hval255 : ∀ x : Fp, x.val < 2 ^ 255 := fun x =>
      lt_of_lt_of_le (ZMod.val_lt x)
        (by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD])
    -- the inner bundle's honest-prover facts (exit accumulator/MSB, running sums)
    have hIPS : InnerProverSpec B
        (eval env ({ alpha := input_var } :
          Var Halo2.Ironwood.DecomposeRunningSum.Inputs Fp))
        (eval env ((innerRegion B.toData cfg 0 input_var).output i₀))
        default env.env.hint :=
      ((inner B).completeness cfg 0 i₀ env ⟨input_var⟩ hWInner hEI
        trivial (hval255 _)).2
    simp only [InnerProverSpec, innerRegion_output, circuit_norm] at hIPS
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ((inner B).completeness cfg 0 i₀ env ⟨input_var⟩ hWInner hEI
        trivial (hval255 _)).1
    · -- the complete addition `mul_b + acc` on the honest exit points
      have hks_lt : ∀ t : ℕ, ZMod.val (env.env.get input_var.cell.column
            ((env.place input_var.cell.regionIndex
              + input_var.cell.rowOffset : ℕ) : ℤ)) / 2 ^ (3 * t) % 8 < 8 :=
        fun t => Nat.mod_lt _ (by norm_num)
      obtain ⟨hax, hay, hmx, hmy, -⟩ := hIPS
      have hC := Halo2.SubcircuitRw.region_completeness_leaf_placed Add.add
        cfg.superConfig.addConfig 0 (i₀ + 1) env
        ⟨((innerRegion B.toData cfg 0 input_var).output i₀).mulB,
         ((innerRegion B.toData cfg 0 input_var).output i₀).acc⟩ hWAdd
      simp only [addc_assumptions_eq, addc_envAssumptions_eq,
        addc_proverAssumptions_eq, innerRegion_output_mulB, innerRegion_output_acc,
        Nat.zero_add, circuit_norm] at hC
      refine hC ⟨?_, ?_⟩
      · have hOn : (Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point 84
            (ZMod.val (env.env.get input_var.cell.column
              ((env.place input_var.cell.regionIndex
                + input_var.cell.rowOffset : ℕ) : ℤ)) / 2 ^ (3 * 84) % 8)).OnCurve :=
          B.windowPoint_onCurve (hks_lt 84)
        rcases hWp : Halo2.Ironwood.Ecc.MulFixed.windowPoint B.point 84
            (ZMod.val (env.env.get input_var.cell.column
              ((env.place input_var.cell.regionIndex
                + input_var.cell.rowOffset : ℕ) : ℤ)) / 2 ^ (3 * 84) % 8) with ⟨wx, wy⟩
        rw [hWp] at hOn hmx hmy
        rw [hmx, hmy]
        exact Or.inl hOn
      · have hOn : ((Halo2.Ironwood.Ecc.MulFixed.partialSum
            (fun t => ZMod.val (env.env.get input_var.cell.column
              ((env.place input_var.cell.regionIndex
                + input_var.cell.rowOffset : ℕ) : ℤ)) / 2 ^ (3 * t) % 8) 83
            • B.point)).OnCurve :=
          B.nsmul_onCurve (Halo2.Ironwood.Ecc.MulFixed.partialSum_pos _ _)
            (Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.RunningSumMul.inv_lt_card
              (Halo2.Ironwood.Ecc.MulFixed.partialSum_lt _ 83 (fun j _ => hks_lt j))
              (by norm_num))
        rcases hSp : Halo2.Ironwood.Ecc.MulFixed.partialSum
            (fun t => ZMod.val (env.env.get input_var.cell.column
              ((env.place input_var.cell.regionIndex
                + input_var.cell.rowOffset : ℕ) : ℤ)) / 2 ^ (3 * t) % 8) 83
            • B.point with ⟨sx, sy⟩
        rw [hSp] at hOn hax hay
        rw [hax, hay]
        exact Or.inl hOn
    · -- the 13-word range check chunk
      have hC := Halo2.SubcircuitRw.region_completeness_leaf_placed
        (LookupRangeCheck.rangeCheckAt 10 13 false) cfg.lookupConfig 0 (i₀ + 2) env () hWrc
      simp only [rca_assumptions_eq, rca_envAssumptions_eq,
        rca_proverAssumptions_eq, circuit_norm] at hC
      exact hC ⟨⟨hTable, hDistinct⟩,
        by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD],
        by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]⟩
    · -- the canonicity region: copies by their witness clauses, the gate on the
      -- honest values (`honest_canon_spec` + `canon_gate_polys`)
      simp only [innerRegion_output_zs] at hWCanon ⊢
      simp only [Vector.getElem_ofFn] at hWCanon ⊢
      simp only [canonicityRegion, canonGate, alpha1Wit, alpha2Wit,
        Halo2.Ironwood.DecomposeRunningSum.eval_rangeCheckExpr, circuit_norm]
        at hWCanon ⊢
      obtain ⟨hWcA, hWcZ84, hWcAP, hWa1, hWa2, hWcZ13, hWcZ44, hWcZ43⟩ := hWCanon
      rw [rca_call_zLast] at hWcZ13
      simp only [AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
        Cell.of_column, Environment.get_advice, Nat.zero_add] at hWcZ13
      obtain ⟨-, -, -, -, hZs⟩ := hIPS
      -- the α₀' witness value, on the honest running sums
      simp only [innerRegion_output_zs, Vector.getElem_ofFn] at hWap
      rw [alphaZeroPrimeWit_eval] at hWap
      simp only [readCell_of, Nat.zero_add, Nat.add_zero] at hWap
      -- z13's honest value (the range-check chunk's honest contract)
      have hZL := Halo2.SubcircuitRw.region_completeness_derived_placed
        (LookupRangeCheck.rangeCheckAt 10 13 false) cfg.lookupConfig 0 (i₀ + 2) env () hWrc
      simp only [rca_spec_eq, rca_assumptions_eq, rca_envAssumptions_eq,
        rca_proverAssumptions_eq, rca_proverSpec_eq, rca_output, rca_extract,
        circuit_norm, AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
        Cell.of_rowOffset, Cell.of_column, Environment.get_advice, Nat.add_zero] at hZL
      obtain ⟨-, hzLast⟩ := hZL ⟨hTable, hDistinct⟩
        ⟨by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD],
         by norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]⟩
      rw [show (10 * 13 : ℕ) = 130 from by norm_num] at hzLast
      -- the honest running sums at 0/84/44/43, in `8^w` form
      have hz0 := hZs ⟨0, by norm_num⟩
      have hz84 := hZs ⟨84, by norm_num⟩
      have hz44 := hZs ⟨44, by norm_num⟩
      have hz43 := hZs ⟨43, by norm_num⟩
      rw [show ((⟨0, by norm_num⟩ : Fin 86) : ℕ) = 0 from rfl] at hz0
      rw [show ((⟨84, by norm_num⟩ : Fin 86) : ℕ) = 84 from rfl,
        show (2:ℕ) ^ (3 * 84) = 8 ^ 84 from by rw [pow_mul]; norm_num] at hz84
      rw [show ((⟨44, by norm_num⟩ : Fin 86) : ℕ) = 44 from rfl,
        show (2:ℕ) ^ (3 * 44) = 8 ^ 44 from by rw [pow_mul]; norm_num] at hz44
      rw [show ((⟨43, by norm_num⟩ : Fin 86) : ℕ) = 43 from rfl,
        show (2:ℕ) ^ (3 * 43) = 8 ^ 43 from by rw [pow_mul]; norm_num] at hz43
      simp only [Nat.add_zero, Nat.mul_zero, pow_zero, Nat.div_one] at hz0
      -- the α value: `z_0 = α` (the copied base-field element)
      obtain ⟨A, hA_def⟩ : ∃ a : Fp, a = env.env.get input_var.cell.column
          ((env.place input_var.cell.regionIndex
            + input_var.cell.rowOffset : ℕ) : ℤ) := ⟨_, rfl⟩
      rw [← hA_def] at hz0 hz84 hz44 hz43
      have hz0A : env.env.advice cfg.superConfig.runningSumConfig.z
          ((env.place i₀ : ℕ) : ℤ) = A := hz0.trans (ZMod.natCast_zmod_val A)
      -- the gate-row facts (`honest_canon_spec` hypotheses)
      rw [hz0A] at hWa1 hWa2 hWap
      rw [hz84] at hWap
      rw [show (2:ℕ) ^ 252 = 8 ^ 84 from by norm_num] at hWa1
      have hdiv2 : A.val / 2 ^ 254 % 2 = A.val / 8 ^ 84 / 4 := by
        rw [Nat.div_div_eq_div_mul, show (8:ℕ) ^ 84 * 4 = 2 ^ 254 from by norm_num]
        exact Nat.mod_eq_of_lt
          (Nat.div_lt_of_lt_mul (lt_of_lt_of_le (hval255 A) (by norm_num)))
      rw [hdiv2] at hWa2
      have hap : env.env.advice (cfg.canonAdvices 0)
            ((env.place (i₀ + 1 + 2) + 1 : ℕ) : ℤ)
          = A - ((A.val / 8 ^ 84 : ℕ) : Fp) * (2:Fp) ^ 252 + (2:Fp) ^ 130
            - ((Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.tPNat : ℕ) : Fp) := by
        rw [hWcAP, hWap]
        push_cast [Halo2.Ironwood.tP, Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.tPNat]
        ring
      have hz13row : env.env.advice (cfg.canonAdvices 0)
            ((env.place (i₀ + 1 + 2) + 2 : ℕ) : ℤ)
          = ((((env.env.advice (cfg.canonAdvices 0)
              ((env.place (i₀ + 1 + 2) + 1 : ℕ) : ℤ)).val / 2 ^ 130 : ℕ)) : Fp) := by
        rw [hWcZ13, hzLast, hWcAP]
      obtain ⟨hDecR, hCanonR⟩ := Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.honest_canon_spec
        (row := { alpha := env.env.advice (cfg.canonAdvices 0)
                    ((env.place (i₀ + 1 + 2) : ℕ) : ℤ),
                  z84Alpha := env.env.advice (cfg.canonAdvices 2)
                    ((env.place (i₀ + 1 + 2) : ℕ) : ℤ),
                  alpha1 := env.env.advice (cfg.canonAdvices 1)
                    ((env.place (i₀ + 1 + 2) + 1 : ℕ) : ℤ),
                  alpha2 := env.env.advice (cfg.canonAdvices 2)
                    ((env.place (i₀ + 1 + 2) + 1 : ℕ) : ℤ),
                  alpha0Prime := env.env.advice (cfg.canonAdvices 0)
                    ((env.place (i₀ + 1 + 2) + 1 : ℕ) : ℤ),
                  z13Alpha0Prime := env.env.advice (cfg.canonAdvices 0)
                    ((env.place (i₀ + 1 + 2) + 2 : ℕ) : ℤ),
                  z44Alpha := env.env.advice (cfg.canonAdvices 1)
                    ((env.place (i₀ + 1 + 2) + 2 : ℕ) : ℤ),
                  z43Alpha := env.env.advice (cfg.canonAdvices 2)
                    ((env.place (i₀ + 1 + 2) + 2 : ℕ) : ℤ) })
        (α := A) (ZMod.val_lt A)
        (hWcA.trans hz0A) (hWcZ84.trans hz84) hWa1 hWa2 hap
        (hWcZ44.trans hz44) (hWcZ43.trans hz43) hz13row
      -- α₁ ∈ {0..3}, α₂ boolean (the honest witnessed top bits)
      have hA1 : Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.Gate.IsAlpha1
          (((A.val / 8 ^ 84 % 4 : ℕ) : Fp)) := by
        have hlt : A.val / 8 ^ 84 % 4 < 4 := Nat.mod_lt _ (by norm_num)
        obtain ⟨m, hm_def⟩ : ∃ m, m = A.val / 8 ^ 84 % 4 := ⟨_, rfl⟩
        rw [← hm_def]
        rw [← hm_def] at hlt
        interval_cases m <;>
          simp [Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem.Gate.IsAlpha1]
      have hA2 : IsBool (((A.val / 8 ^ 84 / 4 : ℕ) : Fp)) := by
        have hlt : A.val / 8 ^ 84 / 4 < 2 := by
          rw [Nat.div_div_eq_div_mul, show (8:ℕ) ^ 84 * 4 = 2 ^ 254 from by norm_num]
          exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le (hval255 A) (by norm_num))
        obtain ⟨m, hm_def⟩ : ∃ m, m = A.val / 8 ^ 84 / 4 := ⟨_, rfl⟩
        rw [← hm_def]
        rw [← hm_def] at hlt
        interval_cases m <;> simp [IsBool]
      rw [← hWa1] at hA1
      rw [← hWa2] at hA2
      have hPolys := canon_gate_polys hA1 hA2 hDecR hCanonR
      rw [rca_call_zLast]
      simp only [AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
        Cell.of_column, Environment.get_advice, Nat.zero_add]
      exact ⟨hPolys, hWcA, hWcZ84, hWcAP, hWcZ13, hWcZ44, hWcZ43⟩

end Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem
