import Clean.Ironwood.Ecc.MulFixed
import Clean.Ironwood.Utilities.LookupRangeCheck
import Clean.Orchard.Ecc.MulFixed.BaseFieldElem

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul_fixed/base_field_elem.rs`
(read in full) — fixed-base scalar multiplication by a base-field element
(gadget API `FixedPointBaseField::mul`), the NullifierK path of the Orchard circuit.

- `Config` (lines 20-29): the `q_mul_fixed_base_field` selector, the three
  `canon_advices`, the lookup config, and the shared `mul_fixed` super config.
- `configure` (lines 31-60): equality on the canon advices, the "Canonicity checks"
  gate (lines 62-163).
- `assign` (lines 165-378), four layouter pieces in order:
  1. region "Base-field elem fixed-base mul (incomplete addition)": the strict
     85-window running-sum `copy_decompose` of α, then the shared
     `assign_region_inner` (fixed constants + window-0 accumulator + the
     incomplete-addition window loop + the most significant window);
  2. region "Base-field elem fixed-base mul (complete addition)": `add(mul_b, acc)`;
  3. `witness_check(α₀' = α₀ + 2¹³⁰ − t_p, 13 words, strict = false)` — the
     "Witness element" region (`lookup_range_check.rs:142-162`);
  4. region "Canonicity checks": the three-row copy/witness block, gate at offset 1.

The proof-content donor is `Clean/Orchard/Ecc/MulFixed/BaseFieldElem.lean`
(`Gate` specs, `RunningSumMul` value algebra, the canonicity argument).
-/

-- The variable-name style linter whnf-walks the chunk-typed hypothesis statements of
-- the completeness helper theorems below and times out; disabled file-wide.
set_option linter.constructorNameAsVariable false

namespace Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem

open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Ecc.MulFixed (coordsGate fixedConstantsLoop processWindow)
open Halo2.Ironwood.DecomposeRunningSum (copyDecompose rangeCheckExpr)
open Orchard (Point pallasB tP)
open Orchard.Ecc.MulFixed (FixedBase)
open Halo2.Ironwood.Ecc.MulFixed (FixedBaseData)

/-- Rust `base_field_elem::Config` (lines 20-29). -/
structure Config where
  qMulFixedBaseField : Selector
  canonAdvices : Fin 3 → Column .advice
  lookupConfig : LookupRangeCheck.Config 10
  superConfig : MulFixed.Config

/-! ## The "Canonicity checks" gate (`base_field_elem.rs:62-163`)

Cell layout, relative to the gate row (selector at `Rotation::cur`, enabled at region
offset 1):

    |   canon_advices[0]  | canon_advices[1] | canon_advices[2] |
    -------------------------------------------------------------
    |          α          |                  |    z_84_alpha    |   ← Rotation::prev
    |     α_0_prime       |       α_1        |       α_2        |   ← Rotation::cur
    | z_13_alpha_0_prime  |    z_44_alpha    |    z_43_alpha    |   ← Rotation::next
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
    -- α_0 is derived, not witnessed (lines 76-79): α − z_84·2^252 (scale on the right)
    let alpha0 := alpha - z84Alpha * (((2 ^ 252 : ℕ) : Fp) : Expression Fp Query)
    let alpha1 : Expression Fp Query := queryAdvice (cfg.canonAdvices 1) 0
    let alpha2 : Expression Fp Query := queryAdvice (cfg.canonAdvices 2) 0
    let alpha0Prime : Expression Fp Query := queryAdvice (cfg.canonAdvices 0) 0
    let z13Alpha0Prime : Expression Fp Query := queryAdvice (cfg.canonAdvices 0) 1
    let z44Alpha : Expression Fp Query := queryAdvice (cfg.canonAdvices 1) 1
    let z43Alpha : Expression Fp Query := queryAdvice (cfg.canonAdvices 2) 1
    -- decomposition checks (lines 88-101)
    let alpha1RangeCheck := rangeCheckExpr 4 alpha1
    let alpha2RangeCheck := rangeCheckExpr 2 alpha2
    let z84AlphaCheck :=
      z84Alpha - (alpha1 + alpha2 * (((1 <<< 2 : ℕ) : Fp) : Expression Fp Query))
    -- α_0_prime = α_0 + 2^130 − t_p (lines 103-108)
    let alpha0PrimeCheck :=
      alpha0Prime - (alpha0 + (((2 ^ 130 : ℕ) : Fp) : Expression Fp Query)
        - ((tP : Fp) : Expression Fp Query))
    -- canonicity checks for MSB = 1 (lines 130-154)
    let alpha0Hi120 := z44Alpha - z84Alpha * (((2 ^ 120 : ℕ) : Fp) : Expression Fp Query)
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

/-- Rust `base_field_elem::Config::configure` (lines 31-60): equality on the three canon
advices, a fresh selector, the canonicity gate. (The canon-advice/incomplete-addition
column deconfliction assert, lines 49-55, holds by construction at the `EccChip` wiring:
canon = advices 6/7/8, add_incomplete = advices 0..3.) -/
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

/-! ## Synthesize (`base_field_elem.rs::assign`, lines 165-378) -/

/-- Output of the inner region: the exit accumulator (windows 0..83), the MSB window
point, and the running sums (`z_0 = α`; `z_43/z_44/z_84` feed the canonicity check). -/
structure InnerOut (F : Type) where
  acc : Point F
  mulB : Point F
  zs : Vector F 86
deriving ProvableStruct

/-- Region 1, "Base-field elem fixed-base mul (incomplete addition)" (lines 174-205):
the strict running-sum decomposition of α (85 3-bit windows over 255 bits), the fixed
constants, the window-0 accumulator, the incomplete-addition loop over windows 1..83,
and the most significant window 84. -/
def innerRegion (B : FixedBaseData) (cfg : Config) (offset : ℕ) (alpha : AssignedCell Fp) :
    RegionCircuit Fp (InnerOut (AssignedCell Fp)) := do
  -- scalar decomposition (lines 179-193): strict `copy_decompose`
  let zsOut ← (copyDecompose 3 85).call cfg.superConfig.runningSumConfig offset ⟨alpha⟩
  -- `assign_fixed_constants` (mul_fixed.rs:181, 195-252); the coords toggle is the
  -- running-sum selector's coords gate
  fixedConstantsLoop (coordsGate cfg.superConfig) B cfg.superConfig offset 85
  -- the shared window chain: init (window 0), incomplete additions (1..83), MSB (84)
  let r ← MulFixed.windowChain cfg.superConfig
    (processWindow B cfg.superConfig alpha) offset 85
  return { acc := r.1, mulB := r.2, zs := zsOut.zs }

/-- The honest `α₀' = (α − z_84·2^252) + 2^130 − t_p` witness, from the α and `z_84`
cells (`base_field_elem.rs:262-277`). -/
def alphaZeroPrimeWit (alpha z84 : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[readCell env alpha - readCell env z84 * ((2 ^ 252 : ℕ) : Fp)
      + ((2 ^ 130 : ℕ) : Fp) - tP]

/-- Rust `witness_check(value, 13, strict = false)` (`lookup_range_check.rs:142-162`):
the "Witness element" region — witness `z_0` from the given program at offset 0, then
the positional 13-round lookup range check (no strict tail). Returns `(z_0, z_13)` —
`α₀'` and its high tail, both copied into the canonicity check. -/
def witnessCheck13 (cfg : LookupRangeCheck.Config 10) (w : WitgenIR Fp 1) :
    Circuit Fp (AssignedCell Fp × AssignedCell Fp) :=
  assignRegion "Witness element" (do
    let z0 ← assignAdvice cfg.runningSum 0 w
    let out ← (LookupRangeCheck.rangeCheckAt 10 13 false).call cfg 0 ()
    return (z0, out.zLast))

/-- The honest `α_1 = α[252..=253]` witness (`bitrange_subset`, line 327). -/
def alpha1Wit (alpha : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[(((readCell env alpha).val / 2 ^ 252 % 4 : ℕ) : Fp)]

/-- The honest `α_2 = α[254]` witness (line 336). -/
def alpha2Wit (alpha : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[(((readCell env alpha).val / 2 ^ 254 % 2 : ℕ) : Fp)]

/-- Region 4, "Canonicity checks" (lines 289-375): selector at offset 1, then the
three-row copy/witness block (see the gate's cell layout). -/
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

The donor proof unit is `Orchard.Ecc.MulFixed.BaseFieldElem.RunningSumMul`; here the
bundle covers exactly Rust's first region (up to but excluding the complete addition),
so the Spec exposes `acc` (windows 0..83 accumulated) and `mul_b` (the MSB window
point) separately, plus the running sums. The parent's complete addition combines them:
`partialSum ks 83 + windowScalar 84 (ks 84) = V` in `Fq` (the `+2` paddings telescope
against `offsetAcc`). -/

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

/-- Pure-ℕ bounds for the first addition (windows 0 + 1) — file-level so the in-proof
uses run in an empty context (`omega` whnfs every hypothesis it scans). -/
private theorem base_bounds {a b : ℕ} (ha : a < 8) (hb : b < 8) :
    0 < (a + 2) * 8 ^ 0 ∧ (a + 2) * 8 ^ 0 < (b + 2) * 8 ^ 1 ∧
    (a + 2) * 8 ^ 0 + (b + 2) * 8 ^ 1
      < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
  have hcard : 100 < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
    norm_num [CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD]
  norm_num
  omega

/-- `OnCurve` of the coords-mk of a point is `OnCurve` of the point (structure eta). -/
private theorem point_eta_onCurve {P : Point Fp} (h : P.OnCurve) :
    ({ x := P.x, y := P.y } : Point Fp).OnCurve := h

/-- Pure-ℕ bounds for a ladder step (file-level, context-free). -/
private theorem step_bounds {k S j : ℕ} (hk : k < 8) (hS_lt : S < 2 * 8 ^ (j + 1))
    (hS_pos : 0 < S) (hj : j ≤ 82) :
    0 < (k + 2) * 8 ^ (j + 1) ∧ S < (k + 2) * 8 ^ (j + 1) ∧
    (k + 2) * 8 ^ (j + 1) < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD ∧
    S < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD ∧
    S + (k + 2) * 8 ^ (j + 1) < CompElliptic.Fields.Pasta.PALLAS_SCALAR_CARD := by
  have hpow : 0 < (8 : ℕ) ^ (j + 1) := pow_pos (by norm_num) _
  have htu : (k + 2) * 8 ^ (j + 1) ≤ 9 * 8 ^ (j + 1) := Nat.mul_le_mul_right _ (by omega)
  have htl : 2 * 8 ^ (j + 1) ≤ (k + 2) * 8 ^ (j + 1) := Nat.mul_le_mul_right _ (by omega)
  have hcard := Orchard.Ecc.MulFixed.BaseFieldElem.RunningSumMul.step_sum_lt hS_lt htu hj
  have hcard2 := Orchard.Ecc.MulFixed.BaseFieldElem.RunningSumMul.inv_lt_card hS_lt (by omega)
  refine ⟨by positivity, by omega, by omega, hcard2, hcard⟩

/-- `partialSum` at a successor (context-free unfold). -/
private theorem partialSum_succ (ks : ℕ → ℕ) (n : ℕ) :
    Orchard.Ecc.MulFixed.partialSum ks (n + 1)
      = Orchard.Ecc.MulFixed.partialSum ks n + (ks (n + 1) + 2) * 8 ^ (n + 1) := rfl

/-- Structure eta for `Point` as an equation. -/
private theorem point_eta (P : Point Fp) : ({ x := P.x, y := P.y } : Point Fp) = P := rfl

/-- `partialSum` at 1, unfolded (file-level, context-free arithmetic). -/
private theorem partialSum_one (ks : ℕ → ℕ) :
    Orchard.Ecc.MulFixed.partialSum ks 1 = ks 0 + 2 + (ks 1 + 2) * 8 ^ 1 := by
  simp [Orchard.Ecc.MulFixed.partialSum]

/-- The incomplete-addition child's output cells (rfl; the hand `add_output_eq`
pattern). -/
private theorem addinc_output (cfgI : AddIncomplete.Config) (row : ℕ)
    (input : Var AddIncomplete.Inputs Fp) (self : RegionIndex) :
    AddIncomplete.add.output cfgI row input self
      = { x := AssignedCell.of self (row + 1) cfgI.xQR,
          y := AssignedCell.of self (row + 1) cfgI.yQR } := rfl

/-- The inner bundle's config facts — exactly Rust's `configure`-time asserts
(`mul_fixed.rs:81-99` + running-sum column sharing). -/
def InnerEnvAssumptions (cfg : Config) (_ : Placed Environment Fp) : Prop :=
  cfg.superConfig.runningSumConfig.z = cfg.superConfig.window ∧
  cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP ∧
  cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP

/-- The inner bundle's soundness contract (donor `RunningSumMul.Spec`, split at the
region boundary). -/
def InnerSpec (B : FixedBase)
    (input : Value Halo2.Ironwood.DecomposeRunningSum.Inputs Fp)
    (out : Value InnerOut Fp) (_ : unit Fp) : Prop :=
  ∃ ks : ℕ → ℕ, (∀ w, w < 85 → ks w < 8) ∧
    (let V := ∑ j ∈ Finset.range 85, ks j * 8 ^ j
    input.alpha = (V : Fp) ∧
    out.acc = { x := ((Orchard.Ecc.MulFixed.partialSum ks 83) • B.point).x,
                y := ((Orchard.Ecc.MulFixed.partialSum ks 83) • B.point).y } ∧
    out.mulB = Orchard.Ecc.MulFixed.windowPoint B.point 84 (ks 84) ∧
    ∀ w : Fin 86, out.zs[w.val] = ((V / 2 ^ (3 * w.val) : ℕ) : Fp))

/-- Honest-prover precondition: α fits 255 bits (automatic at the Pallas instantiation). -/
def InnerProverAssumptions
    (input : ProverValue Halo2.Ironwood.DecomposeRunningSum.Inputs Fp)
    (_ : unit Fp) (_ : ProverHint Fp) : Prop :=
  input.alpha.val < 2 ^ 255

/-- The elaborated-metadata instance for the inner region's synthesize lambda (the
bundle's default `{}`), local so the standalone proofs can state
`Soundness`/`Completeness` over it. -/
instance innerElab (B : FixedBaseData) (config : Config) (offset : ℕ) :
    ElaboratedRegionCircuit Fp Halo2.Ironwood.DecomposeRunningSum.Inputs InnerOut
      (fun input : Var Halo2.Ironwood.DecomposeRunningSum.Inputs Fp =>
        innerRegion B config offset input.alpha) := {}

/-- Reduce the witness tables' `getElem!` at the honest window value: index
`windowVal = α.val / 8^w % 8 < 8`, and `8^w = 2^{3w}`. -/
private theorem ofFn8_get_windowVal (f : Fin 8 → Fp) (env : Placed ProverEnvironment Fp)
    (alpha : AssignedCell Fp) (w : ℕ) (a : Fp) (ha : readCell env alpha = a) :
    (Vector.ofFn f)[MulFixed.windowVal env alpha w]!
      = f ⟨a.val / 2 ^ (3 * w) % 8, Nat.mod_lt _ (by norm_num)⟩ := by
  have hidx : MulFixed.windowVal env alpha w = a.val / 2 ^ (3 * w) % 8 := by
    unfold MulFixed.windowVal
    rw [ha, pow_mul]
    norm_num
  have hlt : MulFixed.windowVal env alpha w < 8 := by
    rw [hidx]; exact Nat.mod_lt _ (by norm_num)
  rw [getElem!_pos (Vector.ofFn f) (MulFixed.windowVal env alpha w) (by simpa using hlt)]
  rw [Vector.getElem_ofFn]
  congr 1
  exact Fin.ext hidx

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
        (MulFixed.processWindow B.toData cfg.superConfig input_var_alpha) offset
        85).operations self)) :
    ∀ w : Fin 85,
      env.env.advice cfg.superConfig.addConfig.xP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Orchard.Ecc.MulFixed.windowPoint B.point w.val
            (input_alpha.val / 2 ^ (3 * w.val) % 8)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Orchard.Ecc.MulFixed.windowPoint B.point w.val
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
        = (Orchard.Ecc.MulFixed.windowPoint B.point w.val
            (input_alpha.val / 2 ^ (3 * w.val) % 8)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Orchard.Ecc.MulFixed.windowPoint B.point w.val
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
        (MulFixed.processWindow B.toData cfg.superConfig input_var_alpha) offset
        85).operations self))
    (hZW : cfg.superConfig.runningSumConfig.z = cfg.superConfig.window)
    (hXPeq : cfg.superConfig.addIncompleteConfig.xP = cfg.superConfig.addConfig.xP)
    (hYPeq : cfg.superConfig.addIncompleteConfig.yP = cfg.superConfig.addConfig.yP)
    (hZs : ∀ w : Fin 86, env.env.advice cfg.superConfig.window
        ((env.place self + (offset + w.val) : ℕ) : ℤ)
      = ((input_alpha.val / 2 ^ (3 * w.val) : ℕ) : Fp)) :
    RegionOperations.Constraints env.place self env.env.toEnvironment
      ((MulFixed.windowChain cfg.superConfig
        (MulFixed.processWindow B.toData cfg.superConfig input_var_alpha) offset
        85).operations self) := by
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
    addinc_proverAssumptions_eq, addinc_output, circuit_norm] at hD1
  have hLoopD := fun (i : Fin 82) => by
    have h := Halo2.SubcircuitRw.region_completeness_derived_placed
      AddIncomplete.add cfg.superConfig.addIncompleteConfig (offset + 2 + i.val) self env
      ⟨⟨AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addConfig.xP,
        AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addConfig.yP⟩,
       ⟨AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addIncompleteConfig.xQR,
        AssignedCell.of self (offset + 2 + i.val) cfg.superConfig.addIncompleteConfig.yQR⟩⟩
      ((hLoopW i).2.2.2)
    simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
      addinc_proverAssumptions_eq, addinc_output, circuit_norm] at h
    exact h
  -- honest accumulator invariant: cells at `offset + j + 1` hold `[partialSum ks j]·B`
  have hInv : ∀ j : ℕ, 1 ≤ j → j ≤ 83 →
      env.env.advice cfg.superConfig.addIncompleteConfig.xQR
          ((env.place self + (offset + j + 1) : ℕ) : ℤ)
        = (Orchard.Ecc.MulFixed.partialSum
            (fun t => input_alpha.val / 2 ^ (3 * t) % 8) j • B.point).x ∧
      env.env.advice cfg.superConfig.addIncompleteConfig.yQR
          ((env.place self + (offset + j + 1) : ℕ) : ℤ)
        = (Orchard.Ecc.MulFixed.partialSum
            (fun t => input_alpha.val / 2 ^ (3 * t) % 8) j • B.point).y := by
    intro j
    induction j with
    | zero => exact fun h _ => absurd h (by norm_num)
    | succ n ih =>
      intro _ hle
      rcases Nat.eq_zero_or_pos n with rfl | hnpos
      · -- j = 1: the explicit first addition
        obtain ⟨hp1x, hp1y, -⟩ := hPW ⟨1, by norm_num⟩
        obtain ⟨hp0x, hp0y, -⟩ := hPW ⟨0, by norm_num⟩
        rw [show ((⟨1, by norm_num⟩ : Fin 85) : ℕ) = 1 from rfl] at hp1x hp1y
        rw [show ((⟨0, by norm_num⟩ : Fin 85) : ℕ) = 0 from rfl,
          show offset + 0 = offset from by omega] at hp0x hp0y
        obtain ⟨t1, ht1_def⟩ : ∃ t : ℕ, t = (Orchard.Ecc.MulFixed.windowScalar 1
          (input_alpha.val / 2 ^ (3 * 1) % 8)).val := ⟨_, rfl⟩
        obtain ⟨s0, hs0_def⟩ : ∃ t : ℕ, t = (Orchard.Ecc.MulFixed.windowScalar 0
          (input_alpha.val / 2 ^ (3 * 0) % 8)).val := ⟨_, rfl⟩
        have ht1 : t1 = (input_alpha.val / 2 ^ (3 * 1) % 8 + 2) * 8 ^ 1 := by
          rw [ht1_def]
          exact Orchard.Ecc.MulFixed.windowScalar_val (by norm_num) (hks_lt 1)
        have hs0 : s0 = (input_alpha.val / 2 ^ (3 * 0) % 8 + 2) * 8 ^ 0 := by
          rw [hs0_def]
          exact Orchard.Ecc.MulFixed.windowScalar_val (by norm_num) (hks_lt 0)
        have hwp1 : Orchard.Ecc.MulFixed.windowPoint B.point 1
            (input_alpha.val / 2 ^ (3 * 1) % 8) = t1 • B.point := by rw [ht1_def]; rfl
        have hwp0 : Orchard.Ecc.MulFixed.windowPoint B.point 0
            (input_alpha.val / 2 ^ (3 * 0) % 8) = s0 • B.point := by rw [hs0_def]; rfl
        rw [hwp1] at hp1x hp1y
        rw [hwp0] at hp0x hp0y
        have hOnP : (t1 • B.point).OnCurve := by
          rw [← hwp1]; exact B.windowPoint_onCurve (hks_lt 1)
        have hOnQ : (s0 • B.point).OnCurve := by
          rw [← hwp0]; exact B.windowPoint_onCurve (hks_lt 0)
        obtain ⟨hbb1, hbb2, hbb3⟩ := base_bounds (hks_lt 0) (hks_lt 1)
        rw [← hs0] at hbb1 hbb2 hbb3
        rw [← ht1] at hbb2 hbb3
        have hxne : (t1 • B.point).x ≠ (s0 • B.point).x :=
          B.nsmul_x_ne hbb1 hbb2 hbb3
        obtain ⟨⟨-, hOut⟩, -⟩ := hD1 ⟨by rw [hp1x, hp1y]; exact point_eta_onCurve hOnP,
          by rw [hp0x, hp0y]; exact point_eta_onCurve hOnQ,
          by rw [hp1x, hp0x]; exact hxne⟩
        rw [show offset + 1 + 1 = offset + 2 from by omega] at hOut
        rw [show offset + 0 + 1 + 1 = offset + 2 from by omega]
        rw [hp1x, hp1y, hp0x, hp0y] at hOut
        rw [point_eta (t1 • B.point), point_eta (s0 • B.point),
          Orchard.Point.nsmul_add_nsmul B.onCurve] at hOut
        have hps : t1 + s0 = Orchard.Ecc.MulFixed.partialSum
            (fun t => input_alpha.val / 2 ^ (3 * t) % 8) 1 := by
          rw [ht1, hs0, partialSum_one]
          ring
        rw [hps] at hOut
        exact ⟨congrArg Orchard.Point.x hOut, congrArg Orchard.Point.y hOut⟩
      · -- step: window n+1 (loop chunk i = n−1)
        have hL := hLoopD ⟨n - 1, by omega⟩
        rw [show offset + 2 + (n - 1) = offset + n + 1 from by omega] at hL
        obtain ⟨hpx, hpy, -⟩ := hPW ⟨n + 1, by omega⟩
        rw [show ((⟨n + 1, by omega⟩ : Fin 85) : ℕ) = n + 1 from rfl,
          show offset + (n + 1) = offset + n + 1 from by omega] at hpx hpy
        have hih := ih (by omega) (by omega)
        obtain ⟨t, ht_def⟩ : ∃ t : ℕ,
            t = (Orchard.Ecc.MulFixed.windowScalar (n + 1)
              (input_alpha.val / 2 ^ (3 * (n + 1)) % 8)).val := ⟨_, rfl⟩
        obtain ⟨S, hS_def⟩ : ∃ S : ℕ,
            S = Orchard.Ecc.MulFixed.partialSum
              (fun t => input_alpha.val / 2 ^ (3 * t) % 8) n := ⟨_, rfl⟩
        have hval : t = (input_alpha.val / 2 ^ (3 * (n + 1)) % 8 + 2) * 8 ^ (n + 1) := by
          rw [ht_def]
          exact Orchard.Ecc.MulFixed.windowScalar_val (by omega) (hks_lt _)
        have hwp : Orchard.Ecc.MulFixed.windowPoint B.point (n + 1)
            (input_alpha.val / 2 ^ (3 * (n + 1)) % 8) = t • B.point := by
          rw [ht_def]; rfl
        rw [hwp] at hpx hpy
        rw [← hS_def] at hih
        have hS_lt : S < 2 * 8 ^ (n + 1) := by
          rw [hS_def]
          exact Orchard.Ecc.MulFixed.partialSum_lt _ n (fun _ _ => hks_lt _)
        have hS_pos : 0 < S := by
          rw [hS_def]; exact Orchard.Ecc.MulFixed.partialSum_pos _ n
        obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ :=
          step_bounds (hks_lt (n + 1)) hS_lt hS_pos (by omega)
        rw [← hval] at hb1 hb2 hb3 hb5
        obtain ⟨⟨-, hOut⟩, -⟩ := hL ⟨by
            rw [hpx, hpy]
            exact point_eta_onCurve (B.nsmul_onCurve hb1 hb3),
          by
            rw [hih.1, hih.2]
            exact point_eta_onCurve (B.nsmul_onCurve hS_pos hb4),
          by
            rw [hpx, hih.1]
            exact B.nsmul_x_ne hS_pos hb2 (by omega)⟩
        rw [show offset + n + 1 + 1 = offset + n + 2 from by omega] at hOut
        rw [show offset + (n + 1) + 1 = offset + n + 2 from by omega]
        rw [hpx, hpy, hih.1, hih.2] at hOut
        rw [point_eta (t • B.point), point_eta (S • B.point),
          Orchard.Point.nsmul_add_nsmul B.onCurve] at hOut
        have hps : t + S = Orchard.Ecc.MulFixed.partialSum
            (fun t => input_alpha.val / 2 ^ (3 * t) % 8) (n + 1) := by
          rw [hval, hS_def, partialSum_succ]
          ring
        rw [hps] at hOut
        exact ⟨congrArg Orchard.Point.x hOut, congrArg Orchard.Point.y hOut⟩
  simp only [MulFixed.windowChain, MulFixed.processWindow, circuit_norm, mul_one]
  have hC1 := Halo2.SubcircuitRw.region_completeness_leaf_placed
    AddIncomplete.add cfg.superConfig.addIncompleteConfig (offset + 1) self env
    ⟨⟨AssignedCell.of self (offset + 1) cfg.superConfig.addConfig.xP,
      AssignedCell.of self (offset + 1) cfg.superConfig.addConfig.yP⟩,
     ⟨AssignedCell.of self offset cfg.superConfig.addConfig.xP,
      AssignedCell.of self offset cfg.superConfig.addConfig.yP⟩⟩ hAW1
  simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
    addinc_proverAssumptions_eq, addinc_output, circuit_norm] at hC1
  constructor
  · -- first addition: window-1 point + window-0 point, honest values
    obtain ⟨hp1x, hp1y, -⟩ := hPW ⟨1, by norm_num⟩
    obtain ⟨hp0x, hp0y, -⟩ := hPW ⟨0, by norm_num⟩
    rw [show ((⟨1, by norm_num⟩ : Fin 85) : ℕ) = 1 from rfl] at hp1x hp1y
    rw [show ((⟨0, by norm_num⟩ : Fin 85) : ℕ) = 0 from rfl,
      show offset + 0 = offset from by omega] at hp0x hp0y
    obtain ⟨t1, ht1_def⟩ : ∃ t : ℕ, t = (Orchard.Ecc.MulFixed.windowScalar 1
      (input_alpha.val / 2 ^ (3 * 1) % 8)).val := ⟨_, rfl⟩
    obtain ⟨s0, hs0_def⟩ : ∃ t : ℕ, t = (Orchard.Ecc.MulFixed.windowScalar 0
      (input_alpha.val / 2 ^ (3 * 0) % 8)).val := ⟨_, rfl⟩
    have ht1 : t1 = (input_alpha.val / 2 ^ (3 * 1) % 8 + 2) * 8 ^ 1 := by
      rw [ht1_def]
      exact Orchard.Ecc.MulFixed.windowScalar_val (by norm_num) (hks_lt 1)
    have hs0 : s0 = (input_alpha.val / 2 ^ (3 * 0) % 8 + 2) * 8 ^ 0 := by
      rw [hs0_def]
      exact Orchard.Ecc.MulFixed.windowScalar_val (by norm_num) (hks_lt 0)
    have hwp1 : Orchard.Ecc.MulFixed.windowPoint B.point 1
        (input_alpha.val / 2 ^ (3 * 1) % 8) = t1 • B.point := by rw [ht1_def]; rfl
    have hwp0 : Orchard.Ecc.MulFixed.windowPoint B.point 0
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
      addinc_proverAssumptions_eq, addinc_output, circuit_norm] at hC
    obtain ⟨hpx, hpy, -⟩ := hPW ⟨i.val + 2, by omega⟩
    rw [show ((⟨i.val + 2, by omega⟩ : Fin 85) : ℕ) = i.val + 2 from rfl,
      show offset + (i.val + 2) = offset + 2 + i.val from by omega] at hpx hpy
    have hih := hInv (i.val + 1) (by omega) (by omega)
    rw [show offset + (i.val + 1) + 1 = offset + 2 + i.val from by omega] at hih
    obtain ⟨t, ht_def⟩ : ∃ t : ℕ,
        t = (Orchard.Ecc.MulFixed.windowScalar (i.val + 2)
          (input_alpha.val / 2 ^ (3 * (i.val + 2)) % 8)).val := ⟨_, rfl⟩
    obtain ⟨S, hS_def⟩ : ∃ S : ℕ,
        S = Orchard.Ecc.MulFixed.partialSum
          (fun t => input_alpha.val / 2 ^ (3 * t) % 8) (i.val + 1) := ⟨_, rfl⟩
    have hval : t = (input_alpha.val / 2 ^ (3 * (i.val + 2)) % 8 + 2) * 8 ^ (i.val + 2) := by
      rw [ht_def]
      exact Orchard.Ecc.MulFixed.windowScalar_val (by omega) (hks_lt _)
    have hwp : Orchard.Ecc.MulFixed.windowPoint B.point (i.val + 2)
        (input_alpha.val / 2 ^ (3 * (i.val + 2)) % 8) = t • B.point := by
      rw [ht_def]; rfl
    rw [hwp] at hpx hpy
    rw [← hS_def] at hih
    have hS_lt : S < 2 * 8 ^ (i.val + 2) := by
      rw [hS_def]
      exact Orchard.Ecc.MulFixed.partialSum_lt _ _ (fun _ _ => hks_lt _)
    have hS_pos : 0 < S := by
      rw [hS_def]; exact Orchard.Ecc.MulFixed.partialSum_pos _ _
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
        (MulFixed.processWindow B.toData cfg.superConfig input_var_alpha) offset
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
        = (Orchard.Ecc.MulFixed.windowPoint B.point w.val
            (input_alpha.val / 2 ^ (3 * w.val) % 8)).x ∧
      env.env.advice cfg.superConfig.addConfig.yP
          ((env.place self + (offset + w.val) : ℕ) : ℤ)
        = (Orchard.Ecc.MulFixed.windowPoint B.point w.val
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
    have hcongr : Orchard.Ecc.MulFixed.interpolate
        (MulFixed.readParams cfg.superConfig
          (Query.eval env.env.toEnvironment
            (fun j => if j = cfg.superConfig.runningSumConfig.qRangeCheck.index then 1
              else 0)
            ((env.place self + (offset + i.val) : ℕ) : ℤ)))
        ((input_alpha.val / 2 ^ (3 * i.val) % 8 : ℕ) : Fp)
        = Orchard.Ecc.MulFixed.interpolate (B.params i.val)
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
    unfold Orchard.Point.OnCurve at hoc
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

/-- Constraints of a `pure` region step, any payload (no ops; substitution-friendly). -/
private theorem pure_constraints (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment Fp) (v : Var InnerOut Fp) :
    RegionOperations.Constraints place self env
      ((pure (f := RegionCircuit Fp) v).operations self) := by
  rw [RegionCircuit.operations_pure]
  exact trivial

/-- The inner bundle's completeness, standalone (its own declaration/heartbeat budget —
the shared-budget split; body per the donor `RunningSumMul.completeness`). -/
private theorem inner_completeness (B : FixedBase) (cfg : Config) (offset : ℕ) :
    FormalRegionCircuit.Completeness
      (Input := Halo2.Ironwood.DecomposeRunningSum.Inputs) (Output := InnerOut)
      (fun input : Var Halo2.Ironwood.DecomposeRunningSum.Inputs Fp =>
        innerRegion B.toData cfg offset input.alpha)
      (fun _ _ _ => default)
      (InnerEnvAssumptions cfg) (fun _ => True) InnerProverAssumptions
      (fun _ _ _ _ => True) := by
    circuit_proof_start
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
    refine And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))
    · with_reducible exact hDC.1
    · with_reducible
        exact inner_completeness_fixed B cfg offset self env input_var_alpha
          input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs
    · with_reducible
        exact inner_completeness_chain B cfg offset self env input_var_alpha
          input_alpha h_input hWfix hWchain hZW hXPeq hYPeq hZs
    · rw [RegionCircuit.operations_pure]
      exact trivial



set_option linter.constructorNameAsVariable false in
/-- The inner-region bundle: `innerRegion` with the donor-shaped contract. -/
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
    -- PROOF ARC recipe per Mul.lean:982-1002: NO structural unfolds in the list
    -- (innerRegion at h_output/goal whnf-cliffs); contract defs only.
    circuit_proof_start [InnerSpec, InnerEnvAssumptions, InnerProverAssumptions]
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
        _ = V % 8 ^ 85 := Orchard.Ecc.MulFixed.sum_base8 V 85
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
          = (Orchard.Ecc.MulFixed.windowPoint B.point w.val (V / 2 ^ (3 * w.val) % 8)).x ∧
        env.env.advice cfg.superConfig.addConfig.yP
            ((env.place self + (offset + w.val) : ℕ) : ℤ)
          = (Orchard.Ecc.MulFixed.windowPoint B.point w.val (V / 2 ^ (3 * w.val) % 8)).y := by
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
          = Orchard.Ecc.MulFixed.interpolate (B.params w.val)
              ((V / 2 ^ (3 * w.val) % 8 : ℕ) : Fp) := by
        rw [← sub_eq_zero.mp hIx]
        apply MulFixed.interpolate_congr_params <;>
          simp only [MulFixed.readParams, circuit_norm, add_zero] <;>
          first
          | exact hL0 | exact hL1 | exact hL2 | exact hL3
          | exact hL4 | exact hL5 | exact hL6 | exact hL7
      have hspec : Orchard.Ecc.MulFixed.Coords.Spec (B.params w.val)
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
        addinc_output, circuit_norm] at hA1
      have hLoopS := fun (i : Fin 82) => by
        have h := hALoop i
        subcircuit_rw at h
        simp only [addinc_spec_eq, addinc_assumptions_eq, addinc_envAssumptions_eq,
          addinc_output, circuit_norm, mul_one] at h
        exact h
      clear hALoop
      -- window points as nsmul, with scalar values
      have hks_lt : ∀ t, V / 2 ^ (3 * t) % 8 < 8 := fun t => Nat.mod_lt _ (by norm_num)
      -- ── the accumulator invariant: after windows 0..j, the output cells at
      --    `offset + j + 1` hold `[partialSum ks j]·B` ──
      have hInv : ∀ j : ℕ, 1 ≤ j → j ≤ 83 →
          env.env.advice cfg.superConfig.addIncompleteConfig.xQR
              ((env.place self + (offset + j + 1) : ℕ) : ℤ)
            = (Orchard.Ecc.MulFixed.partialSum (fun t => V / 2 ^ (3 * t) % 8) j
                • B.point).x ∧
          env.env.advice cfg.superConfig.addIncompleteConfig.yQR
              ((env.place self + (offset + j + 1) : ℕ) : ℤ)
            = (Orchard.Ecc.MulFixed.partialSum (fun t => V / 2 ^ (3 * t) % 8) j
                • B.point).y := by
        intro j
        induction j with
        | zero => exact fun h _ => absurd h (by norm_num)
        | succ n ih =>
          intro _ hle
          rcases Nat.eq_zero_or_pos n with rfl | hnpos
          · -- base j = 1: the explicit first addition (windows 1 + 0)
            obtain ⟨hp1x, hp1y⟩ := hWP ⟨1, by norm_num⟩
            obtain ⟨hp0x, hp0y⟩ := hWP ⟨0, by norm_num⟩
            rw [show ((⟨1, by norm_num⟩ : Fin 85) : ℕ) = 1 from rfl] at hp1x hp1y
            rw [show ((⟨0, by norm_num⟩ : Fin 85) : ℕ) = 0 from rfl] at hp0x hp0y
            rw [show offset + 0 = offset from by omega] at hp0x hp0y
            -- scalar values of the two window points, kept OPAQUE (performance)
            obtain ⟨t1, ht1_def⟩ :
                ∃ t : ℕ, t = (Orchard.Ecc.MulFixed.windowScalar 1 (V / 2 ^ (3 * 1) % 8)).val :=
              ⟨_, rfl⟩
            obtain ⟨s0, hs0_def⟩ :
                ∃ t : ℕ, t = (Orchard.Ecc.MulFixed.windowScalar 0 (V / 2 ^ (3 * 0) % 8)).val :=
              ⟨_, rfl⟩
            have ht1 : t1 = (V / 2 ^ (3 * 1) % 8 + 2) * 8 ^ 1 := by
              rw [ht1_def]
              exact Orchard.Ecc.MulFixed.windowScalar_val (by norm_num) (hks_lt 1)
            have hs0 : s0 = (V / 2 ^ (3 * 0) % 8 + 2) * 8 ^ 0 := by
              rw [hs0_def]
              exact Orchard.Ecc.MulFixed.windowScalar_val (by norm_num) (hks_lt 0)
            have hwp1 : Orchard.Ecc.MulFixed.windowPoint B.point 1 (V / 2 ^ (3 * 1) % 8)
                = t1 • B.point := by rw [ht1_def]; rfl
            have hwp0 : Orchard.Ecc.MulFixed.windowPoint B.point 0 (V / 2 ^ (3 * 0) % 8)
                = s0 • B.point := by rw [hs0_def]; rfl
            rw [hwp1] at hp1x hp1y
            rw [hwp0] at hp0x hp0y
            have hOnP : (t1 • B.point).OnCurve := by
              rw [← hwp1]; exact B.windowPoint_onCurve (hks_lt 1)
            have hOnQ : (s0 • B.point).OnCurve := by
              rw [← hwp0]; exact B.windowPoint_onCurve (hks_lt 0)
            obtain ⟨hbb1, hbb2, hbb3⟩ := base_bounds (hks_lt 0) (hks_lt 1)
            rw [← hs0] at hbb1 hbb2 hbb3
            rw [← ht1] at hbb2 hbb3
            have hxne : (t1 • B.point).x ≠ (s0 • B.point).x :=
              B.nsmul_x_ne hbb1 hbb2 hbb3
            obtain ⟨-, hOut⟩ := hA1 ⟨by rw [hp1x, hp1y]; exact point_eta_onCurve hOnP,
              by rw [hp0x, hp0y]; exact point_eta_onCurve hOnQ,
              by rw [hp1x, hp0x]; exact hxne⟩
            rw [show offset + 1 + 1 = offset + 2 from by omega] at hOut
            rw [show offset + 0 + 1 + 1 = offset + 2 from by omega]
            rw [hp1x, hp1y, hp0x, hp0y] at hOut
            rw [point_eta (t1 • B.point), point_eta (s0 • B.point),
              Orchard.Point.nsmul_add_nsmul B.onCurve] at hOut
            have hps : t1 + s0
                = Orchard.Ecc.MulFixed.partialSum (fun t => V / 2 ^ (3 * t) % 8) 1 := by
              rw [ht1, hs0, partialSum_one]
              ring
            rw [hps] at hOut
            exact ⟨congrArg Orchard.Point.x hOut, congrArg Orchard.Point.y hOut⟩
          · -- step: window n+1 joins the accumulator (loop chunk i = n−1)
            have hL := hLoopS ⟨n - 1, by omega⟩
            rw [show offset + 2 + (n - 1) = offset + n + 1 from by omega] at hL
            obtain ⟨hpx, hpy⟩ := hWP ⟨n + 1, by omega⟩
            rw [show ((⟨n + 1, by omega⟩ : Fin 85) : ℕ) = n + 1 from rfl,
              show offset + (n + 1) = offset + n + 1 from by omega] at hpx hpy
            have hih := ih (by omega) (by omega)
            -- opaque scalars (performance)
            obtain ⟨t, ht_def⟩ : ∃ t : ℕ,
                t = (Orchard.Ecc.MulFixed.windowScalar (n + 1)
                  (V / 2 ^ (3 * (n + 1)) % 8)).val := ⟨_, rfl⟩
            obtain ⟨S, hS_def⟩ : ∃ S : ℕ,
                S = Orchard.Ecc.MulFixed.partialSum (fun t => V / 2 ^ (3 * t) % 8) n :=
              ⟨_, rfl⟩
            have hval : t = (V / 2 ^ (3 * (n + 1)) % 8 + 2) * 8 ^ (n + 1) := by
              rw [ht_def]
              exact Orchard.Ecc.MulFixed.windowScalar_val (by omega) (hks_lt _)
            have hwp : Orchard.Ecc.MulFixed.windowPoint B.point (n + 1)
                (V / 2 ^ (3 * (n + 1)) % 8) = t • B.point := by
              rw [ht_def]; rfl
            rw [hwp] at hpx hpy
            rw [← hS_def] at hih
            have hS_lt : S < 2 * 8 ^ (n + 1) := by
              rw [hS_def]
              exact Orchard.Ecc.MulFixed.partialSum_lt _ n (fun _ _ => hks_lt _)
            have hS_pos : 0 < S := by
              rw [hS_def]; exact Orchard.Ecc.MulFixed.partialSum_pos _ n
            obtain ⟨hb1, hb2, hb3, hb4, hb5⟩ :=
              step_bounds (hks_lt (n + 1)) hS_lt hS_pos (by omega)
            rw [← hval] at hb1 hb2 hb3 hb5
            obtain ⟨-, hOut⟩ := hL ⟨by
                rw [hpx, hpy]
                exact point_eta_onCurve (B.nsmul_onCurve hb1 hb3),
              by
                rw [hih.1, hih.2]
                exact point_eta_onCurve (B.nsmul_onCurve hS_pos hb4),
              by
                rw [hpx, hih.1]
                exact B.nsmul_x_ne hS_pos hb2 (by omega)⟩
            rw [show offset + n + 1 + 1 = offset + n + 2 from by omega] at hOut
            rw [show offset + (n + 1) + 1 = offset + n + 2 from by omega]
            rw [hpx, hpy, hih.1, hih.2] at hOut
            rw [point_eta (t • B.point), point_eta (S • B.point),
              Orchard.Point.nsmul_add_nsmul B.onCurve] at hOut
            have hps : t + S = Orchard.Ecc.MulFixed.partialSum
                (fun t => V / 2 ^ (3 * t) % 8) (n + 1) := by
              rw [hval, hS_def, partialSum_succ]
              ring
            rw [hps] at hOut
            exact ⟨congrArg Orchard.Point.x hOut, congrArg Orchard.Point.y hOut⟩
      have hI83 := hInv 83 (by norm_num) le_rfl
      rw [show offset + 83 + 1 = offset + 84 from by omega] at hI83
      rw [← hOax, ← hOay]
      rcases hP : Orchard.Ecc.MulFixed.partialSum (fun t => V / 2 ^ (3 * t) % 8) 83
          • B.point with ⟨px, py⟩
      rw [hP] at hI83
      rw [hI83.1, hI83.2]
    · -- mulB = windowPoint 84 k₈₄  (the MSB coords row)
      obtain ⟨hwx, hwy⟩ := hWP ⟨84, by norm_num⟩
      rw [← hOmx, ← hOmy]
      rcases hW : Orchard.Ecc.MulFixed.windowPoint B.point 84 (V / 2 ^ (3 * 84) % 8)
        with ⟨wx, wy⟩
      rw [show ((⟨84, by norm_num⟩ : Fin 85) : ℕ) = 84 from rfl, hW] at hwx hwy
      rw [hwx, hwy]
    · -- the running sums are the shifts of the digit sum
      intro w
      rw [hSum, ← congrArg (fun v => v[w.val]'w.isLt) hOzs]
      simp only [circuit_norm, hZW]
      exact hZs w

  completeness := fun cfg offset => inner_completeness B cfg offset

/-- Rust `base_field_elem::Config::assign` (lines 165-378): the four layouter pieces in
source order. Returns the result point `[α]B`. -/
def synthesize (B : FixedBaseData) (cfg : Config) (alpha : AssignedCell Fp) :
    Circuit Fp (Var Point Fp) := do
  -- 1. the incomplete-addition region
  let inn ←
    assignRegion "Base-field elem fixed-base mul (incomplete addition)"
      (innerRegion B cfg 0 alpha)
  let zs := inn.zs
  -- 2. the complete addition `mul_b + acc` (lines 207-218)
  let result ←
    assignRegion "Base-field elem fixed-base mul (complete addition)"
      (Add.add.call cfg.superConfig.addConfig 0 ⟨inn.mulB, inn.acc⟩)
  -- Rust binds `alpha := scalar.base_field_elem = running_sum[0]` (line 189/257): every
  -- downstream α reference — the canonicity copy AND the witness programs — uses the
  -- z_0 CELL, not the original α cell.
  let alphaZ0 := zs[0]
  -- 3. the 13-word lookup range check of α₀' (lines 271-287)
  let (alphaPrime, z13) ← witnessCheck13 cfg.lookupConfig (alphaZeroPrimeWit alphaZ0 zs[84])
  -- 4. the canonicity checks (lines 289-375)
  assignRegion "Canonicity checks"
    (canonicityRegion cfg alphaZ0 zs[84] alphaPrime z13 zs[44] zs[43])
  return result

end Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem
