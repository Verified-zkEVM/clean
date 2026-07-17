import Clean.Ironwood.Ecc.MulFixed
import Clean.Ironwood.Utilities.LookupRangeCheck

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

/-- Region 1, "Base-field elem fixed-base mul (incomplete addition)" (lines 174-205):
the strict running-sum decomposition of α (85 3-bit windows over 255 bits), the fixed
constants, the window-0 accumulator, the incomplete-addition loop over windows 1..83,
and the most significant window 84. Returns `(acc, mul_b, zs)` — the two points the
complete addition combines, and the running-sum cells (`z_0 = α`, `z_43/z_44/z_84` feed
the canonicity check). -/
def innerRegion (B : FixedBaseData) (cfg : Config) (offset : ℕ) (alpha : AssignedCell Fp) :
    RegionCircuit Fp
      (Point (AssignedCell Fp) × Point (AssignedCell Fp) × Vector (AssignedCell Fp) 86) := do
  -- scalar decomposition (lines 179-193): strict `copy_decompose`
  let zsOut ← (copyDecompose 3 85).call cfg.superConfig.runningSumConfig offset ⟨alpha⟩
  -- `assign_fixed_constants` (mul_fixed.rs:181, 195-252)
  fixedConstantsLoop B cfg.superConfig offset 85
  -- initialize the accumulator: window 0 (mul_fixed.rs:184, 307-321)
  let acc0 ← processWindow B cfg.superConfig alpha 0 offset
  -- window 1 (mul_fixed.rs:187, 323-360): the accumulator is the window-0 point — a
  -- REAL copy into the incomplete-addition q cells
  let mulB1 ← processWindow B cfg.superConfig alpha 1 (offset + 1)
  let _a1 ← AddIncomplete.add.call cfg.superConfig.addIncompleteConfig (offset + 1)
    ⟨mulB1, acc0⟩
  -- windows 2..83: the accumulator is the previous round's output, which sits at the
  -- SAME cells the q-copy targets (Rust "will be copied into themselves")
  RegionCircuit.forRange' (offset + 2) 1 82 (fun i row => do
    let mulB ← processWindow B cfg.superConfig alpha (i + 2) row
    let qx ← cellAt cfg.superConfig.addIncompleteConfig.xQR row
    let qy ← cellAt cfg.superConfig.addIncompleteConfig.yQR row
    let _ ← AddIncomplete.add.call cfg.superConfig.addIncompleteConfig row
      ⟨mulB, { x := qx, y := qy }⟩
    return ())
  -- most significant window 84 (mul_fixed.rs:190, 378-405)
  let mulB ← processWindow B cfg.superConfig alpha 84 (offset + 84)
  -- the exit accumulator: the last incomplete addition's output cells (row offset+84)
  let accX ← cellAt cfg.superConfig.addIncompleteConfig.xQR (offset + 84)
  let accY ← cellAt cfg.superConfig.addIncompleteConfig.yQR (offset + 84)
  return ({ x := accX, y := accY }, mulB, zsOut.zs)

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
    LookupRangeCheck.rangeCheckLoop 10 cfg z0 0 13
    let z13 ← cellAt cfg.runningSum 13
    return (z0, z13))

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

/-- Rust `base_field_elem::Config::assign` (lines 165-378): the four layouter pieces in
source order. Returns the result point `[α]B`. -/
def synthesize (B : FixedBaseData) (cfg : Config) (alpha : AssignedCell Fp) :
    Circuit Fp (Var Point Fp) := do
  -- 1. the incomplete-addition region
  let ⟨acc, mulB, zs⟩ ←
    assignRegion "Base-field elem fixed-base mul (incomplete addition)"
      (innerRegion B cfg 0 alpha)
  -- 2. the complete addition `mul_b + acc` (lines 207-218)
  let result ←
    assignRegion "Base-field elem fixed-base mul (complete addition)"
      (Add.add.call cfg.superConfig.addConfig 0 ⟨mulB, acc⟩)
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
