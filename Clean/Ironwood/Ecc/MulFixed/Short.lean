import Clean.Ironwood.Ecc.MulFixed

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul_fixed/short.rs` (read in
full) — fixed-base scalar multiplication by a short signed exponent
(`|magnitude| < 2^64`, sign ∈ {1, −1}); `L_SCALAR_SHORT = 64`,
`NUM_WINDOWS_SHORT = ⌈64/3⌉ = 22` (`constants.rs:22-27`).

- `Config` (lines 13-18): the `q_mul_fixed_short` selector and the shared super config.
- `configure` (lines 20-33) + the "Short fixed-base mul gate" (lines 35-77): on
  `q_mul_fixed_short` — `last_window_check` (bool check of `z_21`, copied into the `u`
  column), `sign_check` (`sign² − 1`, sign on the `window` column), the redundant
  `y_check` (`(y_p − y_a)(y_p + y_a)`), and `negation_check` (`sign·y_p − y_a`), with
  `y_p` on `add.y_p` and `y_a` on `add.y_qr`, all at `cur`.
- `assign` (lines 108-199), two regions:
  1. "Short fixed-base mul (incomplete addition)": `decompose` (lines 84-106: strict
     `copy_decompose` of the magnitude, 64 bits in 22 windows), then the shared
     `assign_region_inner` with the running-sum `q_range_check` as the coords toggle;
  2. "Short fixed-base mul (most significant word)": `add(mul_b, acc)` at offset 0;
     at offset 1 — copy `sign` into `window`, copy `z_21` into `u`, enable
     `q_mul_fixed_short`, witness the conditionally-negated `y` into `add.y_p`.
     Result = `(magnitude_mul.x, y_var)`.

Phase-1 donor: `Orchard/Ecc/MulFixed/Short.lean` (Gate spec, the signed-magnitude value
algebra). Donor spec shape: `∃ m < 2^64, magnitude = ↑m ∧ (sign = 1 ∧ output = ↑m • B
∨ sign = −1 ∧ output = −(↑m • B) …)`.
-/

namespace Halo2.Ironwood.Ecc.MulFixed.Short

open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Ecc.MulFixed
  (coordsGate fixedConstantsLoop processWindow windowChain FixedBaseData)
open Halo2.Ironwood.DecomposeRunningSum (copyDecompose rangeCheckExpr)
open Orchard (Point)

/-- Rust `short::Config` (lines 13-18). -/
structure Config where
  qMulFixedShort : Selector
  superConfig : MulFixed.Config

/-- The "Short fixed-base mul gate" (lines 35-77), the exact Rust AST and constraint
order. -/
def shortGate (cfg : Config) : Gate Fp where
  name := "Short fixed-base mul gate"
  selector := cfg.qMulFixedShort
  constraints :=
    let yP : Expression Fp Query := queryAdvice cfg.superConfig.addConfig.yP 0
    let yA : Expression Fp Query := queryAdvice cfg.superConfig.addConfig.yQR 0
    -- z_21 = k_21, copied into the `u` column (line 44)
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

/-- Rust `short::Config::configure` (lines 20-33). -/
def configure (superConfig : MulFixed.Config) : Configure Fp Config := do
  let qMulFixedShort ← selector
  let cfg : Config := { qMulFixedShort, superConfig }
  createGate (shortGate cfg)
  return cfg

/-- The magnitude-sign input pair (Rust `MagnitudeSign`, both already-assigned cells). -/
structure Inputs (F : Type) where
  magnitude : F
  sign : F
deriving ProvableStruct

/-- The conditionally-negated final `y` witness: `sign = −1 ? −y : y` over the sign cell
and the magnitude-mul `y` cell (lines 177-183). -/
def yVarWit (sign yMag : AssignedCell Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[if readCell env sign = -1 then -(readCell env yMag) else readCell env yMag]

/-- Region 1, "Short fixed-base mul (incomplete addition)" (lines 117-145): the strict
22-window running-sum decomposition of the magnitude, then the shared inner body over
the magnitude cell (fixed constants with the running-sum coords toggle; the window
chain). Returns `(acc, mul_b, zs)`. -/
def innerRegion (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (input : Inputs (AssignedCell Fp)) :
    RegionCircuit Fp
      (Point (AssignedCell Fp) × Point (AssignedCell Fp) × Vector (AssignedCell Fp) 23) := do
  -- `decompose` (lines 84-106): strict copy_decompose, 64 bits in 22 windows
  let zsOut ← (copyDecompose 3 22).call cfg.superConfig.runningSumConfig offset
    ⟨input.magnitude⟩
  -- `assign_fixed_constants` with the running-sum coords gate as toggle (line 140)
  fixedConstantsLoop (coordsGate cfg.superConfig) B cfg.superConfig offset 22
  -- the window chain over the magnitude cell
  let (acc, mulB) ← windowChain cfg.superConfig
    (processWindow B cfg.superConfig input.magnitude) offset 22
  return (acc, mulB, zsOut.zs)

/-- Region 2, "Short fixed-base mul (most significant word)" (lines 148-198): the
complete addition at offset 0, then the sign row at offset 1. Returns the result point
(`magnitude_mul.x`, conditionally-negated `y`). -/
def mswRegion (cfg : Config) (acc mulB : Point (AssignedCell Fp))
    (sign z21 : AssignedCell Fp) : RegionCircuit Fp (Point (AssignedCell Fp)) := do
  -- [magnitude]B by complete addition (lines 152-158)
  let magnitudeMul ← Add.add.call cfg.superConfig.addConfig 0 ⟨mulB, acc⟩
  -- offset 1: copy sign into `window` (lines 163-169)
  let _s ← copyAdvice sign cfg.superConfig.window 1
  -- copy z_21 into `u` (lines 171-175)
  let _z ← copyAdvice z21 cfg.superConfig.u 1
  -- enable the short gate (line 186)
  (shortGate cfg).enable 1
  -- witness the conditionally-negated y into `add.y_p` (lines 188-194)
  let yVar ← assignAdvice cfg.superConfig.addConfig.yP 1 (yVarWit sign magnitudeMul.y)
  return { x := magnitudeMul.x, y := yVar }

/-- Rust `short::Config::assign` (lines 108-199): the two regions. Returns the result
point `[sign·magnitude]B`. -/
def synthesize (B : FixedBaseData) (cfg : Config) (input : Inputs (AssignedCell Fp)) :
    Circuit Fp (Var Point Fp) := do
  let (acc, mulB, zs) ←
    assignRegion "Short fixed-base mul (incomplete addition)"
      (innerRegion B cfg 0 input)
  assignRegion "Short fixed-base mul (most significant word)"
    (mswRegion cfg acc mulB input.sign zs[21])

end Halo2.Ironwood.Ecc.MulFixed.Short
