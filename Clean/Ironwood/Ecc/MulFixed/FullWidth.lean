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

/-- Region 1, "Full-width fixed-base mul (incomplete addition)" (lines 126-147): witness
the scalar windows, then the shared inner body — fixed constants (toggle =
`q_mul_fixed_full`), window-0 accumulator, the incomplete-addition loop over windows
1..83, the most significant window 84. -/
def innerRegion (B : FixedBaseData) (cfg : Config) (offset : ℕ)
    (windows : Vector (FExpr Fp) 85) :
    RegionCircuit Fp (Point (AssignedCell Fp) × Point (AssignedCell Fp)) := do
  -- witness the scalar (lines 132-136)
  witnessScalarLoop cfg windows offset
  -- `assign_fixed_constants` with `q_mul_fixed_full` as the coords toggle (line 143)
  fixedConstantsLoop (fullWidthGate cfg) B cfg.superConfig offset 85
  -- the shared window chain: init (window 0), incomplete additions (1..83), MSB (84)
  MulFixed.windowChain cfg.superConfig (processWindowH B cfg windows) offset 85

/-- Rust `full_width::Config::assign` (lines 115-177): the two regions. Returns the
result point `[scalar]B`. -/
def synthesize (B : FixedBaseData) (cfg : Config) (windows : Vector (FExpr Fp) 85) :
    Circuit Fp (Var Point Fp) := do
  let (acc, mulB) ←
    assignRegion "Full-width fixed-base mul (incomplete addition)"
      (innerRegion B cfg 0 windows)
  assignRegion "Full-width fixed-base mul (last window, complete addition)"
    (Add.add.call cfg.superConfig.addConfig 0 ⟨mulB, acc⟩)

end Halo2.Ironwood.Ecc.MulFixed.FullWidth
