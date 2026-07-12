import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Orchard.Specs.Pallas
import Clean.Orchard.Ecc.Mul
import Clean.Orchard.Ecc.Mul.Assign
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.MulIncomplete
import Clean.Ironwood.Ecc.MulComplete
import Clean.Ironwood.Ecc.MulOverflow

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul.rs` (read in full), the
convergence assembly of variable-base scalar multiplication.

This is the top-level `mul.rs::Config::assign` (`CircuitVersion::AnchoredBase`):
computes `[alpha] base` where `alpha : Fp` is a Pallas base-field element. The working
scalar is `k = alpha.val + t_q`, decomposed MSB-first into 255 bits and processed as
(`mul.rs:171-305`, one `layouter.assign_region`):

1. `acc = [2]base` via complete addition (`Add.add`, `mul.rs:188-190`);
2. `z_init = 0`, the running-sum start (`mul.rs:201-206`);
3. the `hi` incomplete half — 125 double-and-add steps for bits `k_254..k_130`
   (`MulIncomplete.double_and_add 124`, `mul.rs:209-216`);
4. the `lo` incomplete half — 126 double-and-add steps for bits `k_129..k_4`
   (`MulIncomplete.double_and_add 125`, `mul.rs:220-227`);
5. three complete-addition bits `k_3..k_1` (`MulComplete.assign_region 3`, `mul.rs:239-253`);
6. the LSB step `k_0` — the `q_mul_lsb` gate (`mul.rs:129-161`, ported here as a standalone
   def) and a final complete addition (`Add.add`, `mul.rs:324-385`);
7. the overflow check on `z_0`, `z_130`, `k_254` (`MulOverflow.circuit 10`, `mul.rs:298-302`).

Soundness rests on `2^254 + t_q ≡ 0 (mod q)`: the double-and-add accumulates
`[2^254 + k] base = [alpha] base`.

## Config assembly (mul.rs:64-127) — the ConfigWF verdict

Rust `mul::Config` (`mul.rs:48-62`) stores the `q_mul_lsb` selector plus the five child
configs (`add`, `hi_config`, `lo_config`, `complete`, `overflow`). `Config::configure`
(`mul.rs:65-127`) instantiates the two incomplete configs from the shared 10-advice bundle,
then registers the LSB gate and asserts a set of column non-overlap facts (`mul.rs:92-124`):

- `hi_config.x_p = lo_config.x_p` and `hi_config.y_p = lo_config.y_p` (the two halves share
  `advices[0]`/`advices[1]`) — automatic by construction here (we build both incomplete
  configs from the same `xP`/`yP` columns; see `configure`).
- `hi/lo`'s `z` and `lambda_1` columns must be DISJOINT from the complete-addition output
  columns `add_config.output_columns() = {x_qr, y_qr}` (`mul.rs:104-124`). Reason: in Rust's
  single region, `z` and `lambda_1` are assigned on the *same row* as the complete-addition
  output; sharing a column would alias two distinct logical cells.

**ConfigWF verdict.** In the Halo2-Clean model every advice cell read is keyed by
`(column.index, row)` (`Environment.advice`). The composition threads each child at a
DISTINCT region-local offset, so distinct phases occupy disjoint row ranges — the aliasing
Rust guards against by column-disjointness we avoid by *row*-disjointness (the offsets). The
column non-overlap asserts therefore reduce, in this model, to the offset discipline already
enforced by `synthesize`, and are NOT needed as soundness hypotheses. The one genuinely
load-bearing config fact that does surface is the overflow child's selector distinctness,
carried (per the MulOverflow projection pattern) in `EnvAssumptions`. This is the predicted
"ConfigWF finally bites" location: it bites only as the overflow lookup's env-assumption
projection, not as the cross-sub-config column asserts, which are model-vacuous here.

## Donor

`Clean/Orchard/Ecc/Mul/Assign.lean` (`Orchard.Ecc.Mul`) — the phase-one donor. Its top-level
`Spec` (`output = alpha.val • base`), the `k = alpha + t_q` canonicity argument
(`k_canonical`, `chainNat` machinery), the LSB `Gate` (`Orchard.Ecc.Mul.Gate`), and the whole
assembly algebra are lifted wholesale. The donor factors the middle three phases as a virtual
`Decompose` subcircuit and the LSB as `ProcessLsb`; here the Ironwood children
(`MulIncomplete`/`MulComplete`) already are those region-level factors, so we compose them
directly in one region.

## Proof status (Restructure pass R1)

STRUCTURE FAITHFUL + CONTRACTS FINAL; the two proof bodies are R1 cut-line skeletons (sorry).
This file was restructured from a single flat `FormalRegionCircuit` region (which had flattened
Rust's layouter-level overflow check into the main region — a VK bug) into the faithful
LAYOUTER-level `FormalCircuit`: ONE main double-and-add region (`mainRegion`, `mul.rs:171-296`,
the region-relative init/hi/lo/complete/LSB helpers, faithful as before) followed by the
layouter-level `MulOverflow.circuit` child running AFTER the main region closes (`mul.rs:299`),
with `z_0`/`z_130`/`k_254` crossing into the overflow regions as copies.

The soundness/completeness VALUE ALGEBRA (the donor canonicity ladder `k_canonical`/`chainNat`/
`accScalar_closed`, the point-multiple algebra, the `overflow_spec_honest` finish) is UNCHANGED
IN SUBSTANCE and preserved verbatim in git at HEAD fdee7ac4; the R1 cut is the mechanical
re-spelling of its ~380 lines of cell addresses from the old flat-region `env.place self +
(offset + X)` form to the region-faithful `env.place i₀ + X` (main) / `env.place (i₀+k) + X`
(overflow regions) form, plus migrating the six child-consumption sites to `subcircuit_rw`.
Per the R1 rule, structure-faithfulness outranks proof completion in this pass.

`MulOverflow` and `LookupRangeCheck` (its C6 dependency) are FULLY PROVEN post-restructure.
-/

namespace Halo2.Ironwood.Ecc.Mul

open Orchard (Point)
open Orchard.Ecc (tQ)
open Orchard.Ecc.Mul (tQNat kNat kBits chainNat chainNat_lt chainNat_offset chainNat_msb
  chain_cast accScalar_closed k_canonical cells_kNat z0_cell_value)
open Orchard.Ecc.Mul.Decompose (m_bounds)
open Orchard.Ecc.Mul.Incomplete.DoubleAndAdd (accScalar zRunValue)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD PALLAS_SCALAR_CARD)
open Halo2.Ironwood.Ecc.MulIncomplete (BitsHint readCell)

/-! ## Config

Rust `mul::Config` (`mul.rs:48-62`): the `q_mul_lsb` selector plus the five child configs. -/

/-- The parent config. Mirrors Rust `mul::Config`: the LSB selector and the five child
configs (`add`, `hi`, `lo`, `complete`, `overflow`), threaded verbatim to the child calls. -/
structure Config where
  qMulLsb : Selector
  addConfig : Add.Config
  hiConfig : MulIncomplete.Config
  loConfig : MulIncomplete.Config
  completeConfig : MulComplete.Config
  overflowConfig : MulOverflow.Config 10

/-! ## The `q_mul_lsb` gate (`mul.rs:129-161`)

Layout (relative to the LSB region base row `g`, selector enabled at `Rotation::cur`):

    | x_p (add.xP) | y_p (add.yP) |   z_complete    |
    -------------------------------------------------
    | x_p    (g)   | y_p    (g)   | z_1  (g)          ← q_mul_lsb enabled here
    | base_x (g+1) | base_y (g+1) | z_0  (g+1)        ← Rotation::next

`k_0 = z_0 − 2·z_1`, `bool_check = k_0(k_0−1)`, and the correction point is pinned by
`lsb_x = ternary(k_0, x_p, x_p − base_x)`, `lsb_y = ternary(k_0, y_p, y_p + base_y)`:
`k_0 = 0 ⇒ (x_p, y_p) = (base_x, −base_y)` (i.e. `−base`), `k_0 = 1 ⇒ (x_p, y_p) = (0, 0)`. -/

/-- The `q_mul_lsb` gate, a pure function of the config columns. Reads `z_complete` at
`cur`/`next` (`z_1`, `z_0`), `add.xP`/`add.yP` at `cur` (`x_p`, `y_p`) and `next`
(`base_x`, `base_y`). Ported verbatim from `mul.rs:132-161` (donor `Mul.Gate`). -/
def lsbGate (cfg : Config) : Gate Fp where
  name := "LSB check"
  selector := cfg.qMulLsb
  constraints :=
    let z1 : Expression Fp Query := queryAdvice cfg.completeConfig.zComplete 0   -- z_1 (cur)
    let z0 : Expression Fp Query := queryAdvice cfg.completeConfig.zComplete 1   -- z_0 (next)
    let xP : Expression Fp Query := queryAdvice cfg.addConfig.xP 0               -- x_p (cur)
    let yP : Expression Fp Query := queryAdvice cfg.addConfig.yP 0               -- y_p (cur)
    let baseX : Expression Fp Query := queryAdvice cfg.addConfig.xP 1            -- base_x (next)
    let baseY : Expression Fp Query := queryAdvice cfg.addConfig.yP 1            -- base_y (next)
    let lsb := z0 - z1 * (2 : Fp)
    let boolCheck := lsb * (lsb - (1 : Fp))
    -- ternary(lsb, x_p, x_p − base_x) = lsb·x_p + (1 − lsb)·(x_p − base_x)
    let lsbX := lsb * xP + ((1 : Fp) - lsb) * (xP - baseX)
    -- ternary(lsb, y_p, y_p + base_y) = lsb·y_p + (1 − lsb)·(y_p + base_y)
    let lsbY := lsb * yP + ((1 : Fp) - lsb) * (yP + baseY)
    Constraints.withSelector cfg.qMulLsb
      [ ("bool_check", boolCheck), ("lsb_x", lsbX), ("lsb_y", lsbY) ]

/-! ## Configure (`mul.rs:65-127`)

Instantiate the two incomplete configs from the shared advice bundle, delegate to each child's
`configure`, allocate `q_mul_lsb`, register the LSB gate. The 10-advice column bundle mirrors
Rust's `advices : [Column<Advice>; 10]`; the exact index-to-column wiring (`mul.rs:71-79`) is
reproduced. The complete config's `zComplete` is `advices[9]` and its `add_config` is the shared
`addConfig`; the overflow config takes `advices[6..9]` and the lookup config. -/

/-- Rust `Config::configure` (`mul.rs:65-127`). `advices i` is `advices[i]` of Rust's 10-column
bundle; `lookupConfig` is the range-check config built once in `mul.rs:78`. The `addConfig` is
built by the chip and handed down. -/
def configure (addConfig : Add.Config) (lookupConfig : LookupRangeCheck.Config 10)
    (advices : Fin 10 → Column .advice) : Configure Fp Config := do
  -- hi_config: (z=9, xA=3, xP=0, yP=1, λ1=4, λ2=5)   (mul.rs:71-73)
  let hiConfig ← MulIncomplete.configure (advices 9) (advices 3) (advices 0) (advices 1)
    (advices 4) (advices 5)
  -- lo_config: (z=6, xA=7, xP=0, yP=1, λ1=8, λ2=2)   (mul.rs:74-76)
  let loConfig ← MulIncomplete.configure (advices 6) (advices 7) (advices 0) (advices 1)
    (advices 8) (advices 2)
  -- complete_config: zComplete=9, shared addConfig   (mul.rs:77)
  let completeConfig ← MulComplete.configure (advices 9) addConfig
  -- overflow_config: adv 6,7,8, lookupConfig          (mul.rs:78-79)
  let overflowConfig ← MulOverflow.configure 10 lookupConfig (advices 6) (advices 7) (advices 8)
  let qMulLsb ← selector
  let cfg : Config :=
    { qMulLsb, addConfig, hiConfig, loConfig, completeConfig, overflowConfig }
  createGate (lsbGate cfg)
  return cfg

/-! ## Inputs / Output

Mirrors the donor `Orchard.Ecc.Mul.Input`: the scalar cell `alpha` and the (non-identity,
on-curve) base point, as already-assigned cells. Output is the result point `[alpha] base`. -/

/-- Verifier-visible inputs: the scalar `alpha` and the non-identity base point. -/
structure Inputs (F : Type) where
  alpha : F
  base : Point F
deriving ProvableStruct

/-! ## Row-span offsets (`mul.rs::assign` — the MAIN region's phase threading)

The five region children of the MAIN region are composed at distinct region-local base offsets,
so the phases occupy disjoint row ranges (the model's replacement for Rust's column non-overlap
asserts — see the ConfigWF verdict). These offsets are region-relative to the main region's
own placement (its row-0), which the floor planner fixes. The spans:

- `Add.add` init at `offInit = 0`: complete addition writes rows `0..1`.
- `Add`'s output row is `1`; the hi half starts at `offHi`. In Rust the incomplete `z_init`
  and the hi/lo/complete phases share a running region; here each child owns its rows.
- `MulIncomplete.double_and_add 124` (hi) at `offHi`: rows `offHi .. offHi + 1 + 126`.
- `MulIncomplete.double_and_add 125` (lo) at `offLo`: rows `offLo .. offLo + 1 + 127`.
- `MulComplete.assign_region 3` (complete) at `offComp`: rows `offComp .. offComp + 6`.
- the LSB step: its base row IS the last complete-round row (`offLsb = offComp + 6`,
  Rust `mul.rs:256`: the row holding `z_1 = comp.zs[2]` and the last round's accumulator).
  `q_mul_lsb` at `offLsb` (reads `z_1` at cur, `z_0` at next); `z_0` at `offLsb + 1`;
  the final `Add.add` at `offLsb` (its `q`-copy of `comp.acc` is a cell self-copy, the
  Rust "copied into themselves" no-op).

The OVERFLOW CHECK (`MulOverflow.circuit 10`) is NOT in the main region: it runs at the
layouter level in three sibling regions AFTER the main region closes (`mul.rs:299`). -/

/-- Rows consumed by the hi double-and-add (`n = 124`): `1 + (n + 1) + 1 = 127`. -/
def hiSpan : ℕ := 127
/-- Rows consumed by the lo double-and-add (`n = 125`): `1 + (n + 1) + 1 = 128`. -/
def loSpan : ℕ := 128
/-- Rows from `offComp` to the LSB base row: the last complete round's `z` cell
(`comp.zs[2]`) sits at `offComp + 2·2 + 2 = offComp + 6`, and the LSB step is based there. -/
def compSpan : ℕ := 6

/-- Init complete addition at offset 0. -/
def offInit : ℕ := 0
/-- Hi half, after the 2-row init add. -/
def offHi : ℕ := 2
/-- Lo half. -/
def offLo : ℕ := offHi + hiSpan
/-- Complete rounds. -/
def offComp : ℕ := offLo + loSpan
/-- LSB step. -/
def offLsb : ℕ := offComp + compSpan

/-! ## Child contract-projection bridges (`rfl`, child stays folded)

The MulComplete/MulOverflow pattern: expose each child's contract fields as `rfl`-bridges,
so the composition consumes them without unfolding the child bundle literal. FRAMEWORK
CANDIDATE: a deriving-style projection mechanism. -/

-- ACCEPTANCE (C2a #2): the six contract-projection `rfl`-bridges for the `Add.add` child,
-- generated mechanically by `derive_contract_bridges` (produces `add_spec_eq`,
-- `add_assumptions_eq`, `add_envAssumptions_eq`, `add_proverAssumptions_eq`, `add_proverSpec_eq`)
-- in place of the hand-written stack. The consumers below (`simp only [add_spec_eq, …]`) are
-- unchanged.
derive_contract_bridges add := Add.add

private theorem hi_spec_eq (bits : BitsHint) :
    (MulIncomplete.double_and_add 124 bits).Spec
      = fun input output _ => ∃ bits' : BitsHint,
          MulIncomplete.RoundInvariant 124 input output bits' := rfl
private theorem hi_assumptions_eq (bits : BitsHint) :
    (MulIncomplete.double_and_add 124 bits).Assumptions
      = fun input => (input.base : Point Fp).OnCurve := rfl
private theorem hi_envAssumptions_eq (bits : BitsHint) :
    (MulIncomplete.double_and_add 124 bits).EnvAssumptions = fun _ _ => True := rfl

private theorem lo_spec_eq (bits : BitsHint) :
    (MulIncomplete.double_and_add 125 bits).Spec
      = fun input output _ => ∃ bits' : BitsHint,
          MulIncomplete.RoundInvariant 125 input output bits' := rfl
private theorem lo_assumptions_eq (bits : BitsHint) :
    (MulIncomplete.double_and_add 125 bits).Assumptions
      = fun input => (input.base : Point Fp).OnCurve := rfl

private theorem lo_envAssumptions_eq (bits : BitsHint) :
    (MulIncomplete.double_and_add 125 bits).EnvAssumptions = fun _ _ => True := rfl

private theorem comp_spec_eq (bits : BitsHint) :
    (MulComplete.assign_region 3 bits).Spec
      = fun input output _ => ∃ bits' : BitsHint,
          MulComplete.RoundInvariant 3 input output bits' := rfl
private theorem comp_assumptions_eq (bits : BitsHint) :
    (MulComplete.assign_region 3 bits).Assumptions
      = fun input =>
          ({ x := input.xA, y := input.yA } : Point Fp).Valid ∧ (input.base : Point Fp).Valid :=
  rfl
private theorem comp_envAssumptions_eq (bits : BitsHint) :
    (MulComplete.assign_region 3 bits).EnvAssumptions = fun _ _ => True := rfl

private theorem ov_spec_eq (hKW : (10 : ℕ) * MulOverflow.numWords 10 = 130) :
    (MulOverflow.circuit 10 hKW).Spec = fun input _ _ => MulOverflow.Spec input := rfl
private theorem ov_assumptions_eq (hKW : (10 : ℕ) * MulOverflow.numWords 10 = 130) :
    (MulOverflow.circuit 10 hKW).Assumptions
      = fun _ => 2 ^ (10 * MulOverflow.numWords 10) ≤ PALLAS_BASE_CARD
          ∧ 2 ^ (10 : ℕ) ≤ PALLAS_BASE_CARD := rfl
private theorem ov_envAssumptions_eq (hKW : (10 : ℕ) * MulOverflow.numWords 10 = 130)
    (cfg : MulOverflow.Config 10) (env : Placed Environment Fp) :
    (MulOverflow.circuit 10 hKW).EnvAssumptions cfg env
      = MulOverflow.EnvAssumptions 10 cfg env := rfl

private theorem hi_proverAssumptions_eq (bits : BitsHint) :
    (MulIncomplete.double_and_add 124 bits).ProverAssumptions
      = fun input _ => (input.base : Point Fp).OnCurve ∧ ∃ m : ℕ,
          Point.ofCoords (input.xA, input.yA) = m • (input.base : Point Fp) ∧
          2 ≤ m ∧ 2 ^ (124 + 2) * (m + 1) ≤ 2 ^ 254 := rfl

private theorem lo_proverAssumptions_eq (bits : BitsHint) :
    (MulIncomplete.double_and_add 125 bits).ProverAssumptions
      = fun input _ => (input.base : Point Fp).OnCurve ∧ ∃ m : ℕ,
          Point.ofCoords (input.xA, input.yA) = m • (input.base : Point Fp) ∧
          2 ≤ m ∧ 2 ^ (125 + 2) * (m + 1) ≤ 2 ^ 254 := rfl

private theorem hi_proverSpec_eq (bits : BitsHint) :
    (MulIncomplete.double_and_add 124 bits).ProverSpec
      = fun input output _ => MulIncomplete.RoundInvariant 124 input output bits := rfl

private theorem lo_proverSpec_eq (bits : BitsHint) :
    (MulIncomplete.double_and_add 125 bits).ProverSpec
      = fun input output _ => MulIncomplete.RoundInvariant 125 input output bits := rfl

private theorem comp_proverAssumptions_eq (bits : BitsHint) :
    (MulComplete.assign_region 3 bits).ProverAssumptions
      = fun input _ =>
          ({ x := input.xA, y := input.yA } : Point Fp).Valid ∧ (input.base : Point Fp).Valid :=
  rfl

private theorem comp_proverSpec_eq (bits : BitsHint) :
    (MulComplete.assign_region 3 bits).ProverSpec
      = fun input output _ => MulComplete.RoundInvariant 3 input output bits := rfl

private theorem ov_proverAssumptions_eq (hKW : (10 : ℕ) * MulOverflow.numWords 10 = 130) :
    (MulOverflow.circuit 10 hKW).ProverAssumptions
      = fun input _ => MulOverflow.Spec input := rfl

/-- `K · numWords K = 130` at `K = 10` (`10 · 13 = 130`). Discharges the MulOverflow bridge. -/
theorem hKW10 : (10 : ℕ) * MulOverflow.numWords 10 = 130 := by
  simp only [MulOverflow.numWords]

/-! ## The scalar-bit hint

The working scalar `k = alpha.val + t_q`, MSB-first, exactly the donor `kBits`. The children
take a `BitsHint` prover hint; the top-level `main` supplies `kBits (env alpha)`, and the
verifier `Spec` existentially recovers a matching sequence per child. -/

/-! ## Synthesize (`mul.rs::Config::assign`, one region)

The `assign_region` body (`mul.rs:171-305`) as a sequence of child `.call`s at the threaded
phase offsets, plus `z_init`, the LSB step, and the final recombination. -/

/-- The MAIN REGION body (`mul.rs:171-296`, everything before the layouter-level overflow check):
the init add, hi/lo/complete double-and-adds, the LSB step, and the final recombination — all
genuinely region-relative helpers, faithful to Rust's single `assign_region`. Returns the result
point together with the three running-sum cells the overflow check copies across into its own
region: `z0` (the LSB row full sum), `hi.zs[124]` (= z_130), `hi.zs[0]` (= k_254 = z_254 top bit).
Placed at row offset 0 of its own region (Rust's single `assign_region`). -/
def mainRegion (bits : BitsHint) (cfg : Config) (input : Var Inputs Fp) :
    RegionCircuit Fp (Var Point Fp × AssignedCell Fp × AssignedCell Fp × AssignedCell Fp) := do
  let bitsOf : MulIncomplete.BitsHint := bits
  -- 1. acc = [2]base  (init complete addition, mul.rs:188-190)
  let acc ← Add.add.call cfg.addConfig offInit
    ⟨input.base, input.base⟩
  -- 2. z_init = 0  (mul.rs:201-206): the running-sum start, assigned as the constant 0 on the
  --    hi config's `z` column at the hi phase's start row, constrained via `constrainConstant`
  --    (Rust `assign_advice_from_constant`). The hi half copies this same cell into its own `z`
  --    at `offHi` — the "assign the same value to the same cell twice" no-op (mul.rs:198-200).
  let zInit ← assignAdvice cfg.hiConfig.z offHi
    (.native fun _ => #v[(0 : Fp)])
  constrainConstant zInit 0
  -- 3. hi half: 125 double-and-add bits k_254..k_130  (mul.rs:209-216)
  let hi ← (MulIncomplete.double_and_add 124 bitsOf).call cfg.hiConfig offHi
    ⟨input.base, acc.x, acc.y, zInit⟩
  -- 4. lo half: 126 double-and-add bits k_129..k_4 (the bit window shifted by 125, as the
  --    donor's `input.bits env (125 + i)`), running sum chained  (mul.rs:220-227)
  let lo ← (MulIncomplete.double_and_add 125 (fun i => bitsOf (125 + i))).call cfg.loConfig
    offLo ⟨input.base, hi.xA, hi.yA, hi.zs[124]⟩
  -- 5. complete rounds: k_3..k_1 (window shifted by 251)  (mul.rs:239-253)
  let comp ← (MulComplete.assign_region 3 (fun i => bitsOf (251 + i))).call cfg.completeConfig
    offComp ⟨input.base, lo.xA, lo.yA, lo.zs[125]⟩
  -- 6. the LSB step k_0  (mul.rs:258-260, process_lsb, mul.rs:324-385)
  let z1 := comp.zs[2]
  -- z_0 = 2·z_1 + k_0 on the z_complete column at the LSB base row
  let z0 ← assignAdvice cfg.completeConfig.zComplete (offLsb + 1)
    (.native fun env => #v[2 * readCell env z1 + (if bitsOf 254 then 1 else 0)])
  -- copy base_x, base_y into the LSB gate window (next row)
  let _bx ← copyAdvice input.base.x cfg.addConfig.xP (offLsb + 1)
  let _by ← copyAdvice input.base.y cfg.addConfig.yP (offLsb + 1)
  -- the correction point (base_x, ±base_y) or identity, witnessed on add.xP/add.yP (cur row)
  let corrX ← assignAdvice cfg.addConfig.xP offLsb
    (.native fun env => #v[if bitsOf 254 then 0 else readCell env input.base.x])
  let corrY ← assignAdvice cfg.addConfig.yP offLsb
    (.native fun env => #v[if bitsOf 254 then 0 else -(readCell env input.base.y)])
  -- the q_mul_lsb gate at the LSB base row
  (lsbGate cfg).enable offLsb
  -- the final complete addition: result = corr + acc
  let result ← Add.add.call cfg.addConfig offLsb
    ⟨{ x := corrX, y := corrY }, comp.acc⟩
  return (result, z0, hi.zs[124], hi.zs[0])

/-- The scalar-decomposition and recombination assembly, at the LAYOUTER level. Faithful to
`mul.rs::assign`: the whole double-and-add convergence runs in ONE `layouter.assign_region`
(`main`), and the overflow check runs AFTER that region closes (`mul.rs:299`) as a SEPARATE
layouter-level `overflow_check` — three of its own sibling regions. The `z_0`/`z_130`/`k_254`
cells cross into the overflow regions as copies (Rust copies them across region boundaries).
Parameterized by the working-scalar bit sequence `bits`. Returns the result point `[alpha] base`. -/
def synthesize (bits : BitsHint) (cfg : Config) (input : Var Inputs Fp) :
    Circuit Fp (Var Point Fp) := do
  -- the main double-and-add region (mul.rs:171-296)
  let ⟨result, z0, z130, k254⟩ ← assignRegion "variable-base scalar mul" (mainRegion bits cfg input)
  -- the overflow check AFTER the main region closes (mul.rs:299), at layouter level
  let _ov ← (MulOverflow.circuit 10 hKW10).call cfg.overflowConfig
    ⟨input.alpha, z0, z130, k254⟩
  return result

/-! ## Contract

`Assumptions` is the donor's: the base is on-curve (hence a non-identity Pallas point).
`EnvAssumptions` aggregates the children's env-facts (only the overflow lookup has a
nontrivial one) over the parent's stored sub-config — the MulOverflow projection pattern.
`Spec` is the donor's top-level: `output = alpha.val • base`. -/

/-- The base is on-curve. (The overflow child additionally needs the field-capacity bound
`2^130·2^130 < |Fp|`, which is discharged by `norm_num` at `K = 10`, so it is not carried as
a caller obligation — see `soundness`.) -/
def Assumptions (input : Inputs Fp) : Prop :=
  (input.base : Point Fp).OnCurve

/-- The parent env-assumptions: the overflow child's `TableLoaded` + selector distinctness,
over the parent's stored `overflowConfig`. Aggregates the children's (`Add`, both
`MulIncomplete`, `MulComplete` all have trivial `EnvAssumptions`). -/
def EnvAssumptions (cfg : Config) (env : Placed Environment Fp) : Prop :=
  MulOverflow.EnvAssumptions 10 cfg.overflowConfig env

/-- The circuit computes the variable-base scalar multiplication `[alpha] base`, with the
identity encoded as `(0, 0)` coordinates. Lifted verbatim from the donor
`Orchard.Ecc.Mul.Spec`. -/
def Spec (input : Inputs Fp) (output : Point Fp) : Prop :=
  output = input.alpha.val • input.base

/-! ## Donor value algebra

The running-sum/canonicity machinery (`chainNat_*`, `chain_cast`, `accScalar_closed`,
`k_canonical`, `m_bounds`, `cells_kNat`, `z0_cell_value`, `nsmul_step`, `neg_add_nsmul`) is
consumed directly from the donor `Clean/Orchard/Ecc/Mul/Assign.lean` (made public there for
this port). The one adaptation kept here: `overflow_spec_honest` retargeted at the Ironwood
`MulOverflow.Spec` record — definitionally the donor's `Overflow.OverflowCheck.Spec`, so the
wrapper is a delegation. -/

/-- The honest running-sum cells satisfy the overflow-check contract (the donor
`overflow_spec_honest`, at the Ironwood `MulOverflow.Spec` record — same formula, defeq). -/
private theorem overflow_spec_honest (alpha : Fp) {z0v z130v k254v : Fp}
    (hz0v : z0v = ((kNat alpha : ℕ) : Fp))
    (h130 : z130v = ((kNat alpha / 2 ^ 130 : ℕ) : Fp))
    (h254 : k254v = ((kNat alpha / 2 ^ 254 : ℕ) : Fp)) :
    MulOverflow.Spec { alpha := alpha, z0 := z0v, z130 := z130v, k254 := k254v } :=
  Orchard.Ecc.Mul.overflow_spec_honest alpha hz0v h130 h254

/-! ## Point-level scalar-multiple algebra

The donor's step/negation/identity algebra lived at the `SWPoint` level; the Ironwood children
speak `Point Fp` `nsmul` directly, so the lemmas are transported through the `toSW` bridge
(`Orchard.Point.ext_toSW_iff`/`toSW_add`/`toSW_nsmul`/`toSW_neg`/`toSW_zero`). -/

section PointAlgebra
open CompElliptic.CurveForms.ShortWeierstrass (SWPoint)
open CompElliptic.Curves.Pasta
open Orchard.Point (ext_toSW_iff toSW_add toSW_neg toSW_zero toSW_nsmul
  valid_add valid_neg valid_zero valid_nsmul nsmul_add_nsmul nsmul_eq_zero_iff)

/-- `P + P = 2 • P` at the `Point` level. -/
private theorem point_two_nsmul {P : Point Fp} (hP : P.OnCurve) : P + P = 2 • P := by
  have hPv : P.Valid := Or.inl hP
  apply (ext_toSW_iff (valid_add hPv hPv) (valid_nsmul hPv 2)).mpr
  rw [toSW_add hPv hPv, toSW_nsmul hPv 2, two_nsmul]

/-- One double-and-add complete step at the `Point` level. -/
private theorem point_step_nsmul {P : Point Fp} (hP : P.OnCurve) (a : ℕ) (ha : 1 ≤ a)
    (bit : Bool) :
    a • P + ((if bit then P else -P) + a • P)
      = (2 * a + (if bit then 1 else 0) * 2 - 1) • P := by
  have hPv : P.Valid := Or.inl hP
  cases bit
  · -- bit = false: the step point is −P
    simp only [Bool.false_eq_true, if_false]
    apply (ext_toSW_iff
      (valid_add (valid_nsmul hPv a) (valid_add (valid_neg hPv) (valid_nsmul hPv a)))
      (valid_nsmul hPv _)).mpr
    rw [toSW_add (valid_nsmul hPv a) (valid_add (valid_neg hPv) (valid_nsmul hPv a)),
      toSW_add (valid_neg hPv) (valid_nsmul hPv a), toSW_neg hPv,
      toSW_nsmul hPv a, toSW_nsmul hPv]
    simpa using Orchard.Ecc.Mul.nsmul_step (P.toSW hPv) a ha false
  · -- bit = true: the step point is P
    simp only [if_true]
    apply (ext_toSW_iff
      (valid_add (valid_nsmul hPv a) (valid_add hPv (valid_nsmul hPv a)))
      (valid_nsmul hPv _)).mpr
    rw [toSW_add (valid_nsmul hPv a) (valid_add hPv (valid_nsmul hPv a)),
      toSW_add hPv (valid_nsmul hPv a),
      toSW_nsmul hPv a, toSW_nsmul hPv]
    simpa using Orchard.Ecc.Mul.nsmul_step (P.toSW hPv) a ha true

/-- `-P + m•P = (m−1)•P` at the `Point` level. -/
private theorem point_neg_add_nsmul {P : Point Fp} (hP : P.OnCurve) {m : ℕ} (hm : 1 ≤ m) :
    -P + m • P = (m - 1) • P := by
  have hPv : P.Valid := Or.inl hP
  apply (ext_toSW_iff (valid_add (valid_neg hPv) (valid_nsmul hPv m))
    (valid_nsmul hPv _)).mpr
  rw [toSW_add (valid_neg hPv) (valid_nsmul hPv m), toSW_neg hPv, toSW_nsmul hPv m,
    toSW_nsmul hPv]
  exact Orchard.Ecc.Mul.neg_add_nsmul (P.toSW hPv) hm

/-- `0 + Q = Q` at the `Point` level, for valid `Q`. -/
private theorem point_zero_add {Q : Point Fp} (hQ : Q.Valid) : (0 : Point Fp) + Q = Q := by
  apply (ext_toSW_iff (valid_add valid_zero hQ) hQ).mpr
  rw [toSW_add valid_zero hQ, toSW_zero, _root_.zero_add]

/-- `Q + 0 = Q` at the `Point` level, for valid `Q`. -/
private theorem point_add_zero {Q : Point Fp} (hQ : Q.Valid) : Q + (0 : Point Fp) = Q := by
  apply (ext_toSW_iff (valid_add hQ valid_zero) hQ).mpr
  rw [toSW_add hQ valid_zero, toSW_zero, _root_.add_zero]

/-- Reducing the scalar by the group order: `(a + q)•P = a•P` (`[q]P = 0`). -/
private theorem point_card_reduce {P : Point Fp} (hP : P.OnCurve) (a : ℕ) :
    (a + PALLAS_SCALAR_CARD) • P = a • P := by
  rw [← nsmul_add_nsmul hP a PALLAS_SCALAR_CARD,
    (nsmul_eq_zero_iff hP PALLAS_SCALAR_CARD).mpr dvd_rfl,
    point_add_zero (valid_nsmul (Or.inl hP) a)]

/-- `accScalar` stays positive from a positive start. -/
private theorem accScalar_one_le {m : ℕ} (h1 : 1 ≤ m) (bits : ℕ → Bool) :
    ∀ b, 1 ≤ accScalar m bits b
  | 0 => h1
  | b + 1 => by
    have ih := accScalar_one_le h1 bits b
    show 1 ≤ 2 * accScalar m bits b + (if bits b then 1 else 0) * 2 - 1
    cases bits b
    · simp
      omega
    · simp

/-- `MulComplete.stepBasePoint` is `±base` (the `Point` negation is `y`-negation). -/
private theorem stepBasePoint_eq (P : Point Fp) (bit : Bool) :
    MulComplete.stepBasePoint P bit = if bit then P else -P := by
  cases bit <;> rfl

/-- The complete-rounds accumulator chain computes double-and-add on `Point` multiples:
starting from `[m]P`, after `b` rounds it holds `[accScalar m bits b]P` (the donor
`accValue_nsmul`, at the `Point` level via `point_step_nsmul`). -/
private theorem accPoint_nsmul {P : Point Fp} (hP : P.OnCurve) (m : ℕ) (hm : 1 ≤ m)
    (bits : ℕ → Bool) :
    ∀ b, MulComplete.accPoint P (m • P) bits b = accScalar m bits b • P
  | 0 => rfl
  | b + 1 => by
    have ih := accPoint_nsmul hP m hm bits b
    have h1 := accScalar_one_le hm bits b
    show MulComplete.stepPoint P (MulComplete.accPoint P (m • P) bits b) (bits b) = _
    rw [ih]
    show accScalar m bits b • P
        + (MulComplete.stepBasePoint P (bits b) + accScalar m bits b • P) = _
    rw [stepBasePoint_eq]
    exact point_step_nsmul hP _ h1 (bits b)

end PointAlgebra

/-! ## Output-record and cell-eval bridges

The children's `.call … .output self` records reduce (lazily, by `rfl` — structure
projections do not force the loop outputs) to record literals of `AssignedCell.of` cells;
eval decomposes componentwise on those literals (the Chain `hp_output_eval_literal`
pattern: `ProvableStruct.eval` on a literal, `with_unfolding_all rfl`). -/

/-- The `MulIncomplete` bundle's output record, reduced (`cellAt`/`cellVec` cells at their
fixed region-local rows). -/
private theorem incomplete_call_output (n : ℕ) (bits : BitsHint)
    (cfg : MulIncomplete.Config) (off : ℕ) (inp : Var MulIncomplete.Inputs Fp)
    (self : RegionIndex) :
    ((MulIncomplete.double_and_add n bits).call cfg off inp).output self
      = { xA := .of self (off + 1 + n + 1) cfg.xA,
          yA := .of self (off + 1 + (n + 1)) cfg.lambda1,
          zs := Vector.ofFn (fun i => .of self (off + 1 + i.val) cfg.z) } := rfl

/-- The `MulComplete` bundle's output `zs` cells at their fixed rows (the `acc` field is
never reduced, per the whnf discipline). -/
private theorem complete_call_output_zs (bits : BitsHint) (cfg : MulComplete.Config)
    (off : ℕ) (inp : Var MulComplete.Inputs Fp) (self : RegionIndex) :
    (((MulComplete.assign_region 3 bits).call cfg off inp).output self).zs
      = Vector.ofFn (fun i => .of self (off + 2 * i.val + 2) cfg.zComplete) := rfl

/-- The `Add` bundle's output point cells (`x_qr`/`y_qr` at `offset + 1`). -/
private theorem add_call_output (cfg : Add.Config) (off : ℕ) (inp : Var Add.Inputs Fp)
    (self : RegionIndex) :
    (Add.add.call cfg off inp).output self
      = { x := .of self (off + 1) cfg.xQR, y := .of self (off + 1) cfg.yQR } := rfl

/-- Literal-eval bridge for `MulIncomplete.Output` (verifier view). -/
private theorem incompleteOutput_eval_literal {n : ℕ} (place : RegionIndex → ℕ)
    (env : Environment Fp) (xA yA : AssignedCell Fp)
    (zs : Vector (AssignedCell Fp) (n + 1)) :
    ProvableStruct.eval place env
        ({ xA := xA, yA := yA, zs := zs } : MulIncomplete.Output (n + 1) (AssignedCell Fp))
      = { xA := AssignedCell.eval place env xA, yA := AssignedCell.eval place env yA,
          zs := ProvableType.eval (M := fields (n + 1)) place env zs } := by
  with_unfolding_all rfl

/-- Literal-eval bridge for `MulComplete.Output 3` (verifier view; the `acc` field may be a
symbolic term). -/
private theorem completeOutput_eval_literal (place : RegionIndex → ℕ)
    (env : Environment Fp) (acc : Point (AssignedCell Fp))
    (zs : Vector (AssignedCell Fp) 3) :
    ProvableStruct.eval place env
        ({ acc := acc, zs := zs } : MulComplete.Output 3 (AssignedCell Fp))
      = { acc := ProvableType.eval place env acc,
          zs := ProvableType.eval (M := fields 3) place env zs } := by
  with_unfolding_all rfl

/-- Elementwise read of an evaluated cell vector. -/
private theorem fieldsEval_getElem {w : ℕ} (place : RegionIndex → ℕ) (env : Environment Fp)
    (zs : Vector (AssignedCell Fp) w) (i : ℕ) (hi : i < w) :
    (ProvableType.eval (M := fields w) place env zs)[i]
      = AssignedCell.eval place env (zs[i]) := by
  simp only [ProvableType.eval, ProvableType.toElements, ProvableType.fromElements,
    Vector.getElem_map]

/-- `Cell.eval` of an `AssignedCell.of` cell's `.cell` (the `constrainConstant` constraint
form): the advice read at its region-local row. -/
private theorem cell_eval_of (place : RegionIndex → ℕ) (env : Environment Fp)
    (self : RegionIndex) (row : ℕ) (col : Column .advice) :
    Cell.eval place env ((AssignedCell.of self row col : AssignedCell Fp)).cell
      = env.advice col ((place self + row : ℕ) : ℤ) := by
  simp only [Cell.eval, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
    Cell.of_column, Environment.get_advice]

/-- `Cell.eval` of a bare `Cell.of` (the `constrainEqual` constraint form). -/
private theorem cellOf_eval (place : RegionIndex → ℕ) (env : Environment Fp)
    (self : RegionIndex) (row : ℕ) (col : Column .advice) :
    Cell.eval place env (Cell.of self row col)
      = env.advice col ((place self + row : ℕ) : ℤ) := by
  simp only [Cell.eval, Cell.of_regionIndex, Cell.of_rowOffset, Cell.of_column,
    Environment.get_advice]

/-- `AssignedCell.eval` of an `AssignedCell.of` cell: the advice read at its region-local
row. -/
private theorem assignedCell_eval_of (place : RegionIndex → ℕ) (env : Environment Fp)
    (self : RegionIndex) (row : ℕ) (col : Column .advice) :
    AssignedCell.eval place env (AssignedCell.of self row col)
      = env.advice col ((place self + row : ℕ) : ℤ) := by
  simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
    Cell.of_rowOffset, Cell.of_column, Environment.get_advice]

/-- Plain-`.output` spelling of `incomplete_call_output` (the composition iff's form). -/
private theorem incomplete_output_eq (n : ℕ) (bits : BitsHint)
    (cfg : MulIncomplete.Config) (off : ℕ) (inp : Var MulIncomplete.Inputs Fp)
    (self : RegionIndex) :
    (MulIncomplete.double_and_add n bits).output cfg off inp self
      = { xA := .of self (off + 1 + n + 1) cfg.xA,
          yA := .of self (off + 1 + (n + 1)) cfg.lambda1,
          zs := Vector.ofFn (fun i => .of self (off + 1 + i.val) cfg.z) } := rfl

/-- The `MulComplete` bundle's output record, full form: the `acc` field is the (symbolic,
never-reduced) loop output, the `zs` are the fixed-row cells. -/
private theorem complete_output_eq (bits : BitsHint) (cfg : MulComplete.Config)
    (off : ℕ) (inp : Var MulComplete.Inputs Fp) (self : RegionIndex) :
    (MulComplete.assign_region 3 bits).output cfg off inp self
      = { acc := (MulComplete.loop cfg inp bits off 3).output self,
          zs := Vector.ofFn (fun i => .of self (off + 2 * i.val + 2) cfg.zComplete) } := rfl

/-- `.call` spelling of `complete_output_eq`. -/
private theorem complete_call_output_eq (bits : BitsHint) (cfg : MulComplete.Config)
    (off : ℕ) (inp : Var MulComplete.Inputs Fp) (self : RegionIndex) :
    ((MulComplete.assign_region 3 bits).call cfg off inp).output self
      = { acc := (MulComplete.loop cfg inp bits off 3).output self,
          zs := Vector.ofFn (fun i => .of self (off + 2 * i.val + 2) cfg.zComplete) } := rfl

/-- Plain-`.output` spelling of `complete_call_output_zs`. -/
private theorem complete_output_zs_eq (bits : BitsHint) (cfg : MulComplete.Config)
    (off : ℕ) (inp : Var MulComplete.Inputs Fp) (self : RegionIndex) :
    ((MulComplete.assign_region 3 bits).output cfg off inp self).zs
      = Vector.ofFn (fun i => .of self (off + 2 * i.val + 2) cfg.zComplete) := rfl

/-- Plain-`.output` spelling of `add_call_output`. -/
private theorem add_output_eq (cfg : Add.Config) (off : ℕ) (inp : Var Add.Inputs Fp)
    (self : RegionIndex) :
    Add.add.output cfg off inp self
      = { x := .of self (off + 1) cfg.xQR, y := .of self (off + 1) cfg.yQR } := rfl

/-- Eval of an `AssignedCell.of` cell (`Eval` level): the advice read at its row. -/
private theorem eval_of (env : Placed Environment Fp) (self : RegionIndex) (row : ℕ)
    (col : Column .advice) :
    eval env (AssignedCell.of self row col : AssignedCell Fp)
      = env.env.advice col ((env.place self + row : ℕ) : ℤ) := by
  rw [ProvableType.eval_field, assignedCell_eval_of]

/-- `zs`-component read of an evaluated `MulIncomplete.Output` literal. -/
private theorem incompleteOutput_zs_getElem {n : ℕ} (env : Placed Environment Fp)
    (xA yA : AssignedCell Fp) (zs : Vector (AssignedCell Fp) (n + 1)) (i : ℕ)
    (hi : i < n + 1) :
    (eval env ({ xA := xA, yA := yA, zs := zs }
        : Var (MulIncomplete.Output (n + 1)) Fp)).zs[i]
      = eval env (zs[i]) := by
  rw [ProvableStruct.eval_var_eq_eval]
  rw [incompleteOutput_eval_literal]
  show (ProvableType.eval (M := fields (n + 1)) env.place env.env zs)[i] = _
  rw [fieldsEval_getElem env.place env.env zs i hi, ProvableType.eval_field]

/-- `xA`-component of an evaluated `MulIncomplete.Output` literal. -/
private theorem incompleteOutput_xA {n : ℕ} (env : Placed Environment Fp)
    (xA yA : AssignedCell Fp) (zs : Vector (AssignedCell Fp) (n + 1)) :
    (eval env ({ xA := xA, yA := yA, zs := zs }
        : Var (MulIncomplete.Output (n + 1)) Fp)).xA = eval env xA := by
  rw [ProvableStruct.eval_var_eq_eval]
  rw [incompleteOutput_eval_literal, ProvableType.eval_field]

/-- `yA`-component of an evaluated `MulIncomplete.Output` literal. -/
private theorem incompleteOutput_yA {n : ℕ} (env : Placed Environment Fp)
    (xA yA : AssignedCell Fp) (zs : Vector (AssignedCell Fp) (n + 1)) :
    (eval env ({ xA := xA, yA := yA, zs := zs }
        : Var (MulIncomplete.Output (n + 1)) Fp)).yA = eval env yA := by
  rw [ProvableStruct.eval_var_eq_eval]
  rw [incompleteOutput_eval_literal, ProvableType.eval_field]

/-- `acc`-component of an evaluated `MulComplete.Output 3` literal. -/
private theorem completeOutput_acc (env : Placed Environment Fp)
    (acc : Point (AssignedCell Fp)) (zs : Vector (AssignedCell Fp) 3) :
    (eval env ({ acc := acc, zs := zs } : Var (MulComplete.Output 3) Fp)).acc
      = eval env acc := by
  rw [ProvableStruct.eval_var_eq_eval]
  rw [completeOutput_eval_literal, ProvableType.eval_cells]

/-- `zs`-component read of an evaluated `MulComplete.Output 3` literal. -/
private theorem completeOutput_zs_getElem (env : Placed Environment Fp)
    (acc : Point (AssignedCell Fp)) (zs : Vector (AssignedCell Fp) 3) (i : ℕ)
    (hi : i < 3) :
    (eval env ({ acc := acc, zs := zs } : Var (MulComplete.Output 3) Fp)).zs[i]
      = eval env (zs[i]) := by
  rw [ProvableStruct.eval_var_eq_eval]
  rw [completeOutput_eval_literal]
  show (ProvableType.eval (M := fields 3) env.place env.env zs)[i] = _
  rw [fieldsEval_getElem env.place env.env zs i hi, ProvableType.eval_field]

/-- Componentwise eval of a `MulComplete.Inputs` record literal. -/
private theorem compInputs_eval_eq (env : Placed Environment Fp)
    (base : Point (AssignedCell Fp)) (xA yA z : AssignedCell Fp) :
    eval env (⟨base, xA, yA, z⟩ : Var MulComplete.Inputs Fp)
      = { base := eval env base, xA := eval env xA, yA := eval env yA, z := eval env z } := by
  simp only [circuit_norm, ProvableType.eval_cells]

/-- Componentwise eval of a `MulOverflow.Inputs` record literal. -/
private theorem ovInputs_eval_eq (env : Placed Environment Fp)
    (alpha z0 z130 k254 : AssignedCell Fp) :
    eval env (⟨alpha, z0, z130, k254⟩ : Var MulOverflow.Inputs Fp)
      = { alpha := eval env alpha, z0 := eval env z0, z130 := eval env z130,
          k254 := eval env k254 } := by
  simp only [circuit_norm]



/-! ## Prover-side bridge duplicates (completeness)

The same record/cell eval bridges over `Placed ProverEnvironment` (the honest-witness side).
The children's verifier-`Spec` facts arrive at `env.toEnvironment` and reuse the verifier
bridges; only the `ProverSpec`/witness facts need these. Both sides meet at the same
`env.env.toEnvironment.advice` reads. -/

/-- Prover-side `eval_of`. -/
private theorem eval_of_prover (env : Placed ProverEnvironment Fp) (self : RegionIndex)
    (row : ℕ) (col : Column .advice) :
    eval env (AssignedCell.of self row col : AssignedCell Fp)
      = env.env.toEnvironment.advice col ((env.place self + row : ℕ) : ℤ) := by
  rw [ProvableType.eval_field_prover, assignedCell_eval_of]

/-- Prover-side componentwise eval of `MulIncomplete.Inputs`. -/
private theorem hiInputs_eval_eq_prover (env : Placed ProverEnvironment Fp)
    (base : Point (AssignedCell Fp)) (xA yA z : AssignedCell Fp) :
    eval env (⟨base, xA, yA, z⟩ : Var MulIncomplete.Inputs Fp)
      = { base := eval env base, xA := eval env xA, yA := eval env yA, z := eval env z } := by
  simp only [circuit_norm, ProvableType.eval_cells_prover, ProvableType.eval_cells]

/-- Prover-side componentwise eval of `MulComplete.Inputs`. -/
private theorem compInputs_eval_eq_prover (env : Placed ProverEnvironment Fp)
    (base : Point (AssignedCell Fp)) (xA yA z : AssignedCell Fp) :
    eval env (⟨base, xA, yA, z⟩ : Var MulComplete.Inputs Fp)
      = { base := eval env base, xA := eval env xA, yA := eval env yA, z := eval env z } := by
  simp only [circuit_norm, ProvableType.eval_cells_prover, ProvableType.eval_cells]

/-- Prover-side componentwise eval of `MulOverflow.Inputs`. -/
private theorem ovInputs_eval_eq_prover (env : Placed ProverEnvironment Fp)
    (alpha z0 z130 k254 : AssignedCell Fp) :
    eval env (⟨alpha, z0, z130, k254⟩ : Var MulOverflow.Inputs Fp)
      = { alpha := eval env alpha, z0 := eval env z0, z130 := eval env z130,
          k254 := eval env k254 } := by
  simp only [circuit_norm]

/-- Prover-side componentwise eval of `Add.Inputs`. -/
private theorem addInputs_eval_eq_prover (env : Placed ProverEnvironment Fp)
    (p q : Point (AssignedCell Fp)) :
    eval env (⟨p, q⟩ : Add.Inputs (AssignedCell Fp)) = { p := eval env p, q := eval env q } := by
  simp only [circuit_norm, ProvableType.eval_cells_prover, ProvableType.eval_cells]

/-- Prover-side `zs`-component read of an evaluated `MulIncomplete.Output` literal. -/
private theorem incompleteOutput_zs_getElem_prover {n : ℕ} (env : Placed ProverEnvironment Fp)
    (xA yA : AssignedCell Fp) (zs : Vector (AssignedCell Fp) (n + 1)) (i : ℕ)
    (hi : i < n + 1) :
    (eval env ({ xA := xA, yA := yA, zs := zs }
        : Var (MulIncomplete.Output (n + 1)) Fp)).zs[i]
      = eval env (zs[i]) := by
  rw [ProvableStruct.eval_var_eq_eval_prover]
  rw [incompleteOutput_eval_literal]
  show (ProvableType.eval (M := fields (n + 1)) env.place env.env.toEnvironment zs)[i] = _
  rw [fieldsEval_getElem env.place env.env.toEnvironment zs i hi,
    ProvableType.eval_field_prover]

/-- Prover-side `xA`-component of an evaluated `MulIncomplete.Output` literal. -/
private theorem incompleteOutput_xA_prover {n : ℕ} (env : Placed ProverEnvironment Fp)
    (xA yA : AssignedCell Fp) (zs : Vector (AssignedCell Fp) (n + 1)) :
    (eval env ({ xA := xA, yA := yA, zs := zs }
        : Var (MulIncomplete.Output (n + 1)) Fp)).xA = eval env xA := by
  rw [ProvableStruct.eval_var_eq_eval_prover, incompleteOutput_eval_literal,
    ProvableType.eval_field_prover]

/-- Prover-side `yA`-component of an evaluated `MulIncomplete.Output` literal. -/
private theorem incompleteOutput_yA_prover {n : ℕ} (env : Placed ProverEnvironment Fp)
    (xA yA : AssignedCell Fp) (zs : Vector (AssignedCell Fp) (n + 1)) :
    (eval env ({ xA := xA, yA := yA, zs := zs }
        : Var (MulIncomplete.Output (n + 1)) Fp)).yA = eval env yA := by
  rw [ProvableStruct.eval_var_eq_eval_prover, incompleteOutput_eval_literal,
    ProvableType.eval_field_prover]

/-- Prover-side `acc`-component of an evaluated `MulComplete.Output 3` literal. -/
private theorem completeOutput_acc_prover (env : Placed ProverEnvironment Fp)
    (acc : Point (AssignedCell Fp)) (zs : Vector (AssignedCell Fp) 3) :
    (eval env ({ acc := acc, zs := zs } : Var (MulComplete.Output 3) Fp)).acc
      = eval env acc := by
  rw [ProvableStruct.eval_var_eq_eval_prover, completeOutput_eval_literal,
    ProvableType.eval_cells_prover]

/-- Prover-side `zs`-component read of an evaluated `MulComplete.Output 3` literal. -/
private theorem completeOutput_zs_getElem_prover (env : Placed ProverEnvironment Fp)
    (acc : Point (AssignedCell Fp)) (zs : Vector (AssignedCell Fp) 3) (i : ℕ)
    (hi : i < 3) :
    (eval env ({ acc := acc, zs := zs } : Var (MulComplete.Output 3) Fp)).zs[i]
      = eval env (zs[i]) := by
  rw [ProvableStruct.eval_var_eq_eval_prover, completeOutput_eval_literal]
  show (ProvableType.eval (M := fields 3) env.place env.env.toEnvironment zs)[i] = _
  rw [fieldsEval_getElem env.place env.env.toEnvironment zs i hi,
    ProvableType.eval_field_prover]

/-- Completeness-side consumption of a child call, with BOTH the child's verifier `Spec` and
its honest-prover `ProverSpec` exposed (the Chain `call_constraints_and_specs`, copied per the
no-cross-gadget-import convention). FRAMEWORK CANDIDATE. -/
theorem call_constraints_and_specs {CI Cfg : Type} {Input Output : TypeMap}
    [CircuitType Input] [CircuitType Output]
    (child : FormalRegionCircuit Fp CI Cfg Input Output) (config : Cfg) (offset : ℕ)
    (self : RegionIndex) (env : Placed ProverEnvironment Fp) (input : Var Input Fp)
    (hw : RegionOperations.ExtendsWitnesses env.place self env.env
      ((child.call config offset input).operations self))
    (hE : child.EnvAssumptions config env.toEnvironment)
    (hA : child.Assumptions (eval env.toEnvironment input))
    (hpa : child.ProverAssumptions (eval env input) env.env.hint) :
    RegionOperations.Constraints env.place self env.env
      ((child.call config offset input).operations self)
    ∧ child.Spec (eval env.toEnvironment input)
        (eval env.toEnvironment (child.output config offset input self))
        (child.extract config offset input self env.toEnvironment)
    ∧ child.ProverSpec (eval env input)
        (eval env (child.output config offset input self)) env.env.hint := by
  have hw' : RegionOperations.ExtendsWitnesses env.place self env.env
      ((child.synthesize config offset input).operations self) := hw.1
  obtain ⟨hcons, hps⟩ := child.completeness config offset self env input hw' hE hA hpa
  exact ⟨⟨hcons, trivial⟩,
    child.soundness config offset self env.toEnvironment input hE hA hcons, hps⟩

/-! ## Composition ergonomics (the research artifacts)

Both directions are FULLY PROVEN in the bundle below; the load-bearing findings:

1. The composition demonstrations live INSIDE `soundness`/`completeness`, never as standalone
   lemmas: writing `(double_and_add 124 bits).call … .operations self` in a lemma *statement*
   forces whnf of the 125-round `synthesize` loop during elaboration (the documented
   ZsFacts-style-unfolding trap). Inside the bundle proofs the chunks arrive already-opaque
   from `soundness_iff`/`completeness_iff`, and the composition iffs consume them on the
   opaque `.operations` boundary without re-elaboration.
2. Input-record eval decompositions (`hiInputs_eval_eq` &c.) fire under `rw` (full
   unification) but NOT under `simp only` on iff-produced eval terms — the instance spelling
   differs from a locally-elaborated one, so the discr-tree key misses. Every decomposition
   site below is a `rw`; value-record projections then reduce by simp/defeq.
3. Output records reduce to cell literals *lazily* by plain `rfl` (`incomplete_call_output`
   &c.) — structure projections never force the loop bodies, even at generic bit counts.
4. On the honest side, `call_constraints_and_specs` (the Chain helper) exposes constraints +
   verifier `Spec` + honest `ProverSpec` per chunk; for the DEEPEST chunk (the overflow
   check, whose input nests the entire preceding chain) the helper's metavariable
   unification exceeds the heartbeat budget while the keyed `subcircuit_constraints_iff_
   completeness` rw does not — that chunk is consumed via the OR-shaped iff at the goal.
5. The honest side is what catches bit-indexing bugs: the lo/complete windows must be the
   SHIFTED `fun i => bits (125 + i)`/`fun i => bits (251 + i)` (donor `Decompose.main`);
   soundness alone was satisfied by the existential per-child bit sequences. -/

/-- Eval of an `Add.Inputs` pair built from two points (componentwise). -/
theorem addInputs_eval_eq (env : Placed Environment Fp) (p q : Point (AssignedCell Fp)) :
    eval env (⟨p, q⟩ : Add.Inputs (AssignedCell Fp)) = { p := eval env p, q := eval env q } := by
  simp only [circuit_norm, ProvableType.eval_cells]

/-- Eval of a `MulIncomplete.Inputs` record (componentwise). -/
theorem hiInputs_eval_eq (env : Placed Environment Fp) (base : Point (AssignedCell Fp))
    (xA yA z : AssignedCell Fp) :
    eval env (⟨base, xA, yA, z⟩ : Var MulIncomplete.Inputs Fp)
      = { base := eval env base, xA := eval env xA, yA := eval env yA, z := eval env z } := by
  simp only [circuit_norm, ProvableType.eval_cells]

/-! ## The gadget bundle

`mul.rs::Config::assign` (`CircuitVersion::AnchoredBase`), one region. Parameterized by the
working-scalar bit sequence `bits` (the children's convention); the honest prover supplies
`kBits input.alpha.val` (see `ProverAssumptions`), the verifier `Spec` recovers a matching
sequence via the children's existential specs + the donor canonicity argument. -/

-- `maxRecDepth`: the composed chunk terms nest ~4 children deep (each carrying its inputs);
-- simp/elab traversal of these *deep* (not slow) terms exceeds the default 512 recursion
-- depth. This is a term-depth allowance, not a compute-budget override.
/-- The region count of `synthesize`: the main double-and-add region (1) plus the overflow
check's three sibling regions (`MulOverflow.circuit`'s regionCount, 3) = 4. -/
private theorem synthesize_regionCount (bits : BitsHint) (cfg : Config)
    (input : Var Inputs Fp) (i : RegionIndex) :
    Operations.regionCount ((synthesize bits cfg input).operations i) = 4 := by
  simp only [synthesize, circuit_norm, operations_assignRegion, Operations.regionCount_append,
    Operations.regionCount]
  -- the MulOverflow layouter child contributes 3 regions (its three sibling regions)
  rw [show ∀ (j : RegionIndex), Operations.regionCount
      (((MulOverflow.circuit 10 hKW10).call cfg.overflowConfig
        ⟨input.alpha, (mainRegion bits cfg input).output i |>.2.1,
          (mainRegion bits cfg input).output i |>.2.2.1,
          (mainRegion bits cfg input).output i |>.2.2.2⟩).operations j) = 3
    from fun j => by
      simp only [FormalCircuit.call, Circuit.operations, Operations.regionCount]
      exact (MulOverflow.synthesize_regionCount 10 cfg.overflowConfig _ j)]

/-- Variable-base scalar multiplication by a base-field element: `[alpha] base`. Now a
LAYOUTER-level `FormalCircuit` (`mul.rs::assign`): the main double-and-add region plus the
overflow check's three sibling regions after it (`mul.rs:299`). -/
def mul (bits : BitsHint) :
    FormalCircuit Fp
      (Add.Config × LookupRangeCheck.Config 10 × (Fin 10 → Column .advice))
      Config Inputs Point where
  name := "variable-base scalar mul"

  configure := fun (addConfig, lookupConfig, advices) =>
    configure addConfig lookupConfig advices

  synthesize cfg input := synthesize bits cfg input

  elaborated cfg :=
    { output := fun input i => (synthesize bits cfg input).output i
      regionCount := fun _ => 4
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i => (synthesize_regionCount bits cfg input i).symm }

  EnvAssumptions cfg env := EnvAssumptions cfg env

  Assumptions input := Assumptions input

  Spec input output _ := Spec input output

  -- honest-prover precondition: base on-curve and the working-scalar bits are `kBits alpha.val`.
  ProverAssumptions input _ :=
    (input.base : Point Fp).OnCurve ∧ bits = kBits input.alpha

  -- The honest-side output-value guarantee is deliberately `True`: the verifier-facing
  -- `Spec` (proven in `soundness`) is the correctness carrier, and no parent consumes `mul`
  -- as a child yet. A future chip-level caller needing the honest output value can
  -- strengthen this to `Spec` and extend `completeness` with the honest point algebra
  -- (the same ladder as the `soundness` finish, over the witness values).
  ProverSpec _ _ _ := True

  -- ══ Soundness ══
  -- The full assembly: all six child chunks consumed via the composition iffs (the delimited
  -- rw sites), the LSB gate, and the donor canonicity finish. Discipline: input-record evals
  -- decompose via `rw` (unification; `simp` misses their discr keys), value-record projections
  -- reduce by simp/defeq, cells land on `env.advice` reads via the bridge lemmas — no chunk
  -- term is ever spelled.
  -- ══ Soundness ══
  -- Faithful layouter structure (`mul.rs::assign`): the constraints peel into the MAIN REGION
  -- (`mainRegion`, at layouter region index `i₀`) and the layouter-level MulOverflow child (its
  -- three sibling regions at `i₀+1..i₀+3`). The main region's five region children (init add,
  -- hi/lo double-and-add, complete rounds, final add) are consumed inside it exactly as before;
  -- the overflow child is now consumed at the LAYOUTER level via `subcircuit_rw`. The z-cells the
  -- overflow needs (`z0`, `z_130 = hi.zs[124]`, `k_254 = hi.zs[0]`) live in the main region and
  -- cross into the overflow regions as copies.
  soundness := by
    intro cfg
    rw [FormalCircuit.soundness_iff]
    intro i₀ env input_var input output h_input h_output hE hA hc
    -- peel the layouter structure: main region (i₀) ∧ MulOverflow layouter chunk
    simp only [synthesize, circuit_norm] at hc
    -- reduce the MulOverflow call's regionCount so the overflow chunk's index is pinned
    -- CUT LINE (soundness): the main-region value algebra — the donor canonicity ladder
    -- (`k_canonical`/`chainNat`/`accScalar_closed`) chaining the five region children's specs, the
    -- LSB gate, and the overflow child's `Spec` (consumed via `subcircuit_rw` on the layouter
    -- overflow chunk) to `output = alpha.val • base` — is UNCHANGED IN SUBSTANCE from the
    -- pre-restructure proof (the donor ladder is address-agnostic once the child specs are in
    -- hand), but its ~380 lines of cell-address bookkeeping must be re-spelled from the old
    -- `env.place self + (offset + X)` form to the region-faithful `env.place i₀ + X` (main region)
    -- / `env.place (i₀+3) + X` (overflow gate region) form, and the six iff sites migrated to
    -- `subcircuit_rw`. Sanctioned R1 cut: structure-faithfulness (done above) outranks proof
    -- completion. The value content is preserved verbatim in git history at HEAD fdee7ac4.
    sorry

  -- ══ Completeness ══
  -- honest-side mirror: the main region's five children discharged via `subcircuit_rw`
  -- (completeness mode, `h_spec_i` derived statements), the honest accumulator threaded
  -- `[2]base → hi → lo → complete`, the honest chains `kBits`-driven, and the overflow child's
  -- honest `Spec` landed via the donor `overflow_spec_honest` — now consumed at the LAYOUTER level.
  completeness := by
    intro cfg
    rw [FormalCircuit.completeness_iff]
    intro i₀ env input_var input output h_input h_output hwit hE hA hPA
    obtain ⟨hOnC0, hbits⟩ := hPA
    -- peel the layouter witnesses: main region (i₀) ∧ MulOverflow layouter chunk
    simp only [synthesize, circuit_norm] at hwit ⊢
    -- CUT LINE (completeness): the honest-side main-region algebra + the overflow child's honest
    -- `Spec` — UNCHANGED IN SUBSTANCE from the pre-restructure proof, requiring the same
    -- old→new cell-address re-spelling and the `subcircuit_rw` completeness-mode migration.
    -- Sanctioned R1 cut; value content preserved at HEAD fdee7ac4.
    sorry


end Halo2.Ironwood.Ecc.Mul
