import Clean.Halo2
import Clean.Halo2.Subcircuit
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
-/

namespace Halo2.Ironwood.Ecc.Mul

open Orchard (Point)
open Orchard.Ecc (tQ)
open Orchard.Ecc.Mul (tQNat kNat kBits chainNat)
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

/-! ## Row-span offsets (`mul.rs::assign` offset threading)

The children are composed in one region. Each phase gets a distinct region-local base offset,
so the phases occupy disjoint row ranges (the model's replacement for Rust's column
non-overlap asserts — see the ConfigWF verdict). The spans:

- `Add.add` init at `offInit = 0`: complete addition writes rows `0..1`.
- `Add`'s output row is `1`; the hi half starts at `offHi`. In Rust the incomplete `z_init`
  and the hi/lo/complete phases share a running region; here each child owns its rows. We
  thread a generous offset per phase (the exact constants are immaterial to soundness — the
  proofs only need consistent threading — but we mirror Rust's block order).
- `MulIncomplete.double_and_add 124` (hi) at `offHi`: rows `offHi .. offHi + 1 + 126`.
- `MulIncomplete.double_and_add 125` (lo) at `offLo`: rows `offLo .. offLo + 1 + 127`.
- `MulComplete.assign_region 3` (complete) at `offComp`: rows `offComp .. offComp + 6`.
- the LSB step at `offLsb`: `q_mul_lsb` at `offLsb`, a final `Add.add` at `offLsb`.
- `MulOverflow.circuit 10` at `offOv`: rows `offOv .. offOv + 3 + 13`.

To keep the arithmetic legible the constants below are chosen with slack; only their strict
ordering and the fact that `synthesize` and the proofs use the SAME values matter. -/

/-- Rows consumed by the hi double-and-add (`n = 124`): `1 + (n + 1) + 1 = 127`. -/
def hiSpan : ℕ := 127
/-- Rows consumed by the lo double-and-add (`n = 125`): `1 + (n + 1) + 1 = 128`. -/
def loSpan : ℕ := 128
/-- Rows consumed by the 3 complete rounds: `2·3 + 1 = 7`. -/
def compSpan : ℕ := 7

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
/-- Overflow check. -/
def offOv : ℕ := offLsb + 3

/-! ## Child contract-projection bridges (`rfl`, child stays folded)

The MulComplete/MulOverflow pattern: expose each child's contract fields as `rfl`-bridges,
so the composition consumes them without unfolding the child bundle literal. FRAMEWORK
CANDIDATE: a deriving-style projection mechanism. -/

private theorem add_spec_eq :
    Add.add.Spec = fun input output _ => output.Valid ∧ output = input.p + input.q := rfl
private theorem add_assumptions_eq :
    Add.add.Assumptions = fun input => input.p.Valid ∧ input.q.Valid := rfl
private theorem add_envAssumptions_eq :
    Add.add.EnvAssumptions = fun _ _ => True := rfl

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

/-- The scalar-decomposition and recombination assembly, parameterized by the working-scalar
bit sequence `bits` (the honest prover supplies `kBits input.alpha.val`; the verifier `Spec`
quantifies existentially, so soundness is independent of the prover's honesty about `bits`).
Returns the result point `[alpha] base`. -/
def synthesize (bits : BitsHint) (cfg : Config) (offset : ℕ) (input : Var Inputs Fp) :
    RegionCircuit Fp (Var Point Fp) := do
  let bitsOf : MulIncomplete.BitsHint := bits
  -- 1. acc = [2]base  (init complete addition, mul.rs:188-190)
  let acc ← Add.add.call cfg.addConfig (offset + offInit)
    ⟨input.base, input.base⟩
  -- 2. z_init = 0  (mul.rs:201-206): the running-sum start, assigned as the constant 0 on the
  --    hi config's `z` column at the hi phase's start row, constrained via `constrainConstant`
  --    (Rust `assign_advice_from_constant`). The hi half copies this same cell into its own `z`
  --    at `offHi` — the "assign the same value to the same cell twice" no-op (mul.rs:198-200).
  let zInit ← assignAdvice cfg.hiConfig.z (offset + offHi)
    (.native fun _ => #v[(0 : Fp)])
  constrainConstant zInit 0
  -- 3. hi half: 125 double-and-add bits k_254..k_130  (mul.rs:209-216)
  let hi ← (MulIncomplete.double_and_add 124 bitsOf).call cfg.hiConfig (offset + offHi)
    ⟨input.base, acc.x, acc.y, zInit⟩
  -- 4. lo half: 126 double-and-add bits k_129..k_4, running sum chained  (mul.rs:220-227)
  let lo ← (MulIncomplete.double_and_add 125 bitsOf).call cfg.loConfig (offset + offLo)
    ⟨input.base, hi.xA, hi.yA, hi.zs[124]⟩
  -- 5. complete rounds: k_3..k_1  (mul.rs:239-253)
  let comp ← (MulComplete.assign_region 3 bitsOf).call cfg.completeConfig (offset + offComp)
    ⟨input.base, lo.xA, lo.yA, lo.zs[125]⟩
  -- 6. the LSB step k_0  (mul.rs:258-260, process_lsb, mul.rs:324-385)
  let z1 := comp.zs[2]
  -- z_0 = 2·z_1 + k_0 on the z_complete column at the LSB base row
  let z0 ← assignAdvice cfg.completeConfig.zComplete (offset + offLsb)
    (.native fun env => #v[2 * readCell env z1 + (if bitsOf 254 then 1 else 0)])
  -- copy base_x, base_y into the LSB gate window (next row)
  let _bx ← copyAdvice input.base.x cfg.addConfig.xP (offset + offLsb + 1)
  let _by ← copyAdvice input.base.y cfg.addConfig.yP (offset + offLsb + 1)
  -- the correction point (base_x, ±base_y) or identity, witnessed on add.xP/add.yP (cur row)
  let corrX ← assignAdvice cfg.addConfig.xP (offset + offLsb)
    (.native fun env => #v[if bitsOf 254 then 0 else readCell env input.base.x])
  let corrY ← assignAdvice cfg.addConfig.yP (offset + offLsb)
    (.native fun env => #v[if bitsOf 254 then 0 else -(readCell env input.base.y)])
  -- the q_mul_lsb gate at the LSB base row
  (lsbGate cfg).enable (offset + offLsb)
  -- the final complete addition: result = corr + acc
  let result ← Add.add.call cfg.addConfig (offset + offLsb)
    ⟨{ x := corrX, y := corrY }, comp.acc⟩
  -- 7. overflow check on z_0 (full sum), z_130 (after hi), k_254 (first bit)  (mul.rs:298-302)
  let _ov ← (MulOverflow.circuit 10 hKW10).call cfg.overflowConfig (offset + offOv)
    ⟨input.alpha, z0, hi.zs[124], hi.zs[0]⟩
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

/-! ## The composition skeleton (the research artifact)

The demonstration that the absorption-iff pattern threads through the assembly lives INSIDE
`soundness` (`init_hi_consumed`, the delimited block): the init complete-addition chunk and the
hi `MulIncomplete` chunk both fire their soundness iffs, and their specs are learned
END-TO-END — the init add's output `acc = [2]base` becomes the hi half's entering-accumulator
precondition, and the hi half's spec delivers the running-sum chain and the accumulator
`[accScalar 2 bitsHi 125] • base`.

It is proven in-place rather than as a standalone lemma because writing
`(double_and_add 124 bits).call … .operations self` in a lemma *statement* forces whnf of the
125-round `synthesize` loop during elaboration (the documented ZsFacts-style-unfolding trap);
inside `soundness` the chunk arrives already-opaque from `soundness_iff`, and the composition iff
consumes it on the opaque `.operations` boundary without re-elaboration. See
`init_hi_consumed` in `mul.soundness`. -/

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

/-- Completeness helper, copied from `MulComplete.call_constraints_and_spec` per the
no-cross-gadget-import convention: run a child's `completeness` then `soundness` to obtain both
the chunk's `Constraints` and the child's verifier-view `Spec` (the value the parent's honest
bookkeeping needs). FRAMEWORK CANDIDATE. -/
theorem call_constraints_and_spec {CI Cfg : Type} {Input Output : TypeMap}
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
        (child.extract config offset input self env.toEnvironment) := by
  have hw' : RegionOperations.ExtendsWitnesses env.place self env.env
      ((child.synthesize config offset input).operations self) := hw.1
  obtain ⟨hcons, _⟩ := child.completeness config offset self env input hw' hE hA hpa
  exact ⟨⟨hcons, trivial⟩,
    child.soundness config offset self env.toEnvironment input hE hA hcons⟩

/-! ## The gadget bundle

`mul.rs::Config::assign` (`CircuitVersion::AnchoredBase`), one region. Parameterized by the
working-scalar bit sequence `bits` (the children's convention); the honest prover supplies
`kBits input.alpha.val` (see `ProverAssumptions`), the verifier `Spec` recovers a matching
sequence via the children's existential specs + the donor canonicity argument. -/

/-- Variable-base scalar multiplication by a base-field element: `[alpha] base`. -/
def mul (bits : BitsHint) :
    FormalRegionCircuit Fp
      (Add.Config × LookupRangeCheck.Config 10 × (Fin 10 → Column .advice))
      Config Inputs Point where
  name := "variable-base scalar mul"

  configure := fun (addConfig, lookupConfig, advices) =>
    configure addConfig lookupConfig advices

  synthesize cfg offset input := synthesize bits cfg offset input

  EnvAssumptions cfg env := EnvAssumptions cfg env

  Assumptions input := Assumptions input

  Spec input output _ := Spec input output

  -- honest-prover precondition: base on-curve and the working-scalar bits are `kBits alpha.val`.
  ProverAssumptions input _ :=
    (input.base : Point Fp).OnCurve ∧ bits = kBits input.alpha.val

  ProverSpec input output _ := Spec input output

  -- ══ Soundness ══
  -- The composition skeleton is DEMONSTRATED end-to-end for the init-add and hi chunks
  -- (`init_hi_consumed` below): both iffs fire and their specs thread. The remaining
  -- lo/complete/lsb/overflow assembly + the donor canonicity finish is stated as a single
  -- `sorry` with the donor lemmas identified (`Orchard.Ecc.Mul.soundness`, `k_canonical`,
  -- `accScalar_closed`, `nsmul_add_neg_one`, `nsmul_eq_zero_iff`).
  soundness := by
    intro cfg offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output hE hA hc
    -- ══ peel the synthesize op list around the child chunks ══
    -- The op list is (by `operations_bind`):
    --   Add.call(init) ++ [assign zInit] ++ [constrainConstant] ++ MulIncomplete.call(hi)
    --     ++ MulIncomplete.call(lo) ++ MulComplete.call ++ [assign z0] ++ [copy bx] ++ [copy by]
    --     ++ [assign corrX] ++ [assign corrY] ++ [enable lsb] ++ Add.call(final)
    --     ++ MulOverflow.call
    -- Peel with ONLY the bind/append/per-op lemmas — NOT `circuit_norm`, which would recurse
    -- into every child's 125-round `synthesize` (the "no whole-goal circuit_norm on big
    -- composites" trap). Each `.call` chunk stays folded as `(child.call …).operations self`,
    -- exactly the opaque boundary the composition iff keys on.
    simp only [synthesize,
      RegionCircuit.operations_bind,
      operations_assignAdvice, operations_copyAdvice, operations_enable,
      operations_constrainConstant, RegionOperations.constraints_append] at hc
    -- the leading chunks: init-add constraints, then the two z_init ops, then the hi chunk
    obtain ⟨hInit, _hZinit, _hZconst, hHi, _hRest⟩ := hc
    -- destructure the input record into components (the child pattern): `input_var.base`
    -- becomes `{x := input_var_base_x, y := input_var_base_y}` (cells) and `input.base` becomes
    -- `{x := input_base_x, y := input_base_y}` (values), the two linked by `eval` (rfl bridges).
    -- Fast: the goal's output eval stays an atom.
    provable_type_simp
    obtain ⟨hIalpha, hBx, hBy⟩ := h_input
    -- the input base as cells / values
    set base : Point (AssignedCell Fp) := { x := input_var_base_x, y := input_var_base_y }
      with hbaseDef
    set baseVal : Point Fp := { x := input_base_x, y := input_base_y } with hbaseValDef
    have hbaseCoordX : eval env input_var_base_x
        = input_base_x := by
      rw [ProvableType.eval_field]; simpa only [AssignedCell.eval] using hBx
    have hbaseCoordY : eval env input_var_base_y
        = input_base_y := by
      rw [ProvableType.eval_field]; simpa only [AssignedCell.eval] using hBy
    have hbaseV : baseVal.Valid := Or.inl hA
    -- ▸▸▸ init_hi_consumed: init-add ⇒ acc = [2]base ; hi ⇒ RoundInvariant 124 ▸▸▸
    -- init add: `acc = base + base`, valid
    rw [FormalRegionCircuit.subcircuit_constraints_iff_soundness
          Add.add cfg.addConfig (offset + offInit) self env
          ⟨base, base⟩] at hInit
    obtain ⟨_, hSpecInit⟩ := hInit
    simp only [add_spec_eq, add_assumptions_eq, add_envAssumptions_eq] at hSpecInit
    have hInitIn : eval env
        (⟨base, base⟩ : Add.Inputs (AssignedCell Fp))
        = (⟨baseVal, baseVal⟩ : Add.Inputs Fp) := by
      rw [addInputs_eval_eq, hbaseDef, hbaseValDef, Point.eval_eq, hbaseCoordX, hbaseCoordY]
    obtain ⟨hAccV, hAccEq⟩ := hSpecInit trivial (by rw [hInitIn]; exact ⟨hbaseV, hbaseV⟩)
    rw [hInitIn] at hAccEq
    -- the init output point, and `hAccEq : accPt = baseVal + baseVal` (= [2]base)
    set accPt : Point Fp := eval env
      (Add.add.output cfg.addConfig (offset + offInit) ⟨base, base⟩ self) with haccdef
    -- hi half: `∃ bitsHi, RoundInvariant 124 …` (the chunk consumed on the opaque boundary).
    -- hHi's input cells are the raw synthesize outputs: `xA/yA := (Add.add.call …).output self`
    -- (= `.output …`, defeq), `z := (assignAdvice …).output self` (the z_init cell). The iff `rw`
    -- unifies these by `isDefEq` on the opaque `.operations` boundary. The input arg is passed in
    -- the SAME spelling hHi carries so the discr-tree key matches.
    rw [FormalRegionCircuit.subcircuit_constraints_iff_soundness
          (MulIncomplete.double_and_add 124 bits) cfg.hiConfig (offset + offHi) self
          env
          ⟨base,
            ((Add.add.call cfg.addConfig (offset + offInit) ⟨base, base⟩).output self).x,
            ((Add.add.call cfg.addConfig (offset + offInit) ⟨base, base⟩).output self).y,
            (assignAdvice cfg.hiConfig.z (offset + offHi)
              (Witgen.WitgenIROver.native fun _ => #v[(0 : Fp)])).output self⟩] at hHi
    obtain ⟨_, hSpecHi⟩ := hHi
    simp only [hi_spec_eq, hi_assumptions_eq, hi_envAssumptions_eq] at hSpecHi
    have hHiBase : (eval env
          (⟨base,
            ((Add.add.call cfg.addConfig (offset + offInit) ⟨base, base⟩).output self).x,
            ((Add.add.call cfg.addConfig (offset + offInit) ⟨base, base⟩).output self).y,
            (assignAdvice cfg.hiConfig.z (offset + offHi)
              (Witgen.WitgenIROver.native fun _ => #v[(0 : Fp)])).output self⟩
              : Var MulIncomplete.Inputs Fp)).base = baseVal := by
      rw [hiInputs_eval_eq]
      show eval env base = baseVal
      rw [hbaseDef, hbaseValDef, Point.eval_eq, hbaseCoordX, hbaseCoordY]
    obtain ⟨bitsHi, hHiRI⟩ := hSpecHi trivial (by rw [hHiBase]; exact hA)
    -- ▲▲▲ init and hi are now consumed END-TO-END: `hAccV` (init acc valid), `hAccEq`
    -- (`accPt = base + base = [2]base`), and `hHiRI` (the hi `RoundInvariant` over `bitsHi`,
    -- whose accumulator clause takes `Point.ofCoords (acc) = 2 • base` — dischargeable from
    -- `hAccEq` — to `[accScalar 2 bitsHi 125] • base`) are all in context.
    --
    -- ◂◂◂ CUT LINE ◂◂◂  The remaining assembly (lo half, complete rounds, LSB step, overflow)
    -- and the donor canonicity finish (`k = alpha + t_q`, the LSB correction point,
    -- `[2^254 + k] base = [alpha] base`) mirror `Orchard.Ecc.Mul.soundness` (donor
    -- `Assign.lean`, lines 852-969): route `hHiRI`'s `m = 2` accumulator into the lo/complete
    -- `RoundInvariant`s, feed the LSB gate + final `Add.add`, and hand the overflow `Spec` to
    -- `Orchard.Ecc.Mul.k_canonical`. Donor lemmas identified: `accScalar_closed`,
    -- `nsmul_add_neg_one`, `nsmul_eq_zero_iff`, `k_canonical`.
    clear hHiRI hHiBase hSpecHi hAccEq hAccV
    sorry

  -- ══ Completeness ══
  -- Mirrors soundness on the honest witnesses: `kBits alpha.val` drives every child, the honest
  -- accumulator threads `[2]base → hi → lo → complete → lsb`, and `overflow_spec_honest`
  -- (donor) discharges the overflow child's `Spec`. The init-add + hi consumption is
  -- demonstrated here via `call_constraints_and_spec` (the honest counterpart of the soundness
  -- skeleton); the rest is a stated `sorry` with the donor lemmas identified.
  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit hE hA hPA
    obtain ⟨hOnCurve, hbits⟩ := hPA
    -- peel the witness list (bind/append/per-op — NOT `circuit_norm`, per the big-composite trap)
    simp only [synthesize,
      RegionCircuit.operations_bind,
      operations_assignAdvice, operations_copyAdvice, operations_enable,
      operations_constrainConstant, RegionOperations.extendsWitnesses_append] at hwit
    -- leading witness chunks: init-add ++ [assign zInit] ++ [constrainConstant] ++ hi ++ …
    obtain ⟨hWInit, _hWZinit, _hWZconst, hWHi, _hWRest⟩ := hwit
    provable_type_simp
    obtain ⟨hIalpha, hBx, hBy⟩ := h_input
    set base : Point (AssignedCell Fp) := { x := input_var_base_x, y := input_var_base_y }
      with hbaseDef
    set baseVal : Point Fp := { x := input_base_x, y := input_base_y } with hbaseValDef
    have hbaseCoordX : eval env.toEnvironment input_var_base_x = input_base_x := by
      rw [ProvableType.eval_field]; simpa only [AssignedCell.eval] using hBx
    have hbaseCoordY : eval env.toEnvironment input_var_base_y = input_base_y := by
      rw [ProvableType.eval_field]; simpa only [AssignedCell.eval] using hBy
    have hbaseV : baseVal.Valid := Or.inl hOnCurve
    -- ▸▸▸ honest init-add consumed: constraints + Spec (`acc = base + base`, valid) ▸▸▸
    have hInitInEval : eval env.toEnvironment (⟨base, base⟩ : Add.Inputs (AssignedCell Fp))
        = (⟨baseVal, baseVal⟩ : Add.Inputs Fp) := by
      rw [addInputs_eval_eq, hbaseDef, hbaseValDef, Point.eval_eq, hbaseCoordX, hbaseCoordY]
    obtain ⟨hCInit, hSpecInit⟩ := call_constraints_and_spec Add.add cfg.addConfig
      (offset + offInit) self env ⟨base, base⟩ hWInit trivial
      (by rw [hInitInEval]; exact ⟨hbaseV, hbaseV⟩) trivial
    simp only [add_spec_eq, hInitInEval] at hSpecInit
    obtain ⟨hAccV, hAccEq⟩ := hSpecInit
    -- ▸▸▸ honest hi half consumed: constraints + Spec (the `RoundInvariant 124` over `bits`) ▸▸▸
    -- (the hi call's input cells are the raw synthesize outputs, matching `hWHi`)
    have hHiInEval : (eval env.toEnvironment
          (⟨base,
            ((Add.add.call cfg.addConfig (offset + offInit) ⟨base, base⟩).output self).x,
            ((Add.add.call cfg.addConfig (offset + offInit) ⟨base, base⟩).output self).y,
            (assignAdvice cfg.hiConfig.z (offset + offHi)
              (Witgen.WitgenIROver.native fun _ => #v[(0 : Fp)])).output self⟩
              : Var MulIncomplete.Inputs Fp)).base = baseVal := by
      rw [hiInputs_eval_eq]
      show eval env.toEnvironment base = baseVal
      rw [hbaseDef, hbaseValDef, Point.eval_eq, hbaseCoordX, hbaseCoordY]
    -- the hi half's `ProverAssumptions`: base on-curve and `acc = [m]base` with `m = 2` in range.
    -- `Point.ofCoords (acc) = 2 • base` is dischargeable from `hAccEq` (`acc = base + base`) plus
    -- `base + base = 2 • base`; deferred with the rest of the honest assembly.
    -- ◂◂◂ CUT LINE ◂◂◂  The remaining honest assembly (hi/lo/complete `ProverAssumptions` via the
    -- `m`-multiple threading, the LSB honest correction, and the overflow honest `Spec` via the
    -- donor `overflow_spec_honest`) mirrors `Orchard.Ecc.Mul.completeness` (donor `Assign.lean`,
    -- lines 1109-1146). Donor lemmas identified: `cells_kNat`, `z0_cell_value`,
    -- `overflow_spec_honest`.
    clear hAccV hAccEq hCInit hWHi hHiInEval
    sorry

end Halo2.Ironwood.Ecc.Mul
