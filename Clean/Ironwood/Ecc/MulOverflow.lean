import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Halo2.Tactics.SubcircuitRw
import Clean.Orchard.Specs.Pallas
import Clean.Orchard.Ecc.Defs
import Clean.Orchard.Ecc.Mul.Overflow
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Utilities.LookupRangeCheck

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul/overflow.rs` (read in full),
invoked from `mul.rs:298-302` as `overflow_config.overflow_check(alpha, &zs)` where `zs =
[z_0, z_1, …, z_254, z_255]` are the running sums of the whole variable-base scalar mul.

This is the OVERFLOW CHECK of variable-base scalar mul: given the scalar `alpha` and the
running sums, it enforces the two facts that make the mul sound against overflow of the
254-bit scalar decomposition (`overflow.rs:50-98`):
- `recovery`: `z_0 = alpha + t_q` (the full running sum recovers the scalar plus the field
  modulus offset `t_q`);
- `canonicity`: witnessing `s = alpha + k_254·2^130` and decomposing its low 130 bits, the
  high tail `s_minus_lo_130` vanishes in the appropriate cases (`k_254 = 0`, or `z_130` is
  the top bit `2^124`), ruling out a non-canonical `alpha`.

## What's distinctive: first LOOKUP-USING child composition

The parent calls `LookupRangeCheck.rangeCheck K numWords strict=false` (fully proven) to
decompose the low 130 bits of `s` with thirteen `K = 10`-bit lookups (`overflow.rs:190-208`,
`s_minus_lo_130` → `copy_check(s, num_words = 13, strict = false)`). This is the first
subcircuit-composition consumer whose child *uses a lookup*, so the child's `EnvAssumptions`
is a genuinely non-trivial derived fact:

    rangeCheck.EnvAssumptions cfg env = TableLoaded K cfg env.env ∧ (selector distinctness)

over the CHILD's `LookupRangeCheck.Config K` — a *derived sub-config* (unlike Chain, where
parent and child share `Config` and the discharge is `rfl`/`id`). The parent stores the
child's `LookupRangeCheck.Config K` inside its own `Config` (as `lookupConfig`), and its
own `EnvAssumptions` states the table fact over that *projected* sub-config. The parent then
discharges the child's env-assumption by PROJECTION — reading its own `EnvAssumptions` and
handing the projected `TableLoaded`/distinctness onto the child call. See the verdict note
at `circuit.child_envAssumptions_of_parent`.

## Config composition (mirrors Rust `overflow::Config`)

Rust `overflow::Config<Lookup>` (`overflow.rs:18-26`) holds `q_mul_overflow: Selector`,
`lookup_config: Lookup`, and `advices: [Column<Advice>; 3]`, and `configure` takes the
`lookup_config` as a parameter (built once in `mul.rs:78-79`). We mirror this exactly: the
parent `Config` stores `qOverflow`, the child's `lookupConfig : LookupRangeCheck.Config K`,
and the three advice columns `adv0/adv1/adv2`.

## Boundary

The overflow gate (`create_gate`, `overflow.rs:49-99`) is this file's responsibility, ported
verbatim as a standalone def at its verbatim rotations. The witnessing of `s` and `η`, the
copies of `z_0/z_130/k_254/alpha/s_minus_lo_130`, and the rangeCheck call are the
`overflow_check`/`s_minus_lo_130` bodies (`overflow.rs:101-208`). The upstream computation of
the running sums `zs` belongs to the mul.rs assembly (out of scope; the running-sum cells
`z_0`, `z_130`, `k_254 = z_254` arrive as verifier-visible input cells).

## Donor

`Clean/Orchard/Ecc/Mul/Overflow.lean` (`Orchard.Ecc.Mul.Overflow`) — the phase-one donor.
Its `OverflowCheck.Spec` is lifted wholesale as this file's `Spec`: the recovery equation, the
`k_254 = 0 ∨ z_130 = 2^124` disjunction, and the existential low/high split of `s` with the
two canonicity disjunctions. The value algebra (the `s = alpha + k_254·2^130` derivation, the
`recovery`/`lo_zero`/`canonicity` gate polynomials) is lifted from the donor's `Overflow.Spec`
and `OverflowCheck.soundness`.

## Proof status

Fully proven, no sorries (`#print axioms circuit` = `propext, Classical.choice, Quot.sound`).
Soundness peels the copies + the folded rangeCheck child chunk (consumed via the composition iff
— `rw`-instantiated at the delimited site, the MulComplete route, since the primed simp form does
not fire on the bare-place/env spelling), discharges the child's derived-sub-config
`EnvAssumptions` BY PROJECTION from the parent's, reduces the overflow gate to its five value-level
polynomials, and assembles the donor `Spec`. Completeness mirrors it on the honest witnesses via
`call_constraints_and_spec` (the MulComplete FRAMEWORK CANDIDATE, copied per the
no-cross-gadget-import convention).

One genuine composition finding surfaced (see the `hzLast_zero` note in `completeness`): the
canonicity gate needs the child's honest NATURAL-NUMBER decomposition `zLast = ↑(s.val / 2^130)`,
which `rangeCheck`'s verifier `Spec` (a field equation) does not expose. Resolved by a minimal
additive child-side lemma `LookupRangeCheck.rangeCheck_call_zLast_value` (reads it off the loop
witnesses `rangeCheck_loop_zvalues` that the bundle Spec does not surface — no bundle change).
FRAMEWORK CANDIDATE: a lookup child that decomposes a value should expose that nat decomposition
(a `ProverSpec` carrying it) so composition consumers need not peel the child's internals.
-/

namespace Halo2.Ironwood.Ecc.MulOverflow

open Orchard.Ecc (tQ)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)

/-- The number of `K`-bit words decomposing the low 130 bits of `s` (`overflow.rs:196`:
`num_words = 130 / K`). With `K = 10`, `numWords = 13`. Kept as a def so the layout rows and
the `2^{K·numWords} = 2^130` arithmetic read symbolically. -/
def numWords (K : ℕ) : ℕ := 130 / K

/-! ## Config

Rust `overflow::Config<Lookup>` (`overflow.rs:18-26`): the `q_mul_overflow` selector, the
delegated lookup config, and three advice columns. -/

/-- The parent config. Stores the child's `LookupRangeCheck.Config K` (the *derived sub-config*
whose table the parent's `EnvAssumptions` references), the overflow selector, and the three
advice columns `advices[0..3]`. -/
structure Config (K : ℕ) where
  qOverflow : Selector
  lookupConfig : LookupRangeCheck.Config K
  adv0 : Column .advice
  adv1 : Column .advice
  adv2 : Column .advice

/-! ## The `q_mul_overflow` gate (`overflow.rs:49-99`)

Layout relative to the gate row `g` (`q_mul_overflow` enabled at `Rotation::cur`):

    | advices[0]        | advices[1]        | advices[2] |
    -----------------------------------------------------------
    | z_0   (g-1, prev) | k_254 (g-1, prev) |            |
    | z_130 (g,   cur)  | alpha (g,   cur)  | s (g, cur) |
    | eta   (g+1, next) | s_minus_lo_130 (g+1, next)     |

The five constraints (`overflow.rs:71-96`), verbatim:
- `s_check`      : `s − (alpha + k_254·2^130)`
- `recovery`     : `z_0 − alpha − t_q`
- `lo_zero`      : `k_254·(z_130 − 2^124)`
- `s_minus_lo_130_check` : `k_254·s_minus_lo_130`
- `canonicity`   : `(1 − k_254)·(1 − z_130·eta)·s_minus_lo_130`
-/

/-- The overflow gate, a pure function of the config. Enabled at the middle row `g`;
reads `advices[0]/advices[1]` at `prev/cur/next` and `advices[2]` at `cur`. -/
def overflowGate (K : ℕ) (cfg : Config K) : Gate Fp where
  name := "overflow checks"
  selector := cfg.qOverflow
  constraints :=
    let z0 : Expression Fp Query := queryAdvice cfg.adv0 (-1)   -- z_0   (prev)
    let z130 : Expression Fp Query := queryAdvice cfg.adv0 0     -- z_130 (cur)
    let eta : Expression Fp Query := queryAdvice cfg.adv0 1      -- eta   (next)
    let k254 : Expression Fp Query := queryAdvice cfg.adv1 (-1)  -- k_254 (prev)
    let alpha : Expression Fp Query := queryAdvice cfg.adv1 0    -- alpha (cur)
    let sMinusLo130 : Expression Fp Query := queryAdvice cfg.adv1 1  -- s_minus_lo_130 (next)
    let s : Expression Fp Query := queryAdvice cfg.adv2 0        -- s (cur)
    let twoPow124 : Expression Fp Query := (2 ^ 124 : Fp)
    let twoPow130 : Expression Fp Query := (2 ^ 130 : Fp)
    let sCheck := s - (alpha + k254 * twoPow130)
    let recovery := z0 - alpha - (tQ : Fp)
    let loZero := k254 * (z130 - twoPow124)
    let sMinusLo130Check := k254 * sMinusLo130
    let canonicity := ((1 : Fp) - k254) * ((1 : Fp) - z130 * eta) * sMinusLo130
    Constraints.withSelector cfg.qOverflow
      [ ("s_check", sCheck), ("recovery", recovery), ("lo_zero", loZero),
        ("s_minus_lo_130_check", sMinusLo130Check), ("canonicity", canonicity) ]

/-- Rust `Config::configure` (`overflow.rs:29-47`): enable equality on the three advice
columns, allocate the `q_mul_overflow` selector, register the overflow gate. The
`lookup_config` is handed down by the chip assembly (`mul.rs`), already configured by
`LookupRangeCheck.configure`. -/
def configure (K : ℕ) (lookupConfig : LookupRangeCheck.Config K)
    (adv0 adv1 adv2 : Column .advice) : Configure Fp (Config K) := do
  enableEquality adv0.toAny
  enableEquality adv1.toAny
  enableEquality adv2.toAny
  let qOverflow ← selector
  let cfg : Config K := { qOverflow, lookupConfig, adv0, adv1, adv2 }
  createGate (overflowGate K cfg)
  return cfg

/-! ## Inputs / Output

Mirrors the donor `Orchard.Ecc.Mul.Overflow.OverflowCheck.Input`: the original scalar cell
`alpha` and the running-sum cells the check inspects — `z_0` (full sum), `z_130` (after the
hi half), and `k_254 = z_254` (the top bit). All are already-assigned, verifier-visible
input cells (produced by the mul.rs assembly). No output value is exposed (the gadget only
enforces constraints — like the donor's `FormalAssertion`), so `Output` is `unit`. -/

/-- Verifier-visible inputs: the scalar `alpha` and the running-sum cells `z_0`, `z_130`,
`k_254 = z_254`, as already-assigned cells. -/
structure Inputs (F : Type) where
  alpha : F
  z0 : F
  z130 : F
  k254 : F
deriving ProvableStruct

/-! ## Witness programs

`s` and `η` are the two witnessed cells (`overflow.rs:111-129, 150-159`), spelled over the
Halo2-Clean witgen IR (`FExpr Fp`). -/

/-- The witness value of `s = alpha + k_254·2^130` (`overflow.rs:113-116`: `alpha + k_254 ·
(2^65)² = alpha + k_254·2^130`). -/
def sWit (input : Inputs (AssignedCell Fp)) : WitgenIR Fp 1 :=
  .ofFExpr ((.expr input.alpha) + (.expr input.k254) * (.const (2 ^ 130 : Fp)))

/-- The witness value of `η = inv0(z_130)` (`overflow.rs:150-158`: `Assigned::from(z_130).
invert()`, i.e. the `0⁻¹ = 0` field inverse). -/
def etaWit (input : Inputs (AssignedCell Fp)) : WitgenIR Fp 1 :=
  .ofFExpr (.inv (.expr input.z130))


/-! ## Faithful region structure (`overflow_check`, `overflow.rs:101-208`)

Rust `overflow_check` runs at the LAYOUTER level in THREE sibling regions
(`overflow.rs:118-185`), plus the copyCheck child called via `s_minus_lo_130`
(`overflow.rs:200-205`, a layouter-level `lookup_config.copy_check`). We mirror this exactly:

1. **witness-s region** (`overflow.rs:118-129`, "s = alpha + k_254 ⋅ 2^130"): witness `s` at
   `advices[0]` row 0 of its own region.
2. **the copyCheck child** (`overflow.rs:200-205`): `lookup_config.copy_check(s, num_words, false)`
   — a layouter-level range check that copies `s` into the running-sum column and decomposes its
   low 130 bits; its `zLast` output is `s_minus_lo_130`.
3. **the gate region** (`overflow.rs:136-185`, "overflow check"): enables `q_mul_overflow` and
   COPIES the six participating cells across regions — `z_0`, `z_130`, `k_254`, `alpha` (from the
   parent mul's running-sum region), `s` (from region 1), `s_minus_lo_130` (from the copyCheck
   child). `η = inv0(z_130)` is witnessed here (`overflow.rs:150-158`).

The cross-region copies are `copyAdvice` of cells whose `regionIndex` is a *different* region —
the model supports this directly (`Cell` carries its region index; `copyAdvice`'s
`constrainEqual` reads the source at its own region's placement). -/

/-- The gate region body (`overflow.rs:136-185`), a region-level circuit at row offset 0 of its
own region. Enables the overflow gate at row 1 (so the gate's prev/cur/next are rows 0/1/2) and
copies in the six cells + witnesses `η`. The `s` cell (region 1) and `sMinusLo130` cell (the
copyCheck child) arrive as arguments; the four running-sum cells come from `input`. -/
def gateRegion (K : ℕ) (cfg : Config K) (input : Inputs (AssignedCell Fp))
    (sCell sMinusLo130 : AssignedCell Fp) : RegionCircuit Fp Unit := do
  -- z_0 (adv0 @ 0, gate prev), z_130 (adv0 @ 1, gate cur)   (overflow.rs:145,148)
  let _z0 ← copyAdvice input.z0 cfg.adv0 0
  let _z130 ← copyAdvice input.z130 cfg.adv0 1
  -- η = inv0(z_130) at adv0 @ 2 (gate next)                 (overflow.rs:150-158)
  let _eta ← assignAdvice cfg.adv0 2 (etaWit input)
  -- k_254 (adv1 @ 0, gate prev), alpha (adv1 @ 1, gate cur) (overflow.rs:162,165-170)
  let _k254 ← copyAdvice input.k254 cfg.adv1 0
  let _alpha ← copyAdvice input.alpha cfg.adv1 1
  -- s_minus_lo_130 (adv1 @ 2, gate next)                    (overflow.rs:173-178)
  let _sMinusLo130 ← copyAdvice sMinusLo130 cfg.adv1 2
  -- s (adv2 @ 1, gate cur)                                  (overflow.rs:181)
  let _s ← copyAdvice sCell cfg.adv2 1
  -- enable the overflow gate at the middle row (offset+1 = 1)   (overflow.rs:142)
  (overflowGate K cfg).enable 1
  return ()

/-- The layouter-level `overflow_check` body (`overflow.rs:101-208`): the three faithful sibling
regions plus the copyCheck child. -/
def synthesize (K : ℕ) (cfg : Config K) (input : Inputs (AssignedCell Fp)) :
    Circuit Fp Unit := do
  -- region 1: witness s = alpha + k_254·2^130 at advices[0] row 0   (overflow.rs:118-129)
  let sCell ← assignRegion "s = alpha + k_254 ⋅ 2^130"
    (assignAdvice cfg.adv0 0 (sWit input))
  -- child copyCheck: decompose the low 130 bits of s   (overflow.rs:200-205)
  let dec ← (LookupRangeCheck.copyCheck K (numWords K) false).call cfg.lookupConfig
    { element := sCell }
  -- region 3: the overflow-check gate region with cross-region copies   (overflow.rs:136-185)
  let _ ← assignRegion "overflow check" (gateRegion K cfg input sCell dec.zLast)
  return ()

/-! ## Contract

`EnvAssumptions` states the table fact + selector distinctness over the *projected* child
sub-config `cfg.lookupConfig` — exactly the copyCheck child's `EnvAssumptions` on that config.
`Spec` is the donor `OverflowCheck.Spec`, lifted wholesale. -/

/-- The parent `EnvAssumptions`: the child's `TableLoaded` over the projected `lookupConfig`,
plus the selector distinctness the child needs. Definitionally the copyCheck child's
`EnvAssumptions` applied to `cfg.lookupConfig`. -/
def EnvAssumptions (K : ℕ) (cfg : Config K) (env : Placed Environment Fp) : Prop :=
  LookupRangeCheck.TableLoaded K cfg.lookupConfig env.env ∧
    cfg.lookupConfig.qLookup.index ≠ cfg.lookupConfig.qRunning.index

/-- The overflow-check contract (donor `OverflowCheck.Spec`), verifier view. `z_0` recovers
`alpha + t_q`; `z_130` is `2^124` unless `k_254 = 0`; and some split `s = s_lo + 2^130·s_hi`
with `s_lo < 2^130` satisfies the two canonicity disjunctions. -/
def Spec (input : Inputs Fp) : Prop :=
  input.z0 = input.alpha + (tQ : Fp) ∧
  (input.k254 = 0 ∨ input.z130 = (2 ^ 124 : Fp)) ∧
  ∃ (sHi : Fp) (sLo : ℕ), sLo < 2 ^ 130 ∧
    input.alpha + input.k254 * (2 ^ 130 : Fp) = (sLo : Fp) + (2 ^ 130 : Fp) * sHi ∧
    (input.k254 = 0 ∨ sHi = 0) ∧
    (input.k254 = 1 ∨ input.z130 ≠ 0 ∨ sHi = 0)

/-! ## Child contract-projection bridges (`rfl`, child stays folded)

Bridges exposing exactly the copyCheck child's contract fields without unfolding the bundle
literal. Since `copyCheck = rangeCheck.toFormal`, its contract fields are `rangeCheck`'s. -/

private theorem copyCheck_spec_eq (K : ℕ) :
    (LookupRangeCheck.copyCheck K (numWords K) false).Spec
      = fun input output _ =>
          output.z0 = input.element ∧
          (∃ lo : ℕ, lo < 2 ^ (K * numWords K) ∧
            input.element = (lo : Fp) + ((2 ^ (K * numWords K) : ℕ) : Fp) * output.zLast) ∧
          (false = true → output.zLast = 0 ∧ input.element.val < 2 ^ (K * numWords K)) := rfl

private theorem copyCheck_assumptions_eq (K : ℕ) :
    (LookupRangeCheck.copyCheck K (numWords K) false).Assumptions
      = fun _ => 2 ^ (K * numWords K) ≤ PALLAS_BASE_CARD ∧ 2 ^ K ≤ PALLAS_BASE_CARD := rfl

private theorem copyCheck_envAssumptions_eq (K : ℕ) (cfg : LookupRangeCheck.Config K)
    (env : Placed Environment Fp) :
    (LookupRangeCheck.copyCheck K (numWords K) false).EnvAssumptions cfg env
      = (LookupRangeCheck.TableLoaded K cfg env.env ∧ cfg.qLookup.index ≠ cfg.qRunning.index) :=
  rfl

private theorem copyCheck_proverAssumptions_eq (K : ℕ) :
    (LookupRangeCheck.copyCheck K (numWords K) false).ProverAssumptions
      = fun input _ => (false = true → input.element.val < 2 ^ (K * numWords K)) := rfl

/-- The copyCheck child's `ProverSpec` (C6): the honest nat decomposition of the tail. -/
private theorem copyCheck_proverSpec_eq (K : ℕ) :
    (LookupRangeCheck.copyCheck K (numWords K) false).ProverSpec
      = fun input output _ => output.zLast = ((input.element.val / 2 ^ (K * numWords K) : ℕ) : Fp) :=
  rfl

/-- The child call's output record (`copyCheck = rangeCheck.toFormal`, so the layouter output at
region `i` is `rangeCheck`'s region output at offset 0): `z0` at row 0, `zLast` at row `numWords`. -/
private theorem copyCheck_output (K : ℕ) (cfg : LookupRangeCheck.Config K)
    (inp : Var LookupRangeCheck.Inputs Fp) (i : RegionIndex) :
    (LookupRangeCheck.copyCheck K (numWords K) false).output cfg inp i
      = { z0 := .of i 0 cfg.runningSum,
          zLast := .of i (numWords K) cfg.runningSum } := by
  show ((LookupRangeCheck.rangeCheck K (numWords K) false).synthesize cfg 0 inp).output i = _
  simp only [LookupRangeCheck.rangeCheck, circuit_norm, RegionCircuit.output_bind,
    LookupRangeCheck.output_cellAt, LookupRangeCheck.operations_cellAt,
    RegionCircuit.operations_bind, Halo2.operations_copyAdvice,
    Bool.false_eq_true, if_false, Nat.zero_add]

/-- Eval of the child's single-field input struct `{ element := c }`. -/
private theorem copyCheckInputs_eval_eq (env : Placed Environment Fp) (c : AssignedCell Fp) :
    eval env ({ element := c } : LookupRangeCheck.Inputs (AssignedCell Fp))
      = { element := eval env c } := by
  simp only [circuit_norm]

private theorem copyCheckInputs_eval_eq_prover (env : Placed ProverEnvironment Fp)
    (c : AssignedCell Fp) :
    eval env ({ element := c } : LookupRangeCheck.Inputs (AssignedCell Fp))
      = { element := eval env c } := by
  simp only [circuit_norm]

/-! ## The gadget bundle

`overflow_check` at the LAYOUTER level (`overflow.rs:101-208`), three faithful sibling regions.
Parameterized by `K` and the arithmetic bridge `K · numWords K = 130`. -/

/-- The region count of `synthesize`: region 1 (witness s), the copyCheck child (1 region), and
region 3 (gate) — three regions, independent of the starting index. -/
theorem synthesize_regionCount (K : ℕ) (cfg : Config K) (input : Inputs (AssignedCell Fp))
    (i : RegionIndex) :
    Operations.regionCount ((synthesize K cfg input).operations i) = 3 := by
  simp only [synthesize, circuit_norm, operations_assignRegion, Operations.regionCount_append,
    Operations.regionCount]
  -- the copyCheck child call contributes exactly 1 region (its `toFormal` wrapping region)
  rw [show ∀ (j : RegionIndex),
      Operations.regionCount (((LookupRangeCheck.copyCheck K (numWords K) false).call
        cfg.lookupConfig { element := AssignedCell.of i 0 cfg.adv0 }).operations j) = 1
      from fun j => by
        simp only [FormalCircuit.call, Circuit.operations, Operations.regionCount,
          LookupRangeCheck.copyCheck, FormalRegionCircuit.toFormal, assignRegion, Nat.add_zero]]

def circuit (K : ℕ) (hKW : K * numWords K = 130) :
    FormalCircuit Fp (LookupRangeCheck.Config K × Column .advice × Column .advice ×
      Column .advice) (Config K) Inputs unit where
  name := "overflow checks"

  configure := fun (lookupConfig, adv0, adv1, adv2) => configure K lookupConfig adv0 adv1 adv2

  synthesize cfg input := synthesize K cfg input

  elaborated cfg :=
    { output := fun _ _ => ()
      regionCount := fun _ => 3
      output_eq := by intro _ _; rfl
      regionCount_eq := fun input i => (synthesize_regionCount K cfg input i).symm }

  EnvAssumptions cfg env := EnvAssumptions K cfg env

  Assumptions _ :=
    2 ^ (K * numWords K) ≤ PALLAS_BASE_CARD ∧ 2 ^ K ≤ PALLAS_BASE_CARD

  Spec input _ _ := Spec input

  ProverAssumptions input _ := Spec input

  -- ══ Soundness ══
  soundness := by
    intro cfg
    rw [FormalCircuit.soundness_iff]
    intro i₀ env input_var input output h_input h_output hE hA hc
    obtain ⟨hTable, hDistinct⟩ := hE
    -- peel the three-region layouter structure: region 1 (witness s) at i₀, the copyCheck child
    -- at i₀+1, region 3 (gate) at i₀+2. `circuit_norm` splits the binds into the region/subcircuit
    -- chunks with the region counter threaded.
    simp only [synthesize, circuit_norm] at hc
    -- reduce the gate-region's index `i₀ + 1 + regionCount(copyCheck call)` to `i₀ + 2`
    rw [show Operations.regionCount (((LookupRangeCheck.copyCheck K (numWords K) false).call
        cfg.lookupConfig { element := AssignedCell.of i₀ 0 cfg.adv0 }).operations (i₀ + 1)) = 1
      from by simp only [FormalCircuit.call, Circuit.operations, Operations.regionCount,
        LookupRangeCheck.copyCheck, FormalRegionCircuit.toFormal, assignRegion, Nat.add_zero]] at hc
    -- hc : copyCheck chunk (region i₀+1) ∧ gate-region constraints (region i₀+2). The witness-s
    -- region (i₀) has no constraints (bare assignAdvice → True), dropped by simp.
    obtain ⟨hChild, hGate⟩ := hc
    -- consume the copyCheck child via the engine → its EnvA → A → Spec implication
    subcircuit_rw at hChild
    -- discharge the child's EnvAssumptions (BY PROJECTION from the parent's) and Assumptions
    have hChildE : (LookupRangeCheck.copyCheck K (numWords K) false).EnvAssumptions
        cfg.lookupConfig env := by
      rw [copyCheck_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩
    have hChildA : (LookupRangeCheck.copyCheck K (numWords K) false).Assumptions
        (eval env ({ element := AssignedCell.of i₀ 0 cfg.adv0 }
          : LookupRangeCheck.Inputs (AssignedCell Fp))) := by
      rw [copyCheck_assumptions_eq]; exact hA
    have hSpec := hChild hChildE hChildA
    rw [copyCheck_spec_eq, copyCheck_output, copyCheckInputs_eval_eq] at hSpec
    -- the child decomposition: s = lo + 2^{K·numWords}·zLast, lo < 2^{K·numWords}
    obtain ⟨-, ⟨lo, hlo, hDecomp⟩, -⟩ := hSpec
    -- reduce the gate region constraints (5 gate polys + the copies). The gate is at region i₀+2.
    simp only [gateRegion, circuit_norm, overflowGate, Constraints.withSelector] at hGate
    obtain ⟨hCz0, hCz130, hCk254, hCalpha, hCsml, hCs,
      hSCheck, hRecovery, hLoZero, hSMLcheck, hCanon⟩ := hGate
    -- reduce the copyCheck child's output cell in the `s_minus_lo_130` copy, then land all
    -- copies + the child decomposition on `env.advice` reads
    rw [copyCheck_output] at hCsml
    simp only [AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
      Cell.of_column, Environment.get_advice] at hDecomp hCs hCsml
    -- assemble the donor `Spec`
    simp only [Spec]
    provable_type_simp
    obtain ⟨hIalpha, hIz0, hIz130, hIk254⟩ := h_input
    rw [hIalpha] at hCalpha; rw [hIz0] at hCz0
    rw [hIz130] at hCz130; rw [hIk254] at hCk254
    have h2124 : (2 ^ 124 : Fp) = (2 : Fp) ^ 124 := by norm_num
    rw [hKW] at hDecomp hlo
    rw [show (((2 ^ 130 : ℕ) : Fp)) = (2 ^ 130 : Fp) from by norm_num] at hDecomp
    refine ⟨?_, ?_, ?_⟩
    · -- recovery: z_0 = alpha + t_q
      rw [← hCz0, ← hCalpha, ← sub_eq_zero]; linear_combination hRecovery
    · -- k_254 = 0 ∨ z_130 = 2^124
      rw [← hCk254, ← hCz130]
      rcases mul_eq_zero.mp hLoZero with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h2124]; linear_combination sub_eq_zero.mp h)
    · -- the canonicity existential: sHi = zLast, sLo = lo
      refine ⟨env.env.advice cfg.lookupConfig.runningSum
        ((env.place (i₀ + 1) + numWords K : ℕ) : ℤ), lo, hlo, ?_, ?_, ?_⟩
      · -- alpha + k_254·2^130 = lo + 2^130·zLast, chaining:
        --   gate alpha/k254 → s cell (s_check) → original s (s copy) → decomposition
        rw [← hCalpha, ← hCk254]
        -- normalize hDecomp's `place i₀ + 0` to `place i₀` (defeq) so hCs lines up
        rw [show ((env.place i₀ + 0 : ℕ) : ℤ) = ((env.place i₀ : ℕ) : ℤ) from by norm_num] at hDecomp
        -- s_check gives adv2@(gate cur) = alpha_gate + k254_gate·2^130; hCs gives adv2@(gate cur) =
        -- adv0@(place i₀) = s_original; hDecomp splits s_original. Chain by linear_combination.
        linear_combination -hSCheck + hCs + hDecomp
      · -- k_254 = 0 ∨ zLast = 0
        rw [← hCk254]
        rcases mul_eq_zero.mp hSMLcheck with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [← hCsml]; exact h)
      · -- k_254 = 1 ∨ z_130 ≠ 0 ∨ zLast = 0
        rw [← hCk254, ← hCz130]
        rcases mul_eq_zero.mp hCanon with hK | hRest
        · rcases mul_eq_zero.mp hK with hK1 | hEta
          · exact Or.inl (by linear_combination -hK1)
          · refine Or.inr (Or.inl ?_)
            intro hz
            rw [hz, zero_mul] at hEta
            exact zero_ne_one (by linear_combination -hEta)
        · exact Or.inr (Or.inr (by rw [← hCsml]; exact hRest))

  -- ══ Completeness ══
  completeness := by
    intro cfg
    rw [FormalCircuit.completeness_iff]
    intro i₀ env input_var input output h_input h_output hwit hE hA hpa
    obtain ⟨hTable, hDistinct⟩ := hE
    -- peel the witness list: region 1 (witness s) ++ copyCheck child ++ gate region.
    simp only [synthesize, circuit_norm] at hwit ⊢
    -- reduce the copyCheck call's regionCount to 1, so the gate region is at i₀+2
    rw [show Operations.regionCount (((LookupRangeCheck.copyCheck K (numWords K) false).call
        cfg.lookupConfig { element := AssignedCell.of i₀ 0 cfg.adv0 }).operations (i₀ + 1)) = 1
      from by simp only [FormalCircuit.call, Circuit.operations, Operations.regionCount,
        LookupRangeCheck.copyCheck, FormalRegionCircuit.toFormal, assignRegion, Nat.add_zero]]
      at hwit ⊢
    obtain ⟨hWs, hWchild, hWgate⟩ := hwit
    -- the honest witnessed `s` value (region i₀ row 0 = alpha + k254·2^130)
    simp only [sWit, eval_ofFExpr_zero, Witgen.FExprOver.eval,
      WitgenEnv.readVar_halo2, AssignedCell.eval] at hWs
    -- consume the copyCheck child via the engine's completeness mode: strengthen the child's goal
    -- chunk to `EnvA ∧ A ∧ PA` and introduce `h_spec_0 : EnvA → A → PA → Spec ∧ ProverSpec`.
    subcircuit_rw
    obtain ⟨hIalpha, hIz0, hIz130, hIk254⟩ := h_input
    refine ⟨?_, ?_⟩
    · -- copyCheck child preconditions: EnvA (projection) ∧ A (field card) ∧ PA (vacuous, non-strict)
      refine ⟨?_, ?_, ?_⟩
      · rw [copyCheck_envAssumptions_eq]
        simp only [Placed.toEnvironment_env] at hTable ⊢
        exact ⟨hTable, hDistinct⟩
      · rw [copyCheck_assumptions_eq]; exact hA
      · rw [copyCheck_proverAssumptions_eq]; simp
    · -- the gate region constraints, from the honest values + the child's derived contract
      -- (`h_spec_0`, verifier `Spec` + honest `ProverSpec`) + the honest `Spec` premise (`hpa`).
      have hChildE : (LookupRangeCheck.copyCheck K (numWords K) false).EnvAssumptions
          cfg.lookupConfig env.toEnvironment := by
        rw [copyCheck_envAssumptions_eq]
        simp only [Placed.toEnvironment_env] at hTable ⊢
        exact ⟨hTable, hDistinct⟩
      have hChildA : (LookupRangeCheck.copyCheck K (numWords K) false).Assumptions
          (eval env.toEnvironment ({ element := AssignedCell.of i₀ 0 cfg.adv0 }
            : LookupRangeCheck.Inputs (AssignedCell Fp))) := by
        rw [copyCheck_assumptions_eq]; exact hA
      have hChildPA : (LookupRangeCheck.copyCheck K (numWords K) false).ProverAssumptions
          (eval env ({ element := AssignedCell.of i₀ 0 cfg.adv0 }
            : LookupRangeCheck.Inputs (AssignedCell Fp))) env.env.hint := by
        rw [copyCheck_proverAssumptions_eq]; simp
      obtain ⟨hChildSpec, hChildPS⟩ := h_spec_0 hChildE hChildA hChildPA
      rw [copyCheck_spec_eq, copyCheck_output, copyCheckInputs_eval_eq] at hChildSpec
      rw [copyCheck_proverSpec_eq, copyCheck_output, copyCheckInputs_eval_eq_prover] at hChildPS
      obtain ⟨-, ⟨lo, hlo, hDecompV⟩, -⟩ := hChildSpec
      simp only [AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
        Cell.of_column, Environment.get_advice, AssignedCell.eval] at hChildPS hDecompV hWs
      -- reduce the gate region constraints to the 6 copies + 5 gate polys
      simp only [gateRegion, circuit_norm, overflowGate, Constraints.withSelector]
      rw [copyCheck_output]
      simp only [AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
        Cell.of_column, Environment.get_advice, AssignedCell.eval]
      -- honest Spec facts from `hpa` (the honest-caller precondition = the overflow `Spec`)
      simp only [Spec] at hpa
      provable_type_simp
      obtain ⟨hRec, hLoZ, sHi, sLo, hsLo_lt, hkey, hHiZ, hEtaSpec⟩ := hpa
      -- peel the gate region witnesses: the 6 copy assignAdvice witnesses + η + s copy
      simp only [gateRegion, circuit_norm, Halo2.operations_copyAdvice, operations_assignAdvice,
        RegionOperations.extendsWitnesses_append, RegionOperations.extendsWitnesses_cons,
        RegionOperations.extendsWitnesses_nil, RegionOperation.extendsWitness_assignAdvice,
        RegionOperation.extendsWitness_constrainEqual] at hWgate
      -- reduce the copyCheck child output cell in the s_minus_lo_130 copy witness
      rw [copyCheck_output] at hWgate
      -- the copy witnesses: each gate-window cell = its source (the `.expr src` assignAdvice value)
      simp only [etaWit, eval_ofFExpr_zero, Witgen.FExprOver.eval, WitgenEnv.readVar_halo2,
        AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
        Cell.of_column, Environment.get_advice] at hWgate
      obtain ⟨hWz0, hWz130, hWeta, hWk254, hWalpha, hWsml, hWs2⟩ := hWgate
      -- the honest s cell value (region i₀) = alpha + k254·2^130 (from the `s` witness `hWs`)
      -- and the child tail nat value (`hChildPS`) — normalize the `place i₀ + 0` spelling
      rw [show ((env.place i₀ + 0 : ℕ) : ℤ) = ((env.place i₀ : ℕ) : ℤ) from by norm_num]
        at hChildPS hDecompV
      rw [hKW] at hDecompV hlo hChildPS
      rw [show (((2 ^ 130 : ℕ) : Fp)) = (2 ^ 130 : Fp) from by norm_num] at hDecompV
      -- `sHi = 0 → child zLast = 0` (the only direction the canonicity gate needs). With `sHi = 0`
      -- the honest `Spec` pins `s = ↑sLo < 2^130`, so `s.val < 2^130` and the shift is 0.
      have hCard130 : 2 ^ 130 < PALLAS_BASE_CARD := by
        norm_num [PALLAS_BASE_CARD]
      have hzLastZero : sHi = 0 → env.env.advice cfg.lookupConfig.runningSum
          ((env.place (i₀ + 1) + numWords K : ℕ) : ℤ) = 0 := by
        intro hsHi0
        rw [hChildPS]
        have hsVal : (env.env.advice cfg.adv0 ((env.place i₀ : ℕ) : ℤ)).val < 2 ^ 130 := by
          have hs_eq : env.env.advice cfg.adv0 ((env.place i₀ : ℕ) : ℤ) = (sLo : Fp) := by
            rw [hWs, hkey, hsHi0]; ring
          rw [hs_eq, ZMod.val_natCast_of_lt (lt_trans hsLo_lt hCard130)]; exact hsLo_lt
        rw [Nat.div_eq_of_lt hsVal, Nat.cast_zero]
      have h2124 : (2 ^ 124 : Fp) = (2 : Fp) ^ 124 := by norm_num
      -- assemble: the 6 copies (from the witnesses) + the 5 gate polys
      refine ⟨hWz0, hWz130, hWk254, hWalpha, hWsml, hWs2, ?_, ?_, ?_, ?_, ?_⟩
      · -- s_check: honest s cell (adv2@gate cur, copied from region i₀) = alpha_gate + k254_gate·2^130
        rw [hWs2, hWs, hWalpha, hWk254]; ring
      · -- recovery: z_0 − alpha − t_q = 0
        rw [hWz0, hWalpha]
        rw [← sub_eq_zero] at hRec; linear_combination hRec
      · -- lo_zero: k254·(z130 − 2^124) = 0
        rw [hWk254, hWz130]
        rcases hLoZ with h | h
        · rw [h]; ring
        · rw [h, h2124]; ring
      · -- s_minus_lo_130_check: k254·s_minus_lo_130 = 0 (s_minus_lo_130 = child zLast)
        rw [hWk254, hWsml]
        rcases hHiZ with h | h
        · rw [h]; ring
        · rw [hzLastZero h]; ring
      · -- canonicity: (1 − k254)·(1 − z130·η)·s_minus_lo_130 = 0, η = inv0(z130)
        rw [hWk254, hWz130, hWeta, hWsml]
        rcases hEtaSpec with h | hz | h
        · rw [h]; ring
        · rw [mul_inv_cancel₀ hz]; ring
        · rw [hzLastZero h]; ring

end MulOverflow

end Halo2.Ironwood.Ecc
