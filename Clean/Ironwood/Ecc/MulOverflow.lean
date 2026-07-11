import Clean.Halo2
import Clean.Halo2.Subcircuit
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

/-! ## The overflow-check region body

`overflow_check` (`overflow.rs:101-188`) plus `s_minus_lo_130` (`190-208`), laid out in a
single ambient region relative to `offset`. Rust uses three separate assign_regions; the
Halo2-Clean single-region model places them sequentially. The gate row is `g := offset + 1`,
so the gate's `prev/cur/next` rows are `offset, offset+1, offset+2`.

Row layout:
- `advices[2] @ offset+1` : witness `s` (`overflow.rs:118-129`; copied into the gate's `s`
  cur cell — here assigned directly at the gate's cur row).
- `advices[1] @ offset`   : copy `k_254` (`overflow.rs:162`).
- `advices[1] @ offset+1` : copy `alpha` (`overflow.rs:165-170`).
- `advices[0] @ offset`   : copy `z_0` (`overflow.rs:145`).
- `advices[0] @ offset+1` : copy `z_130` (`overflow.rs:148`).
- `advices[0] @ offset+2` : witness `η = inv0(z_130)` (`overflow.rs:151-158`).
- child `rangeCheck` at `offset+3` on the `s` cell (`overflow.rs:200-205`); its `zLast`
  output is `s_minus_lo_130`.
- `advices[1] @ offset+2` : copy `s_minus_lo_130` (the child's `zLast`; `overflow.rs:173`).
- enable `q_mul_overflow` at `offset+1` (`overflow.rs:142`).

The child uses its OWN `runningSum` column (in `lookupConfig`), disjoint from `advices`, so
its rows do not collide with the overflow window. -/

/-- The overflow-check body. Returns `unit`. -/
def body (K : ℕ) (cfg : Config K) (input : Inputs (AssignedCell Fp)) (offset : ℕ) :
    RegionCircuit Fp Unit := do
  -- s = alpha + k_254·2^130, at the gate's `s` cur cell (advices[2] @ offset+1)
  let sCell ← assignAdvice cfg.adv2 (offset + 1) (sWit input)
  -- copies into the gate window
  let _k254 ← copyAdvice input.k254 cfg.adv1 offset               -- k_254 (prev)
  let _alpha ← copyAdvice input.alpha cfg.adv1 (offset + 1)       -- alpha (cur)
  let _z0 ← copyAdvice input.z0 cfg.adv0 offset                   -- z_0 (prev)
  let _z130 ← copyAdvice input.z130 cfg.adv0 (offset + 1)         -- z_130 (cur)
  -- η = inv0(z_130), at advices[0] @ offset+2 (next)
  let _eta ← assignAdvice cfg.adv0 (offset + 2) (etaWit input)
  -- decompose the low 130 bits of s with the lookup child; s_minus_lo_130 = zLast
  let dec ← (LookupRangeCheck.rangeCheck K (numWords K) false).call cfg.lookupConfig (offset + 3)
    { element := sCell }
  -- copy s_minus_lo_130 into advices[1] @ offset+2 (next)
  let _sMinusLo130 ← copyAdvice dec.zLast cfg.adv1 (offset + 2)
  -- enable the overflow gate at the middle row
  (overflowGate K cfg).enable (offset + 1)
  return ()

/-! ## Contract

`EnvAssumptions` states the table fact + selector distinctness over the *projected* child
sub-config `cfg.lookupConfig` — exactly the child's `EnvAssumptions` on that config. This is
the derived-sub-config threading this consumer exists to surface. `Spec` is the donor
`OverflowCheck.Spec`, lifted wholesale. -/

/-- The parent `EnvAssumptions`: the child's `TableLoaded` over the projected `lookupConfig`,
plus the selector distinctness the child needs. Definitionally the child's `EnvAssumptions`
applied to `cfg.lookupConfig`. -/
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

/-! ## Contract-projection bridges (the child stays folded)

`rfl`-bridges exposing exactly the child rangeCheck's contract fields without unfolding the
bundle literal — the MulComplete/Chain pattern. FRAMEWORK CANDIDATE: a deriving-style
mechanism exposing a `FormalRegionCircuit` literal's contract projections without unfolding. -/

private theorem rangeCheck_spec_eq (K : ℕ) :
    (LookupRangeCheck.rangeCheck K (numWords K) false).Spec
      = fun input output _ =>
          output.z0 = input.element ∧
          (∃ lo : ℕ, lo < 2 ^ (K * numWords K) ∧
            input.element = (lo : Fp) + ((2 ^ (K * numWords K) : ℕ) : Fp) * output.zLast) ∧
          (false = true → output.zLast = 0 ∧ input.element.val < 2 ^ (K * numWords K)) := rfl

private theorem rangeCheck_assumptions_eq (K : ℕ) :
    (LookupRangeCheck.rangeCheck K (numWords K) false).Assumptions
      = fun _ => 2 ^ (K * numWords K) ≤ PALLAS_BASE_CARD ∧ 2 ^ K ≤ PALLAS_BASE_CARD := rfl

private theorem rangeCheck_envAssumptions_eq (K : ℕ) (cfg : LookupRangeCheck.Config K)
    (env : Placed Environment Fp) :
    (LookupRangeCheck.rangeCheck K (numWords K) false).EnvAssumptions cfg env
      = (LookupRangeCheck.TableLoaded K cfg env.env ∧ cfg.qLookup.index ≠ cfg.qRunning.index) :=
  rfl

private theorem rangeCheck_proverAssumptions_eq (K : ℕ) :
    (LookupRangeCheck.rangeCheck K (numWords K) false).ProverAssumptions
      = fun input _ => (false = true → input.element.val < 2 ^ (K * numWords K)) := rfl

/-- The child call's output record: the `z0`/`zLast` cells at their fixed region-local rows
(`rangeCheck.synthesize`'s `cellAt` reads: `z0` at `offset`, `zLast` at `offset + numWords`). -/
private theorem rangeCheck_call_output (K : ℕ) (cfg : LookupRangeCheck.Config K)
    (offset : ℕ) (inp : Var LookupRangeCheck.Inputs Fp) (self : RegionIndex) :
    ((LookupRangeCheck.rangeCheck K (numWords K) false).call cfg offset inp).output self
      = { z0 := .of self offset cfg.runningSum,
          zLast := .of self (offset + numWords K) cfg.runningSum } := rfl

/-- The child's output var in the `FormalRegionCircuit.output` spelling (the composition iff's
form) — same record as `rangeCheck_call_output`. -/
private theorem rangeCheck_output (K : ℕ) (cfg : LookupRangeCheck.Config K)
    (offset : ℕ) (inp : Var LookupRangeCheck.Inputs Fp) (self : RegionIndex) :
    (LookupRangeCheck.rangeCheck K (numWords K) false).output cfg offset inp self
      = { z0 := .of self offset cfg.runningSum,
          zLast := .of self (offset + numWords K) cfg.runningSum } := rfl

/-- Eval of the child's single-field input struct `{ element := c }`. Used only on
locally-stated equations (all spellings elaborated at the same site). -/
private theorem rangeCheckInputs_eval_eq (env : Placed Environment Fp) (c : AssignedCell Fp) :
    eval env ({ element := c } : LookupRangeCheck.Inputs (AssignedCell Fp))
      = { element := eval env c } := by
  simp only [circuit_norm]

/-! ## Value-level bridge: `2^{K·numWords K} = 2^130`

For `K = 10`, `K · numWords K = 10 · 13 = 130`, so the child's decomposition `s = lo +
2^{K·numWords}·zLast` with `lo < 2^{K·numWords}` is exactly the donor's `s = sLo + 2^130·sHi`
with `sLo < 2^130`. The parent carries `K · numWords K = 130` as a hypothesis (discharged by
`rfl`/`norm_num` at the `K = 10` instantiation), keeping the port `K`-generic. -/

/-! ## Completeness helper (the MulComplete FRAMEWORK CANDIDATE, copied)

FRAMEWORK CANDIDATE (for `Clean/Halo2/Subcircuit.lean`): the absorption completeness iff lets
a parent DISCHARGE a child chunk but does not expose the child's contract VALUE. This parent's
honest-value bookkeeping needs the child's `Spec` (the `s_minus_lo_130` decomposition), so it
runs `child.completeness` then `child.soundness` on the verifier view. Copied verbatim from
`MulComplete.call_constraints_and_spec` per the no-cross-gadget-import convention. -/

/-- Completeness-side consumption of a child call, exposing the child's verifier-view `Spec`. -/
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

`overflow_check` over the running sums. Parameterized by `K` and the arithmetic bridge
`K · numWords K = 130`. -/

def circuit (K : ℕ) (hKW : K * numWords K = 130) :
    FormalRegionCircuit Fp (LookupRangeCheck.Config K × Column .advice × Column .advice ×
      Column .advice) (Config K) Inputs unit where
  name := "overflow checks"

  configure := fun (lookupConfig, adv0, adv1, adv2) => configure K lookupConfig adv0 adv1 adv2

  synthesize cfg offset input := body K cfg input offset

  EnvAssumptions cfg env := EnvAssumptions K cfg env

  -- The field-capacity bounds the rangeCheck child needs (Rust `assert!`); at `K = 10`,
  -- `2^130·2^130 = 2^260 < |Fp|` and `2^10 < |Fp|`. Carried as an assumption (discharged by
  -- `norm_num` at the concrete `K`).
  Assumptions _ :=
    2 ^ (K * numWords K) ≤ PALLAS_BASE_CARD ∧ 2 ^ K ≤ PALLAS_BASE_CARD

  Spec input _ _ := Spec input

  -- honest-prover precondition: the inputs genuinely satisfy the overflow-check `Spec` (the
  -- Rust caller guarantees this — the overflow check is an *assertion*, only complete on inputs
  -- where `z_0 = alpha + t_q` and the canonicity facts hold; the established assertion-gadget
  -- pattern, cf. the donor `OverflowCheck.circuit`'s `FormalAssertion` completeness taking the
  -- `Spec` as its premise). The `sHi`/`sLo` existential in `Spec` matches the honest child
  -- decomposition (the honest prover's `s` really splits that way).
  ProverAssumptions input _ := Spec input

  -- ══ Soundness ══
  soundness := by
    intro cfg offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output hE hA hc
    obtain ⟨hTable, hDistinct⟩ := hE
    -- peel the body: the constraint-bearing ops are the 4 gate-window copies, the child chunk,
    -- the s_minus_lo_130 copy, and the gate (5 polys). The `s`/`η` witness assigns bear no
    -- constraint. Unfold the gate in the same pass so all 5 polys reduce uniformly.
    simp only [body, circuit_norm, overflowGate, Constraints.withSelector,
      RegionCircuit.operations_bind,
      operations_assignAdvice, operations_copyAdvice, operations_enable,
      RegionOperations.constraints_append] at hc
    obtain ⟨hCk254, hCalpha, hCz0, hCz130, hChild, hCsml,
      hSCheck, hRecovery, hLoZero, hSMLcheck, hCanon⟩ := hc
    -- ▸▸ composition-iff rw site (the rangeCheck child; delimited per MulComplete) ◂◂
    rw [FormalRegionCircuit.subcircuit_constraints_iff_soundness
          (LookupRangeCheck.rangeCheck K (numWords K) false) cfg.lookupConfig (offset + 3) self
          ⟨env.place, env.env⟩
          { element := AssignedCell.of self (offset + 1) cfg.adv2 }] at hChild
    obtain ⟨-, hSpecFn⟩ := hChild
    -- discharge the child's EnvAssumptions BY PROJECTION from the parent's, and its Assumptions
    have hChildE : (LookupRangeCheck.rangeCheck K (numWords K) false).EnvAssumptions
        cfg.lookupConfig ⟨env.place, env.env⟩ := by
      rw [rangeCheck_envAssumptions_eq]; exact ⟨hTable, hDistinct⟩
    have hChildA : (LookupRangeCheck.rangeCheck K (numWords K) false).Assumptions
        (eval (⟨env.place, env.env⟩ : Placed Environment Fp)
          ({ element := AssignedCell.of self (offset + 1) cfg.adv2 }
            : LookupRangeCheck.Inputs (AssignedCell Fp))) := by
      rw [rangeCheck_assumptions_eq]; exact hA
    have hSpec := hSpecFn hChildE hChildA
    rw [rangeCheck_spec_eq, rangeCheck_output, rangeCheckInputs_eval_eq] at hSpec
    -- the child's decomposition: s = lo + 2^{K·numWords}·zLast, lo < 2^{K·numWords}
    obtain ⟨-, ⟨lo, hlo, hDecomp⟩, -⟩ := hSpec
    -- reduce the child-output cell in the s_minus_lo copy; land the input value on its components
    rw [rangeCheck_call_output] at hCsml
    simp only [AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
      Cell.of_column, Environment.get_advice] at hCsml hDecomp
    -- `provable_type_simp` turns `h_input` into the four component equalities `input_X = <cell
    -- read>` and substitutes them in the goal (`Spec input` becomes the bare-component form).
    simp only [Spec]
    provable_type_simp
    obtain ⟨hIalpha, hIz0, hIz130, hIk254⟩ := h_input
    -- chain each copy to its input component (`hCX : advice = <cell read> = input_X`)
    rw [hIalpha] at hCalpha; rw [hIz0] at hCz0
    rw [hIz130] at hCz130; rw [hIk254] at hCk254
    have h2124 : (2 ^ 124 : Fp) = (2 : Fp) ^ 124 := by norm_num
    -- the child decomposition, with `K·numWords K` reduced to `130` and the coefficient cast
    -- normalized (`((2^130 : ℕ) : Fp) = (2^130 : Fp)`) WITHOUT push_cast touching the row indices
    rw [hKW] at hDecomp hlo
    rw [show (((2 ^ 130 : ℕ) : Fp)) = (2 ^ 130 : Fp) from by norm_num] at hDecomp
    -- ── assemble the donor `Spec` ──
    refine ⟨?_, ?_, ?_⟩
    · -- recovery: z_0 = alpha + t_q — bridge the input cells via the copies, then `hRecovery`
      rw [← hCz0, ← hCalpha]
      rw [← sub_eq_zero]; linear_combination hRecovery
    · -- k_254 = 0 ∨ z_130 = 2^124
      rw [← hCk254, ← hCz130]
      rcases mul_eq_zero.mp hLoZero with h | h
      · exact Or.inl h
      · exact Or.inr (by rw [h2124]; linear_combination sub_eq_zero.mp h)
    · -- the canonicity existential: sHi = zLast (the child high tail), sLo = lo
      refine ⟨env.env.advice cfg.lookupConfig.runningSum
        ((env.place self + (offset + 3 + numWords K) : ℕ) : ℤ), lo, hlo, ?_, ?_, ?_⟩
      · -- alpha + k_254·2^130 = lo + 2^130·zLast (from `s_check` + the child decomposition)
        rw [← hCalpha, ← hCk254]
        have hsEq : env.env.advice cfg.adv2 ((env.place self + (offset + 1) : ℕ) : ℤ)
            = env.env.advice cfg.adv1 ((env.place self + (offset + 1) : ℕ) : ℤ)
              + env.env.advice cfg.adv1 ((env.place self + offset : ℕ) : ℤ) * (2 ^ 130 : Fp) := by
          rw [← sub_eq_zero]; linear_combination hSCheck
        rw [hsEq] at hDecomp
        linear_combination hDecomp
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
  -- The honest copies pin the gate cells to the input cell values; the honest `Spec` (`hpa`)
  -- supplies `recovery`/`lo_zero` and the canonicity disjunctions; `s_check` is the `s`
  -- witness; the honest child decomposition of `s` matches the `Spec`'s `sHi`/`sLo` split (both
  -- are the unique `s = low + 2^130·high`, `low < 2^130`), so the honest `s_minus_lo_130` cell
  -- equals the `Spec`'s `sHi`, discharging `s_minus_lo_130_check`/`canonicity`.
  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit hE hA hpa
    -- peel the witnesses (keep the `.eval` of the assign programs FOLDED — do not unfold
    -- `WitgenIROver.eval` here, so `eval_ofFExpr_zero` can fire on the `s`/`η` programs below)
    simp only [body, circuit_norm,
      RegionCircuit.operations_bind,
      operations_assignAdvice, operations_copyAdvice, operations_enable,
      RegionOperations.extendsWitnesses_append] at hwit ⊢
    obtain ⟨hWs, hWk254, hWalpha, hWz0, hWz130, hWeta, hWchild, hWsMinusLo⟩ := hwit
    obtain ⟨hTable, hDistinct⟩ := hE
    -- the honest witnessed `s` and `η` values, in field form (`eval_ofFExpr_zero` reduces the
    -- `ofFExpr` program to its `FExprOver.eval`; then the arithmetic tree and the cell reads)
    simp only [sWit, etaWit, eval_ofFExpr_zero, Witgen.FExprOver.eval,
      WitgenEnv.readVar_halo2, AssignedCell.eval] at hWs hWeta
    -- ── the child, via `call_constraints_and_spec`: its honest decomposition of `s` ──
    obtain ⟨hCchild, hSpecChild⟩ := call_constraints_and_spec
      (LookupRangeCheck.rangeCheck K (numWords K) false) cfg.lookupConfig (offset + 3) self env
      { element := AssignedCell.of self (offset + 1) cfg.adv2 } hWchild
      (by rw [rangeCheck_envAssumptions_eq]
          simp only [Placed.toEnvironment_env] at hTable ⊢
          exact ⟨hTable, hDistinct⟩)
      (by rw [rangeCheck_assumptions_eq]; exact hA)
      (by rw [rangeCheck_proverAssumptions_eq]; simp)
    rw [rangeCheck_spec_eq, rangeCheck_output, rangeCheckInputs_eval_eq] at hSpecChild
    obtain ⟨-, ⟨lo, hlo, hDecomp⟩, -⟩ := hSpecChild
    -- reduce the child-output cell (`.of self … runningSum`) in the honest decomposition
    simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
      Cell.of_column, Environment.get_advice] at hDecomp
    rw [hKW] at hDecomp hlo
    rw [show (((2 ^ 130 : ℕ) : Fp)) = (2 ^ 130 : Fp) from by norm_num] at hDecomp
    -- ── land the honest input/output components and the `Spec` facts (`hpa`) ──
    simp only [Spec] at hpa
    provable_type_simp
    obtain ⟨hIalpha, hIz0, hIz130, hIk254⟩ := h_input
    obtain ⟨hRec, hLoZ, sHi, sLo, hsLo_lt, hkey, hHiZ, hEtaSpec⟩ := hpa
    -- honest copy VALUE facts (kept separate — the pristine `hW*` are the copy CONSTRAINTS the
    -- goal needs, so we do not rewrite them). Each copy's cell read equals its input component.
    have ealpha : env.env.toEnvironment.advice cfg.adv1 ((env.place self + (offset + 1) : ℕ) : ℤ)
        = input_alpha := hWalpha.trans hIalpha
    have ek254 : env.env.toEnvironment.advice cfg.adv1 ((env.place self + offset : ℕ) : ℤ)
        = input_k254 := hWk254.trans hIk254
    have ez0 : env.env.toEnvironment.advice cfg.adv0 ((env.place self + offset : ℕ) : ℤ)
        = input_z0 := hWz0.trans hIz0
    have ez130 : env.env.toEnvironment.advice cfg.adv0 ((env.place self + (offset + 1) : ℕ) : ℤ)
        = input_z130 := hWz130.trans hIz130
    -- the honest `s` cell value = alpha + k254·2^130 (the `s` witness), and its child split
    have hsCellVal : env.env.toEnvironment.advice cfg.adv2 ((env.place self + (offset + 1) : ℕ) : ℤ)
        = input_alpha + input_k254 * (2 ^ 130 : Fp) := by
      rw [hWs, hIalpha, hIk254]
    have hDecompVal : input_alpha + input_k254 * (2 ^ 130 : Fp)
        = (lo : Fp) + (2 ^ 130 : Fp)
            * env.env.toEnvironment.advice cfg.lookupConfig.runningSum
              ((env.place self + (offset + 3 + numWords K) : ℕ) : ℤ) := by
      rw [← hsCellVal]; exact hDecomp
    -- the honest s_minus_lo_130 cell (advices[1] @ offset+2) = the child zLast (from the copy)
    have hSMLcell : env.env.toEnvironment.advice cfg.adv1 ((env.place self + (offset + 2) : ℕ) : ℤ)
        = env.env.toEnvironment.advice cfg.lookupConfig.runningSum
            ((env.place self + (offset + 3 + numWords K) : ℕ) : ℤ) := by
      simpa only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex,
        Cell.of_rowOffset, Cell.of_column, Environment.get_advice] using hWsMinusLo
    -- ── `sHi = 0 → zLast = 0` (the only direction the canonicity gate needs) ──
    -- Both `(lo, zLast)` (child) and `(sLo, sHi)` (`Spec`) split the SAME `s = alpha + k254·2^130`
    -- with sub-`2^130` low part; when `sHi = 0` the `Spec` side is `s = sLo < 2^130`.
    have hKey' : (lo : Fp) + (2 ^ 130 : Fp)
          * env.env.toEnvironment.advice cfg.lookupConfig.runningSum
            ((env.place self + (offset + 3 + numWords K) : ℕ) : ℤ)
        = (sLo : Fp) + (2 ^ 130 : Fp) * sHi := by
      rw [← hDecompVal]; exact hkey
    have hCard130 : 2 ^ 130 < PALLAS_BASE_CARD := by
      norm_num [CompElliptic.Fields.Pasta.PALLAS_BASE_CARD]
    -- when `sHi = 0` the canonicity gate needs the child's honest `zLast = 0`. The child `Spec`
    -- alone gives only the FIELD equation `↑lo + 2^130·zLast = ↑sLo` (`lo,sLo < 2^130`), which
    -- does NOT force `zLast = 0` (the split is not field-unique without a high bound). We use the
    -- child's honest NATURAL-NUMBER decomposition `zLast = ↑(s.val / 2^{K·numWords})`, exposed by
    -- the minimal additive child-side lemma `rangeCheck_call_zLast_value` (which reads it off the
    -- loop witnesses, `rangeCheck_loop_zvalues`, that `rangeCheck`'s own `Spec` does not surface).
    -- With `sHi = 0` the honest `Spec` gives `s = ↑sLo` (`sLo < 2^130`), so `s.val < 2^130` and
    -- the shift `s.val / 2^130 = 0`.
    -- `numWords K ≥ 1`: otherwise `K · numWords K = 0 ≠ 130` (from `hKW`)
    have hnwpos : 0 < numWords K := by
      rcases Nat.eq_zero_or_pos (numWords K) with h0 | h; · rw [h0, Nat.mul_zero] at hKW; omega
      exact h
    have hzLast_val := LookupRangeCheck.rangeCheck_call_zLast_value K (numWords K) hnwpos cfg.lookupConfig
      (offset + 3) self env { element := AssignedCell.of self (offset + 1) cfg.adv2 } hWchild
    -- the child's zLast cell = ↑(s.val / 2^{K·numWords}); reduce the `element` cell read to the `s`
    -- cell value `advice adv2@(offset+1)`
    simp only [AssignedCell.eval, AssignedCell.of_cell, Cell.of_regionIndex, Cell.of_rowOffset,
      Cell.of_column, Environment.get_advice] at hzLast_val
    rw [hKW] at hzLast_val
    have hzLast_zero : sHi = 0 → env.env.toEnvironment.advice cfg.lookupConfig.runningSum
        ((env.place self + (offset + 3 + numWords K) : ℕ) : ℤ) = 0 := by
      intro hsHi0
      rw [hzLast_val]
      -- with sHi = 0 the honest Spec pins s = ↑sLo (< 2^130), so s.val < 2^130 and the shift is 0
      have hsVal : (env.env.toEnvironment.advice cfg.adv2 ((env.place self + (offset + 1) : ℕ) : ℤ)).val
          < 2 ^ 130 := by
        have hs_eq : env.env.toEnvironment.advice cfg.adv2 ((env.place self + (offset + 1) : ℕ) : ℤ)
            = (sLo : Fp) := by
          rw [hsCellVal, hkey, hsHi0]; ring
        rw [hs_eq, ZMod.val_natCast_of_lt (lt_trans hsLo_lt hCard130)]; exact hsLo_lt
      rw [Nat.div_eq_of_lt hsVal, Nat.cast_zero]
    -- ── assemble the constraints: 4 gate-window copies ++ child ++ s_minus_lo copy ++ gate.
    -- The pristine `hW*` copy witnesses ARE the copy-equality constraints; the `s`/`η` witness
    -- assigns bear no constraint. ──
    refine ⟨hWk254, hWalpha, hWz0, hWz130, hCchild, hWsMinusLo, ?_⟩
    -- the overflow gate on the honest values (via the copy VALUE facts + the honest `Spec`)
    simp only [overflowGate, Constraints.withSelector, circuit_norm]
    have h2124 : (2 ^ 124 : Fp) = (2 : Fp) ^ 124 := by norm_num
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- s_check: honest s = alpha + k254·2^130
      rw [hsCellVal, ealpha, ek254]; ring
    · -- recovery: z_0 − alpha − t_q = 0
      rw [ez0, ealpha]
      rw [← sub_eq_zero] at hRec; linear_combination hRec
    · -- lo_zero: k254·(z130 − 2^124) = 0
      rw [ek254, ez130]
      rcases hLoZ with h | h
      · rw [h]; ring
      · rw [h, h2124]; ring
    · -- s_minus_lo_130_check: k254·s_minus_lo_130 = 0 (s_minus_lo_130 cell = child zLast)
      rw [ek254, hSMLcell]
      rcases hHiZ with h | h
      · rw [h]; ring
      · rw [hzLast_zero h]; ring
    · -- canonicity: (1 − k254)·(1 − z130·eta)·s_minus_lo_130 = 0, with η = inv0(z130)
      rw [ek254, ez130, hWeta, hSMLcell, hIz130]
      rcases hEtaSpec with h | hz | h
      · rw [h]; ring
      · -- z130 ≠ 0 ⇒ z130·(z130⁻¹) = 1, so (1 − 1) = 0
        rw [mul_inv_cancel₀ hz]; ring
      · rw [hzLast_zero h]; ring

end MulOverflow

end Halo2.Ironwood.Ecc
