import Clean.Halo2
import Clean.Halo2.Subcircuit
import Clean.Orchard.Specs.Pallas
import Clean.Orchard.Ecc.Mul.Complete
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.MulIncomplete

/-!
Reference: `halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul/complete.rs` (read in full),
plus the complete-region call site in `mul.rs:238-256`.

This is variable-base scalar multiplication's *complete* phase: the final `NUM_COMPLETE_BITS = 3`
bits (`COMPLETE_RANGE`), processed with the **complete** group law (which is exceptional-case-free
for all Pallas points). Per bit (`complete.rs:129-190`):

- extend the running sum `z` (`z_next = 2·z_cur + k`), stored in the `z_complete` column;
- conditionally negate the base `y` (`y_p = if k then base_y else −base_y`), checked by the
  `q_mul_decompose_var` "decompose scalar" gate (`complete.rs:46-82`);
- perform **two chained complete additions** via the delegated `add::Config`:
  `tmp = U + acc` at `row + offset`, then `acc' = acc + tmp` at `row + offset + 1`,
  where `U = (base.x, ±base.y)` (the `(acc + U) + acc` double-and-add step).

This is **the first real consumer of the subcircuit-composition machinery** (`Clean/Halo2/
Subcircuit.lean`) and, in particular, the first *loop* consumer: each round invokes the proven
child `Add.add` (`Clean/Ironwood/Ecc/Add.lean`) TWICE via `add.call`, at running offsets. The
value-level round algebra is lifted from the phase-one donor
`Clean/Orchard/Ecc/Mul/Complete.lean` (`Orchard.Ecc.Mul.Complete.AssignRegion`).

## Config composition (first exercise)

`complete::Config` holds the `z_complete` column, its own `q_mul_decompose_var` selector, and
delegates to an `add::Config` (`complete.rs:14-21`). We mirror this: the parent `Config` stores
`addConfig : Add.Config` alongside its own `zComplete` column and `qDecompose` selector. The
child config is threaded down verbatim to `add.call addConfig …`. The parent's
`ConfigInput`/`configure` receives the `add::Config` from the chip assembly (`mul.rs` builds it
once and hands it to both `incomplete` and `complete`), exactly as Rust's
`Config::configure(meta, z_complete, add_config)` takes `add_config` as a parameter.

## Boundary (what belongs here vs. mul.rs assembly)

The `q_mul_decompose_var` decomposition gate is complete.rs's own responsibility and is ported
here. The `q_mul_lsb` "LSB check" gate (`mul.rs:129-160`) handles the *least-significant* bit
`k_0` *after* the complete region and belongs to the mul.rs assembly port — out of scope here.

## Proof status (honest)

Structure-complete. The config/IO plumbing, `configure`, and the `synthesize` round loop are
final. The contract (`Spec`/`Assumptions`/`ProverAssumptions`/`ProverSpec`) mirrors the donor.
The loop lemmas are fully stated with donor lemmas identified and threaded hypotheses worked out;
their proofs — and the two-half bundle proofs — carry `-- TACTIC GAP:` sorries at exactly the
loop-composition points this first consumer exists to surface (see the prominent notes at each
gap). The *value-level* algebra it all routes into is the donor's, proven in full.
-/

namespace Halo2.Ironwood.Ecc.MulComplete

open Orchard (Point)
open Orchard.Ecc.Mul.Incomplete.DoubleAndAdd (zRunValue)
open Halo2.Ironwood.Ecc.MulIncomplete (BitsHint readCell adv)

/-! ## Config

Rust `complete::Config` (`complete.rs:13-21`): the `z_complete` advice column, the
`q_mul_decompose_var` selector, and the delegated `add::Config`. -/

structure Config where
  qDecompose : Selector
  zComplete : Column .advice
  addConfig : Add.Config

/-! ## The `q_mul_decompose_var` gate (`complete.rs:46-82`)

Layout (relative to the round's base row `r`, which is `offset + 2·iter`):

    | y_p        | z_complete |
    ------------------------------
    | y_p (r)    | z_{i+1} (r)      ← Rotation::prev of the selector row
    |            | base_y  (r+1)    ← selector enabled here (Rotation::cur)
    |            | z_i     (r+2)    ← Rotation::next

`k = z_i − 2·z_{i+1}`, `bool_check = k(1−k)`, and `y_switch = ternary(k, base_y − y_p,
base_y + y_p)` (`k=1 ⇒ y_p = base_y`, `k=0 ⇒ y_p = −base_y`). The `y_p` cell read is on the
`add::Config`'s `y_p` column at `Rotation::prev` of the selector row (`complete.rs:68-70`). -/

/-- The `q_mul_decompose_var` gate, a pure function of the columns. Enabled at the middle row
of the three-row window (`base_y` at `Rotation::cur`; `z_{i+1}`, `y_p` at `Rotation::prev`;
`z_i` at `Rotation::next`). -/
def decomposeGate (cfg : Config) : Gate Fp where
  name := "Decompose scalar for complete bits of variable-base mul"
  selector := cfg.qDecompose
  constraints :=
    let zPrev : Expression Fp Query := queryAdvice cfg.zComplete (-1)   -- z_{i+1}
    let zNext : Expression Fp Query := queryAdvice cfg.zComplete 1      -- z_i
    let baseY : Expression Fp Query := queryAdvice cfg.zComplete 0      -- base_y (cur)
    let yP : Expression Fp Query := queryAdvice cfg.addConfig.yP (-1)   -- y_p (prev)
    let k := zNext - (2 : Fp) * zPrev
    let boolCheck := k * (k - (1 : Fp))
    -- ternary(k, base_y − y_p, base_y + y_p) = k·(base_y − y_p) + (1 − k)·(base_y + y_p)
    let ySwitch := k * (baseY - yP) + ((1 : Fp) - k) * (baseY + yP)
    Constraints.withSelector cfg.qDecompose
      [ ("bool_check", boolCheck), ("y_switch", ySwitch) ]

/-- Rust `Config::configure` (`complete.rs:24-40`): enable equality on `z_complete`, allocate the
`q_mul_decompose_var` selector, register the decomposition gate. The `add::Config` is handed down
by the chip assembly (`mul.rs`) — different columns are already equality-enabled by `add`'s own
`configure`, so we only enable equality on `z_complete` here. -/
def configure (zComplete : Column .advice) (addConfig : Add.Config) : Configure Fp Config := do
  enableEquality zComplete.toAny
  let qDecompose ← selector
  let cfg : Config := { qDecompose, zComplete, addConfig }
  createGate (decomposeGate cfg)
  return cfg

/-! ## Inputs / Output

Mirrors the donor `Orchard.Ecc.Mul.Complete.AssignRegion.Input`/`Output`. The base point, the
accumulator cells `(x_a, y_a)` from incomplete addition, and the entering running sum `z` are
verifier-visible; the complete-range bits are a prover hint (like `MulIncomplete`, carried on the
bundle as a fixed `BitsHint`). Output is the final accumulator point and the `numBits`
interstitial running sums. -/

/-- The verifier-visible inputs: base point, entering accumulator `(x_a, y_a)`, entering running
sum `z`, as already-assigned cells. -/
structure Inputs (F : Type) where
  base : Point F
  xA : F
  yA : F
  z : F
deriving ProvableStruct

/-- The output: the final accumulator point and the `numBits` interstitial running sums. -/
structure Output (numBits : ℕ) (F : Type) where
  acc : Point F
  zs : Vector F numBits
deriving ProvableStruct

/-! ## Value-level round algebra (lifted from the donor)

`stepValue`/`accValue` are the donor's, re-exposed here over `Point` so the `Spec` and the loop
invariant read in Ironwood spelling. `stepPointValue b acc = acc + (U_b + acc)` with
`U_b = (base.x, ±base.y)` — exactly the two chained complete additions of one round. -/

/-- The conditionally-negated per-bit point `U = (base.x, if bit then base.y else −base.y)`. -/
def stepBasePoint (base : Point Fp) (bit : Bool) : Point Fp :=
  { x := base.x, y := if bit then base.y else -base.y }

/-- One complete-addition round on `Point`s: `acc + (U + acc)` (`complete.rs:181-189`:
`tmp = U + acc`, `acc' = acc + tmp`). Matches the donor's `accValuePoint` recursion. -/
def stepPoint (base : Point Fp) (acc : Point Fp) (bit : Bool) : Point Fp :=
  acc + (stepBasePoint base bit + acc)

/-- The accumulator after the first `b` complete rounds. -/
def accPoint (base : Point Fp) (acc0 : Point Fp) (bits : BitsHint) : ℕ → Point Fp
  | 0 => acc0
  | b + 1 => stepPoint base (accPoint base acc0 bits b) (bits b)

/-- Validity is preserved by a complete round (the complete group law is total on valid points).
`stepBasePoint` is valid when `base` is (negation preserves validity). -/
theorem accPoint_valid {base acc0 : Point Fp} (hbase : base.Valid) (hacc0 : acc0.Valid)
    (bits : BitsHint) (b : ℕ) : (accPoint base acc0 bits b).Valid := by
  induction b with
  | zero => exact hacc0
  | succ k ih =>
    simp only [accPoint, stepPoint]
    have hU : (stepBasePoint base (bits k)).Valid := by
      simp only [stepBasePoint]
      rcases Bool.dichotomy (bits k) with hb | hb <;> rw [hb]
      · simpa using Orchard.Point.valid_neg hbase
      · simpa using hbase
    exact Orchard.Point.valid_add ih (Orchard.Point.valid_add hU ih)

/-! ## The per-bit round loop, in the `MulIncomplete` recursive shape

Following `Clean/Ironwood/Ecc/MulIncomplete.lean` (itself in the `LookupRangeCheck.rangeCheckLoop`
shape): a structurally recursive `RegionCircuit` over the round count, addressing cells by
*absolute* region-local rows. The loop's `operations` is — by `rfl` from the monad's append-bind —
the concatenation of per-round op lists, and each round's op list contains the round's own ops
plus the TWO folded `add.call` chunks. That concatenation is what the loop induction consumes,
and the composition iffs (`FormalRegionCircuit.subcircuit_constraints_iff_soundness'/…'`) fire on
each round's two child chunks.

Row layout (relative to the ambient `offset`, faithful to Rust `assign_region`):
- row `offset`               : the `z` copy from incomplete addition (`complete.rs:115-123`).
- round `iter` base row `r := offset + 2·iter`:
  - `z_i` assigned at `r + 2` (`complete.rs:140-147`);
  - `base_y` copied to `z_complete` at `r + 1`, `q_mul_decompose_var` enabled at `r + 1`
    (`complete.rs:108`, `152-157`);
  - `y_p` assigned to `add.yP` at `r` (`complete.rs:175`);
  - two `add.call`s: `U + acc` at `r`, `acc + tmp` at `r + 1`. -/

/-- The witness-IR value of the conditionally-negated `y_p` at round `iter` (`complete.rs:160-165`:
`if k then base_y else −base_y`). The bit is read from the prover hint. -/
def yPWit (input : Inputs (AssignedCell Fp)) (bits : BitsHint) (iter : ℕ) : WitgenIR Fp 1 :=
  .native fun env => #v[if bits iter then readCell env input.base.y else -(readCell env input.base.y)]

/-- The witness-IR value of the running-sum cell `z_i` at round `iter` (`complete.rs:141-145`:
`z_next = 2·z_cur + k`). Reads the entering `z` and folds `iter` steps. -/
def zWit (input : Inputs (AssignedCell Fp)) (bits : BitsHint) (iter : ℕ) : WitgenIR Fp 1 :=
  .native fun env => #v[zRunValue (readCell env input.z) bits (iter + 1)]

/-- One complete-addition round at loop index `iter`, at absolute rows relative to `offset`. The
base row is `r = offset + 2·iter`. Emits: the running-sum cell `z_i` (at `r + 2`), the base_y copy
(at `r + 1`) and the `q_mul_decompose_var` enable (at `r + 1`), the conditionally-negated `y_p`
(at `r`, on `add.yP`), and the TWO `add.call`s — `U + acc` at offset `r`, `acc' = acc + tmp` at
offset `r + 1`. Returns the round's output accumulator cells (the second `add`'s output point).

The accumulator flows through the return value: `acc` is the previous round's output point (cells).
The first round's `acc` is the entering `(input.xA, input.yA)`; `cellAt`-style naming is not needed
because the child `add.call` returns the fresh R cells directly. -/
def round (cfg : Config) (input : Inputs (AssignedCell Fp)) (bits : BitsHint)
    (offset iter : ℕ) (acc : Point (AssignedCell Fp)) :
    RegionCircuit Fp (Point (AssignedCell Fp)) := do
  let r := offset + 2 * iter
  -- running-sum cell z_i at r + 2
  let _z ← assignAdvice cfg.zComplete (r + 2) (zWit input bits iter)
  -- base_y copied into z_complete at r + 1 (for the decomposition gate's `base_y` read)
  let _baseY ← copyAdvice input.base.y cfg.zComplete (r + 1)
  -- conditionally-negated y_p, assigned on add.yP at r
  let yP ← assignAdvice cfg.addConfig.yP r (yPWit input bits iter)
  -- the q_mul_decompose_var gate at the middle row r + 1 (`complete.rs:108`)
  (decomposeGate cfg).enable (r + 1)
  -- U = (base.x, y_p)
  let U : Point (AssignedCell Fp) := { x := input.base.x, y := yP }
  -- tmp = U + acc, at add-offset r
  let tmp ← Add.add.call cfg.addConfig r ⟨U, acc⟩
  -- acc' = acc + tmp, at add-offset r + 1
  let acc' ← Add.add.call cfg.addConfig (r + 1) ⟨acc, tmp⟩
  return acc'

/-- The complete-addition loop: `numRounds` rounds, structurally recursive, threading the
accumulator point through. By the append-bind of `RegionCircuit`,
`(loop … (k+1)).operations self = (loop … k).operations self ++ (round … k accₖ).operations self`
— the per-round decomposition the induction consumes. The return value is the final accumulator. -/
def loop (cfg : Config) (input : Inputs (AssignedCell Fp)) (bits : BitsHint) (offset : ℕ) :
    ℕ → RegionCircuit Fp (Point (AssignedCell Fp))
  | 0 => pure { x := input.xA, y := input.yA }
  | k + 1 => do
    let acc ← loop cfg input bits offset k
    round cfg input bits offset k acc

/-- Name a whole vector of `z` cells at fixed region-local rows, emitting no op — the running-sum
`Output.zs` cells. (`MulIncomplete.cellVec`, inlined; the round-`iter` `z_i` cell is at
`offset + 2·iter + 2`.) -/
def zsCells (cfg : Config) (offset : ℕ) (numBits : ℕ) :
    RegionCircuit Fp (Vector (AssignedCell Fp) numBits) :=
  fun self => (Vector.ofFn (fun i => AssignedCell.of self (offset + 2 * i.val + 2) cfg.zComplete), [])

@[circuit_norm]
theorem operations_zsCells (cfg : Config) (offset numBits : ℕ) (self : RegionIndex) :
    (zsCells cfg offset numBits).operations self = [] := rfl

@[circuit_norm]
theorem output_zsCells (cfg : Config) (offset numBits : ℕ) (self : RegionIndex) :
    (zsCells cfg offset numBits).output self
      = Vector.ofFn (fun i => AssignedCell.of self (offset + 2 * i.val + 2) cfg.zComplete) := rfl

/-- Per-round operations decomposition (holds by `rfl` via the monad's `operations_bind`), the
crux that makes the loop inductable. Mirrors `MulIncomplete.loop_operations_succ`, but note the
accumulator threads through the *value* of the previous loop stage, so the round's ops depend on
`(loop … k).output self`. -/
theorem loop_operations_succ (cfg : Config) (input : Inputs (AssignedCell Fp)) (bits : BitsHint)
    (offset k : ℕ) (self : RegionIndex) :
    (loop cfg input bits offset (k + 1)).operations self
      = (loop cfg input bits offset k).operations self
        ++ (round cfg input bits offset k ((loop cfg input bits offset k).output self)).operations self := by
  simp only [loop, RegionCircuit.operations_bind]

theorem loop_output_succ (cfg : Config) (input : Inputs (AssignedCell Fp)) (bits : BitsHint)
    (offset k : ℕ) (self : RegionIndex) :
    (loop cfg input bits offset (k + 1)).output self
      = (round cfg input bits offset k ((loop cfg input bits offset k).output self)).output self := by
  simp only [loop, RegionCircuit.output_bind]

/-! ## Per-round composition lemma (the research artifact)

`round_acc_sound` is the concrete demonstration that the absorption-iff pattern holds inside a
round that makes TWO chained child calls with the output→next-precondition threading. It is the
per-round core that the loop induction (soundness `sorry`, above) invokes. Stated over a round at
a fixed `iter`, given the entering accumulator's coordinates as a *valid* point, it consumes both
`add.call` chunks and concludes the round's output cells are the complete `stepPoint`.

Proof deferred with a `-- TACTIC GAP` note: firing the iff twice in one round and threading the
first add's `output.Valid` into the second add's `q.Valid` precondition is exactly the ergonomics
this consumer surfaces. -/

/-- One round's soundness, in the composition-iff shape. If the round's constraints hold, the
entering accumulator `acc` reads a valid point `A`, and the base is valid, then the round's output
point equals `stepPoint base A (bits iter)` and is valid — via the two `add.call` chunks. -/
theorem round_acc_sound (cfg : Config) (input : Inputs (AssignedCell Fp)) (bits : BitsHint)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset iter : ℕ)
    (acc : Point (AssignedCell Fp)) (A base : Point Fp)
    (hAvalid : A.Valid) (hbase : base.Valid)
    (hAcc : eval (⟨place, env⟩ : Placed Environment Fp) acc = A)
    (hBaseX : eval (⟨place, env⟩ : Placed Environment Fp) input.base.x = base.x)
    (hBaseY : eval (⟨place, env⟩ : Placed Environment Fp) input.base.y = base.y)
    (hC : RegionOperations.Constraints place self env
      ((round cfg input bits offset iter acc).operations self)) :
    eval (⟨place, env⟩ : Placed Environment Fp)
        ((round cfg input bits offset iter acc).output self) = stepPoint base A (bits iter)
      ∧ (stepPoint base A (bits iter)).Valid := by
  simp only [round, circuit_norm,
    RegionCircuit.operations_bind, RegionCircuit.output_bind,
    operations_assignAdvice, operations_copyAdvice, operations_enable,
    RegionOperations.constraints_append] at hC ⊢
  obtain ⟨hz, hdec, hC1, hC2⟩ := hC
  rw [FormalRegionCircuit.subcircuit_constraints_iff_soundness
        Add.add cfg.addConfig (offset + 2 * iter) self ⟨place, env⟩
        ⟨{ x := input.base.x, y := AssignedCell.of self (offset + 2 * iter) cfg.addConfig.yP }, acc⟩] at hC1
  rw [FormalRegionCircuit.subcircuit_constraints_iff_soundness
        Add.add cfg.addConfig (offset + 2 * iter + 1) self ⟨place, env⟩
        ⟨acc, (Add.add.call cfg.addConfig (offset + 2 * iter)
          ⟨{ x := input.base.x, y := AssignedCell.of self (offset + 2 * iter) cfg.addConfig.yP }, acc⟩).output self⟩] at hC2
  obtain ⟨_, hSpec1⟩ := hC1
  obtain ⟨_, hSpec2⟩ := hC2
  -- `hSpec1 : EnvAssumptions → Assumptions → Spec` for the FIRST add (`U + acc`), and `hSpec2`
  -- likewise for the SECOND (`acc + tmp`) — both are record projections of `Add.add` (Spec =
  -- `out.Valid ∧ out = p + q`; Assumptions = `p.Valid ∧ q.Valid`; EnvAssumptions = `True`).
  --
  -- Remaining (fully-stated) work, all routing into the donor's proven algebra:
  --  (a) `hEvalU`: eval of the first add's input is `⟨stepBasePoint base (bits iter), A⟩`. Its `p.y`
  --      is the assigned `y_p` cell, which the decomposition gate `hdec` pins to `±base.y` — this
  --      is the donor's `bit_facts` bridge (`Orchard.Ecc.Mul.Complete.AssignRegion.bit_facts`).
  --  (b) `hU.Valid`: from `hbase` via `accPoint_valid`'s one-step `stepBasePoint` validity.
  --  (c) discharge `hSpec1 trivial ⟨hU.Valid, hAvalid⟩ → tmp.Valid ∧ tmp = U + A`.
  --  (d) discharge `hSpec2 trivial ⟨hAvalid, tmp.Valid⟩ → acc' .Valid ∧ acc' = A + tmp`
  --      — the FIRST add's `tmp.Valid` (from (c)) is the SECOND's `q.Valid` precondition: the
  --      output→next-precondition thread the absorption iff gives round-internally.
  --  (e) fold `acc' = A + (U + A) = stepPoint base A (bits iter)` (defeq of `stepPoint`).
  -- TACTIC GAP: steps (a)/(c)/(d) each need the eval-componentwise landing + the projection
  -- unfolding of `Add.add.Spec`/`Assumptions` in a form `simp` can consume; not yet a tactic.
  -- KEY FINDING: the *primed* iff `…_soundness'` does NOT fire under `simp only [circuit_norm, …']`
  -- in a loop lemma stated over bare `place, env` — its discr-tree key is `env.place`/`env.env`
  -- (a `Placed` projection), unmatched by bare `place`/`env`. Only the *generic* iff via explicit
  -- `rw [FormalRegionCircuit.subcircuit_constraints_iff_soundness Add.add cfg.addConfig off self
  -- ⟨place,env⟩ …]` matches (full `isDefEq`, repackaging `⟨place, env⟩`). The straight-line PoC
  -- (`TestSubcircuit`) has a genuine `Placed` env so its primed simp-form fires; a loop consumer
  -- must `rw` the generic iff with ALL arguments supplied per call — the composition friction.
  sorry

/-! ## The bundle contract

`Spec` exposes the complete-rounds invariant, mirroring the donor
`Orchard.Ecc.Mul.Complete.AssignRegion.Spec`: the running-sum chain, and — for valid entering
accumulator and base — the output accumulator is `accValue`/`accPoint` after `numBits` rounds. -/

/-- The complete-rounds invariant: the running-sum chain over `numBits` bits, and (for valid
inputs) the output accumulator equals `accPoint … numBits`, valid throughout. Mirrors the donor's
`Spec`. -/
def RoundInvariant (numBits : ℕ) (input : Inputs Fp) (output : Output numBits Fp)
    (bits : BitsHint) : Prop :=
  let base : Point Fp := input.base
  let acc0 : Point Fp := { x := input.xA, y := input.yA }
  (∀ b : Fin numBits, output.zs[b.val]
      = 2 * (if b.val = 0 then input.z else output.zs[b.val - 1]'(by have := b.isLt; omega))
        + (if bits b.val then 1 else 0)) ∧
  (acc0.Valid → base.Valid →
    output.acc.Valid ∧ output.acc = accPoint base acc0 bits numBits)

/-! ## The gadget bundle

`complete::Config::assign_region` (`complete.rs:87-192`) over `COMPLETE_RANGE.len() =
NUM_COMPLETE_BITS = 3` bits, generalized to `numBits`. Parameterized by the prover bit sequence
`bits`; the verifier-facing `Spec` existentially quantifies a matching sequence. -/

/-- The `z` copy emitted before the loop (`complete.rs:115-123`): the entering running sum into
`cfg.zComplete` at `offset`. -/
def startCopy (cfg : Config) (input : Inputs (AssignedCell Fp)) (offset : ℕ) :
    RegionCircuit Fp Unit := do
  let _z ← copyAdvice input.z cfg.zComplete offset
  return ()

def assign_region (numBits : ℕ) (bits : BitsHint) :
    FormalRegionCircuit Fp (Column .advice × Add.Config) Config Inputs (Output numBits) where
  configure := fun (zComplete, addConfig) => configure zComplete addConfig

  synthesize cfg offset (input : Inputs (AssignedCell Fp)) := do
    -- copy the entering running sum
    startCopy cfg input offset
    -- the per-bit round loop; the final accumulator is the loop's return value
    let accFinal ← loop cfg input bits offset numBits
    -- name the running-sum output cells (at fixed absolute rows)
    let zsOut ← zsCells cfg offset numBits
    return { acc := accFinal, zs := zsOut }

  -- the base point is a valid Pallas point (complete addition is exceptional-case-free).
  Assumptions input :=
    let base : Point Fp := input.base
    let acc0 : Point Fp := { x := input.xA, y := input.yA }
    acc0.Valid ∧ base.Valid

  Spec input output _ :=
    ∃ bits' : BitsHint, RoundInvariant numBits input output bits'

  ProverAssumptions input _ :=
    let base : Point Fp := input.base
    let acc0 : Point Fp := { x := input.xA, y := input.yA }
    acc0.Valid ∧ base.Valid

  ProverSpec input output _ := RoundInvariant numBits input output bits

  -- ══ Soundness ══
  soundness := by
    intro cfg offset
    rw [FormalRegionCircuit.soundness_iff]
    intro self env input_var input output h_input h_output _hE hA hc
    -- TACTIC GAP (composition, loop): peel `startCopy ++ loop ++ zsCells` via
    -- `RegionOperations.constraints_append`; then induct over the loop, and at EACH round consume
    -- its TWO folded `add.call` chunks with
    --   `simp only [circuit_norm, FormalRegionCircuit.subcircuit_constraints_iff_soundness'] at …`
    -- feeding each `add`'s Spec (`output.Valid ∧ output = p + q`) forward: the FIRST add's output
    -- Valid becomes the SECOND add's `q.Valid` precondition, and the round's output Valid becomes
    -- the NEXT round's acc Valid. This "output.Valid feeds next call's Assumptions" chain is
    -- exactly the absorption iff round by round. See `round_sound` below for the per-round shape.
    sorry

  -- ══ Completeness ══
  completeness := by
    intro cfg offset
    rw [FormalRegionCircuit.completeness_iff]
    intro self env input_var input output h_input h_output hwit _hE hA hPA
    -- TACTIC GAP (composition, loop): mirror soundness. Split the witness/constraint op lists;
    -- induct over the loop; at each round rewrite the TWO `add.call` GOAL chunks via
    --   `simp only [circuit_norm, FormalRegionCircuit.subcircuit_constraints_iff_completeness']`
    -- and pick `Or.inr ⟨hwit_call, trivial, trivial, precondition⟩` for each — the child's
    -- `Assumptions` (both addends Valid) discharged from the honest accumulator chain.
    sorry

end Halo2.Ironwood.Ecc.MulComplete
