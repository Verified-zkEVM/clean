import Clean.Halo2
import Clean.Orchard.Specs.Pallas
import Clean.Ironwood.Ecc.Basic
import Clean.Orchard.Ecc.DoubleAndAdd
import Clean.Orchard.Ecc.Mul.Incomplete

/-!
Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul/incomplete.rs` (read in full),
plus the `hi_config`/`lo_config` instantiation in `mul.rs`.

This is variable-base scalar multiplication's *incomplete* phase: for each scalar bit, one
double-and-add round with the `x_a / x_p / λ₁ / λ₂` column layout, the `q_mul` selectors at
three rotations (`q_mul_1` on the first row, `q_mul_2` on the interior, `q_mul_3` on the last),
a running `z` column (`z_i = 2·z_{i+1} + k_i`), and the round relation
`acc_{i+1} = (acc_i + (2k−1)P) + acc_i` (two incomplete additions merged into the specialized
round gate `Y_A = (λ₁+λ₂)(x_A − x_R)`).

The `hi` and `lo` halves of `mul.rs` are two instantiations of the *same* `incomplete::Config`
structure, differing only in the advice columns handed to `configure` (`mul.rs:71-76`) and in
the bit-count `NUM_BITS` (`INCOMPLETE_HI_LEN = 125`, `INCOMPLETE_LO_LEN = 126`). We port the
structure once, generic over the bit count `n + 1` (Rust `NUM_BITS`), exactly as the phase-one
donor `Clean/Orchard/Ecc/Mul/Incomplete.lean` (namespace `Orchard.Ecc.Mul.Incomplete`) does.

## Donor reuse

The value-level algebra is *pure* `Fp`/`Point` mathematics, framework-agnostic, and is proven
in full by the phase-one donor. We import and reuse it wholesale:

- `Orchard.Ecc.Mul.Incomplete.DoubleAndAdd.accScalar` — the accumulated multiplier recursion
  `m_{b+1} = 2 m_b + 2 k_b − 1` (each round is `([m]P ⸭ (2k−1)P) ⸭ [m]P = [2m+2k−1]P`).
- `…DoubleAndAdd.zRunValue` — the running sum `z_b = 2 z_{b−1} + k_b`.
- `…DoubleAndAdd.stepPoint` / `step_nsmul` — the per-bit conditionally-negated point and the
  non-degenerate double-and-add step lemma.
- `…DoubleAndAdd.accVal` / `lambdaCellsValue` / `rowLambdaValue` — the honest witness values.
- `…DoubleAndAdd.soundness_aux` / `honest_step` / `accVal_eq_nsmul` — the chain inductions.
- `Orchard.Ecc.DoubleAndAdd.{xR, yA, coordinates_of_constraints}` — the derived row formulas
  and the "constraints ⇒ output coordinates" bridge.

Only the *framework wiring* is new here: the `Config`/gates/`configure`, the `synthesize` loop
in the `LookupRangeCheck.rangeCheckLoop` shape (structurally recursive `RegionCircuit`, absolute
rows, per-round `rfl`-decomposable operations), and the `FormalRegionCircuit` bundle whose
soundness/completeness route the cleaned row facts into the donor's chain inductions.

## Contract

This is a *fragment* of mul (parents: `mul.rs`). Its `Spec` exposes the round invariant: after
`n + 1` rounds from accumulator `A = [m]P` with on-curve base `P` and bits `b`, the running-sum
relation `z_i = 2 z_{i+1} + k_i` holds and the output accumulator equals the double-and-add
result `[accScalar m b (n+1)] • P`. The incomplete-addition preconditions (`P` on-curve
non-identity, `A = [m]P` a small positive multiple with `2 ≤ m` and `2^{n+2}(m+1) ≤ 2^{254}`,
so no exceptional case arises across the whole run) are exactly the donor's `Assumptions` /
`ProverAssumptions`, ported faithfully.
-/

namespace Halo2.Ironwood.Ecc.MulIncomplete

open Orchard (Point)
open Orchard.Ecc (DoubleAndAddRow)
open Orchard.Ecc.Mul.Incomplete.DoubleAndAdd
  (accScalar zRunValue stepPoint accVal lambdaCellsValue rowLambdaValue)

/-! ## Config

Rust `incomplete::Config<NUM_BITS>` (`incomplete.rs:58-72`), flattened: the three `q_mul`
selectors, the running-sum column `z`, the four `DoubleAndAdd` columns (`x_a, x_p, λ₁, λ₂`),
and the point's `y_p`. `NUM_BITS` is not a config field in Rust (it is a const generic); we
carry it as the parameter `n` (bit count `n + 1`) on the *bundle*, not the `Config`. -/

structure Config where
  qMul1 : Selector
  qMul2 : Selector
  qMul3 : Selector
  z : Column .advice
  xA : Column .advice
  xP : Column .advice
  yP : Column .advice
  lambda1 : Column .advice
  lambda2 : Column .advice

/-! ## Gates as standalone defs, polynomials verbatim at the Rust rotations

Both `DoubleAndAdd::x_r` and `Y_A` are pure functions of the columns at a rotation
(`incomplete.rs:29-55`). We inline them here as `Expression` builders. Note `Y_A` in Rust is
`(λ₁ + λ₂)(x_a − x_r)` *without* the `1/2` factor — the caller (`create_gate`) multiplies by
`TWO_INV`. We keep the polynomials exactly as the compiled gate builds them: each `y_a` term
carries the `pallas::Base::TWO_INV` scalar. To stay in a `ring`-friendly shape we clear the
`1/2` by multiplying the two gradient constraints through by `2` — this is the same
normalization the donor's `Loop.gradient1/gradient2` use (`Incomplete.lean:51-61`). -/

/-- `x_{R} = λ₁² − x_A − x_P` at `rotation` (`DoubleAndAdd::x_r`). -/
def xRExpr (cfg : Config) (rot : Rotation) : Expression Fp Query :=
  let xA : Expression Fp Query := queryAdvice cfg.xA rot
  let xP : Expression Fp Query := queryAdvice cfg.xP rot
  let l1 : Expression Fp Query := queryAdvice cfg.lambda1 rot
  l1 * l1 - xA - xP

/-- `Y_A = (λ₁ + λ₂)(x_A − x_R)` at `rotation`, *without* the `1/2` (Rust `Y_A`). The compiled
gate multiplies this by `TWO_INV`; the round gate below clears the halving by scaling the whole
gradient constraint by `2`, so `y_a` appears as this expression. -/
def yAExpr (cfg : Config) (rot : Rotation) : Expression Fp Query :=
  let xA : Expression Fp Query := queryAdvice cfg.xA rot
  let l1 : Expression Fp Query := queryAdvice cfg.lambda1 rot
  let l2 : Expression Fp Query := queryAdvice cfg.lambda2 rot
  (l1 + l2) * (xA - xRExpr cfg rot)

/-- The shared "for-loop" body of the `q_mul_{2,3}` gates (`incomplete.rs:121-169`), scaled to
clear the `1/2` in `y_a`: booleanity of the bit `k = z_cur − 2·z_prev`, `gradient_1`,
`secant_line`, `gradient_2`. `yANext` is the caller-supplied next-row `Y_A` (for `q_mul_2` it is
`y_a(next)`; for `q_mul_3` it is the witnessed doubled final `y`). Written as a list of
`(name, poly)` with each polynomial in the `2·(…)` normal form of the donor. -/
def forLoopPolys (cfg : Config) (yANextDouble : Expression Fp Query) :
    List (String × Expression Fp Query) :=
  let zCur : Expression Fp Query := queryAdvice cfg.z 0
  let zPrev : Expression Fp Query := queryAdvice cfg.z (-1)
  let xACur : Expression Fp Query := queryAdvice cfg.xA 0
  let xANext : Expression Fp Query := queryAdvice cfg.xA 1
  let xPCur : Expression Fp Query := queryAdvice cfg.xP 0
  let yPCur : Expression Fp Query := queryAdvice cfg.yP 0
  let l1 : Expression Fp Query := queryAdvice cfg.lambda1 0
  let l2 : Expression Fp Query := queryAdvice cfg.lambda2 0
  -- k = z_cur − 2·z_prev
  let k : Expression Fp Query := zCur - zPrev * (2 : Fp)
  let boolCheck := k * (k - (1 : Fp))
  -- 2·λ₁·(x_A − x_P) − 2·y_A + 2·(2k−1)·y_P  (donor `gradient1`, ×2 form)
  let gradient1 :=
    (2 : Fp) * l1 * (xACur - xPCur) - yAExpr cfg 0
      + (2 : Fp) * ((k * (2 : Fp) - (1 : Fp)) * yPCur)
  -- λ₂² − x_{A,next} − x_R − x_A  (donor `secantLine`)
  let secantLine := l2 * l2 - xANext - xRExpr cfg 0 - xACur
  -- 2·λ₂·(x_A − x_{A,next}) − 2·y_A − yANextDouble  (donor `gradient2`, ×2 form)
  let gradient2 := (2 : Fp) * l2 * (xACur - xANext) - yAExpr cfg 0 - yANextDouble
  [ ("bool_check", boolCheck),
    ("gradient_1", gradient1),
    ("secant_line", secantLine),
    ("gradient_2", gradient2) ]

/-- The `q_mul_1 == 1` gate (`incomplete.rs:173-179`): the copied `y_a` (in the `λ₁` column at
the current row) equals the derived `y_a` of the next row. In `2·` form: `2·y_a_witnessed =
Y_A(next)`. -/
def qMul1Gate (cfg : Config) : Gate Fp where
  name := "q_mul_1 == 1 checks"
  selector := cfg.qMul1
  constraints :=
    let yAWitnessed : Expression Fp Query := queryAdvice cfg.lambda1 0
    Constraints.withSelector cfg.qMul1
      [("init y_a", (2 : Fp) * yAWitnessed - yAExpr cfg 1)]

/-- The `q_mul_2 == 1` gate (`incomplete.rs:183-209`): base-constancy checks `x_p`/`y_p` are the
same on the next row, plus the shared for-loop body with `yANextDouble = Y_A(next)`. -/
def qMul2Gate (cfg : Config) : Gate Fp where
  name := "q_mul_2 == 1 checks"
  selector := cfg.qMul2
  constraints :=
    let xPCur : Expression Fp Query := queryAdvice cfg.xP 0
    let xPNext : Expression Fp Query := queryAdvice cfg.xP 1
    let yPCur : Expression Fp Query := queryAdvice cfg.yP 0
    let yPNext : Expression Fp Query := queryAdvice cfg.yP 1
    Constraints.withSelector cfg.qMul2
      ([ ("x_p_check", xPCur - xPNext),
         ("y_p_check", yPCur - yPNext) ]
        ++ forLoopPolys cfg (yAExpr cfg 1))

/-- The `q_mul_3 == 1` gate (`incomplete.rs:213-217`): the for-loop body on the last row, with
`yANextDouble = 2·y_a_final` (the witnessed final `y` in the `λ₁` column at the next row). -/
def qMul3Gate (cfg : Config) : Gate Fp where
  name := "q_mul_3 == 1 checks"
  selector := cfg.qMul3
  constraints :=
    let yAFinal : Expression Fp Query := queryAdvice cfg.lambda1 1
    Constraints.withSelector cfg.qMul3
      (forLoopPolys cfg ((2 : Fp) * yAFinal))

/-- Rust `Config::configure` (`incomplete.rs:75-104`): enable equality on `z` and `λ₁`, allocate
the three simple selectors, register the three gates. The columns are handed down by `mul.rs`
(different for `hi`/`lo`). -/
def configure (z xA xP yP lambda1 lambda2 : Column .advice) : Configure Fp Config := do
  enableEquality z.toAny
  enableEquality lambda1.toAny
  let qMul1 ← selector
  let qMul2 ← selector
  let qMul3 ← selector
  let cfg : Config := { qMul1, qMul2, qMul3, z, xA, xP, yP, lambda1, lambda2 }
  createGate (qMul1Gate cfg)
  createGate (qMul2Gate cfg)
  createGate (qMul3Gate cfg)
  return cfg

/-! ## Inputs / Output

Mirrors the donor `DoubleAndAdd.Input`/`Output`. The base point and the accumulator cells are
verifier-visible; the scalar bits are a prover-side `Value<bool>` sequence (`Unconstrained`
native hint). The output is the final accumulator cells and all interstitial running sums. -/

/-- Prover-side scalar bits, MSB-first, indexed from the first processed bit — the Ironwood
alias of the donor's `BitsHint`. -/
def BitsHint : Type := ℕ → Bool

instance : Inhabited BitsHint := ⟨fun _ => false⟩

/-- The verifier-visible inputs: the (non-identity, on-curve) base point and the accumulator
`(x_a, y_a)` and running sum `z` entering the phase, as already-assigned cells. The scalar bits
are supplied separately as a prover hint (see the bundle's `ProverAssumptions`/`ProverSpec`,
which quantify over a bit sequence). -/
structure Inputs (F : Type) where
  base : Point F
  xA : F
  yA : F
  z : F
deriving ProvableStruct

/-- The output: the final accumulator cells `(x_a, y_a)` and the `n + 1` interstitial running
sums. -/
structure Output (numBits : ℕ) (F : Type) where
  xA : F
  yA : F
  zs : Vector F numBits
deriving ProvableStruct

/-! ## Honest witness programs

The honest cell values are complex functions of the base/accumulator cells and the prover bits,
so — like the donor's `witnessNative` — we express them via the witgen `native` escape hatch
(`WitgenIROver.native`), reading the placed prover environment. Each returns a length-1 vector.

`readCell env c` reads the value of an already-assigned input cell `c` in the placed prover
environment `env` — the base coordinates and starting accumulator that the honest values depend
on. -/

/-- Read an input cell's value in a placed prover environment. -/
def readCell (env : Placed ProverEnvironment Fp) (c : AssignedCell Fp) : Fp :=
  c.eval env.place env.env.toEnvironment

/-- Honest `z` running-sum value at loop row `r` (`incomplete.rs:302-306`). -/
def zWit (input : Inputs (AssignedCell Fp)) (bits : BitsHint) (r : ℕ) : WitgenIR Fp 1 :=
  .native fun env => #v[zRunValue (readCell env input.z) bits r]

/-- Honest `λ₁` value at loop row `r`. -/
def l1Wit (input : Inputs (AssignedCell Fp)) (bits : BitsHint) (r : ℕ) : WitgenIR Fp 1 :=
  .native fun env => #v[
    (rowLambdaValue (readCell env input.base.x) (readCell env input.base.y)
      (readCell env input.xA) (readCell env input.yA) bits r).lambda1]

/-- Honest `λ₂` value at loop row `r`. -/
def l2Wit (input : Inputs (AssignedCell Fp)) (bits : BitsHint) (r : ℕ) : WitgenIR Fp 1 :=
  .native fun env => #v[
    (rowLambdaValue (readCell env input.base.x) (readCell env input.base.y)
      (readCell env input.xA) (readCell env input.yA) bits r).lambda2]

/-- Honest next-row `x_a` value after loop row `r` (`accVal … (r+1)`). -/
def xANextWit (input : Inputs (AssignedCell Fp)) (bits : BitsHint) (r : ℕ) : WitgenIR Fp 1 :=
  .native fun env => #v[
    (accVal (readCell env input.base.x) (readCell env input.base.y)
      (readCell env input.xA) (readCell env input.yA) bits (r + 1)).1]

/-- Honest final `y_a` value after `n + 1` rounds (`accVal … (n+1)`). -/
def yAFinalWit (n : ℕ) (input : Inputs (AssignedCell Fp)) (bits : BitsHint) : WitgenIR Fp 1 :=
  .native fun env => #v[
    (accVal (readCell env input.base.x) (readCell env input.base.y)
      (readCell env input.xA) (readCell env input.yA) bits (n + 1)).2]

/-! ## The per-bit round loop, in the `rangeCheckLoop` shape

Following `Clean/Ironwood/Utilities/LookupRangeCheck.lean`: a structurally recursive
`RegionCircuit` over the round count, addressing cells by *absolute* region-local rows (not
threaded through the monad), so the loop's `operations` is — by `rfl` from the monad's
append-bind — the concatenation of per-round op lists. That append shape is what lets the
z-chain / accumulator invariant be proven by induction over rounds.

Row layout (relative to the ambient `offset`, faithful to Rust `double_and_add`,
`incomplete.rs:255-397`):
- row `offset`      : starting `z` copy (`z` col) and starting `y_a` copy (`λ₁` col).
- row `offset + 1`  : starting `x_a` copy (`x_a` col); loop row 0 begins here.
- loop row `r` (`0 ≤ r ≤ n`) at absolute row `offset + 1 + r`: assign `z, x_p, y_p, λ₁, λ₂`
  and the next-row `x_a` at `offset + 1 + r + 1`.
- row `offset + 1 + (n + 1)` : the witnessed final `y_a` (`λ₁` col).

Selectors: `q_mul_1` at `offset`; `q_mul_2` at `offset + 1 .. offset + n`; `q_mul_3` at
`offset + 1 + n`. -/

/-- One double-and-add round at loop index `r`, at absolute rows relative to `offset`. Assigns
the five per-row cells and the next-row `x_a`, and enables the round's selector. The first loop
row (`r = 0`) additionally anchors `x_p`/`y_p` to `base` by copy — the `CircuitVersion::
AnchoredBase` variant (`incomplete.rs:317-337`); the `q_mul_2` constancy then propagates the
anchor. Cells are at fixed absolute rows so round `r` is independent of the others — the
concatenation property the loop induction consumes. -/
def round (cfg : Config) (input : Inputs (AssignedCell Fp)) (bits : BitsHint)
    (offset r : ℕ) : RegionCircuit Fp Unit := do
  let row := offset + 1 + r
  let _z ← assignAdvice cfg.z row (zWit input bits r)
  -- x_p / y_p: anchored copy of `base` on the first loop row, plain assignment otherwise
  if r = 0 then
    let _xP ← copyAdvice input.base.x cfg.xP row
    let _yP ← copyAdvice input.base.y cfg.yP row
  else
    let _xP ← assignAdvice cfg.xP row (.ofFExpr (.expr input.base.x))
    let _yP ← assignAdvice cfg.yP row (.ofFExpr (.expr input.base.y))
  let _l1 ← assignAdvice cfg.lambda1 row (l1Wit input bits r)
  let _l2 ← assignAdvice cfg.lambda2 row (l2Wit input bits r)
  let _xANext ← assignAdvice cfg.xA (row + 1) (xANextWit input bits r)
  return ()

/-- The double-and-add loop: `numRounds` rounds, structurally recursive. By the append-bind of
`RegionCircuit`, `(loop … (k+1)).operations self = (loop … k).operations self ++
(round … k).operations self` — the per-round decomposition the induction consumes. -/
def loop (cfg : Config) (input : Inputs (AssignedCell Fp)) (bits : BitsHint) (offset : ℕ) :
    ℕ → RegionCircuit Fp Unit
  | 0 => pure ()
  | k + 1 => do
    loop cfg input bits offset k
    round cfg input bits offset k

/-- Per-round operations decomposition (holds by `rfl` via the monad's `operations_bind`): the
crux that makes the loop inductable. Mirrors `rangeCheckLoop_operations_succ`. -/
theorem loop_operations_succ (cfg : Config) (input : Inputs (AssignedCell Fp)) (bits : BitsHint)
    (offset k : ℕ) (self : RegionIndex) :
    (loop cfg input bits offset (k + 1)).operations self
      = (loop cfg input bits offset k).operations self
        ++ (round cfg input bits offset k).operations self := rfl

/-- Read the assigned cell at a known region-local row/column (no op emitted) — lets `synthesize`
name the running-sum and accumulator cells for the `Output`, which live at fixed rows rather
than being threaded through the loop's return value. (`LookupRangeCheck.cellAt`.) -/
def cellAt (col : Column .advice) (row : ℕ) : RegionCircuit Fp (AssignedCell Fp) :=
  fun self => (.of self row col, [])

@[circuit_norm]
theorem operations_cellAt (col : Column .advice) (row : ℕ) (self : RegionIndex) :
    (cellAt col row).operations self = [] := rfl

@[circuit_norm]
theorem output_cellAt (col : Column .advice) (row : ℕ) (self : RegionIndex) :
    (cellAt col row).output self = .of self row col := rfl

/-! ## Loop-shaped standalone lemmas

The z-chain and accumulator invariants, proven by induction over rounds using the per-round
operations decomposition (`loop_operations_succ`) and the append splitting of
`RegionOperations.Constraints`/`ExtendsWitnesses`. This is the loop-shaped proof structure of
`LookupRangeCheck.rangeCheck_loop_word_bounds` / `rangeCheck_loop_zvalues` /
`rangeCheck_loop_constraints_complete`, adapted to the double-and-add round.

The per-row cell values read off the environment. The double-and-add region packs six cells per
loop row (`z, x_p, y_p, λ₁, λ₂, x_a'`) after three starting-copy rows, exactly the donor's
`rowZ`/`rowXA`/… absolute-row addressing (`Incomplete.lean:419-448`) — here spelled through the
Ironwood `env.advice cfg.col (place self + row)` accessor rather than the donor's flat
`env.get`.

TACTIC GAP (proofs sorried): the framework half — reducing each round's `enableGate` constraint
(`gate.constraints.Forall … poly.eval (Query.eval env (sel↦1) row) = 0`) to the value-level row
equations `gradient_1/secant_line/gradient_2` over `env.advice` reads at the rotated rows — is
mechanical `circuit_norm` + `cast_row_pred`/`row_succ_succ` normalization, but is not yet
distilled into a reusable tactic. Once the row facts are cleaned, the value-level chain
induction is *exactly* the donor's `soundness_aux`/`accVal_eq_nsmul` (imported), applied to the
env-cell readers. These statements are fully worked out; only their proofs are deferred. -/

/-- Env reader: advice value of column `col` at region-local row `row` in region `self`. -/
def adv (cfg_col : Column .advice) (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment Fp) (row : ℕ) : Fp :=
  env.advice cfg_col ((place self + row : ℕ) : ℤ)

/-- **Round-invariant / accumulator lemma (soundness).** If the loop's constraints hold in the
ambient region, the base `P` is on-curve, and the starting accumulator reads `[m]P` at the
`x_a`/`λ₁` starting cells (`hxA0`/`hyA0`) with `m` in the exceptional-case-free range, then after
`n + 1` rounds the final `x_a` cell (row `offset + 1 + (n+1)`) is `([accScalar m bits (n+1)]•P).x`
and the witnessed doubled final `y` is `2·([…]•P).y`.

This routes the cleaned round facts into the donor's `soundness_aux` (imported). Stated fully;
proof deferred (see the TACTIC GAP above). -/
theorem loop_acc_sound (cfg : Config) (input : Inputs (AssignedCell Fp)) (bits : BitsHint)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset n : ℕ)
    (P : Point Fp) (hP : P.OnCurve)
    (m : ℕ) (h2 : 2 ≤ m) (hbound : 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254)
    (hxA0 : adv cfg.xA place self env (offset + 1) = (m • P).x)
    (hyA0 : adv cfg.lambda1 place self env offset = (m • P).y)
    (hxPBase : adv cfg.xP place self env (offset + 1) = P.x)
    (hyPBase : adv cfg.yP place self env (offset + 1) = P.y)
    (hLoop : RegionOperations.Constraints place self env
      ((loop cfg input bits offset (n + 1)).operations self)) :
    adv cfg.xA place self env (offset + 1 + n + 1)
      = ((accScalar m bits (n + 1)) • P).x := by
  sorry

/-- **z-chain lemma (soundness).** Under the loop constraints and the starting `z` copy, each
running-sum cell satisfies `z_{r} = 2·z_{r-1} + k_r` with `k_r ∈ {0,1}` — the chain the `Spec`'s
running-sum conjunct exposes. Stated fully; proof deferred (mechanical, from each round's
`bool_check` gate constraint). -/
theorem loop_zchain_sound (cfg : Config) (input : Inputs (AssignedCell Fp)) (bits : BitsHint)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset n : ℕ)
    (hz0 : adv cfg.z place self env offset = input.z.eval place env)
    (hLoop : RegionOperations.Constraints place self env
      ((loop cfg input bits offset (n + 1)).operations self)) :
    ∃ bits' : BitsHint,
      adv cfg.z place self env (offset + 1)
        = 2 * input.z.eval place env + (if bits' 0 then 1 else 0) ∧
      ∀ r : Fin n, adv cfg.z place self env (offset + 1 + (r.val + 1))
        = 2 * adv cfg.z place self env (offset + 1 + r.val)
          + (if bits' (r.val + 1) then 1 else 0) := by
  sorry

/-- **Completeness loop lemma.** The honest prover's `ExtendsWitnesses` of the loop pins every
cell to the donor's honest value (`zRunValue`/`rowLambdaValue`/`accVal`), and the loaded round
gates then hold — the `Constraints` half of completeness. Routes into the donor's `honest_step`
/`accVal_eq_nsmul` (imported). Stated fully; proof deferred (see the TACTIC GAP above). -/
theorem loop_constraints_complete (cfg : Config) (input : Inputs (AssignedCell Fp)) (bits : BitsHint)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment Fp) (offset n : ℕ)
    (P : Point Fp) (hP : P.OnCurve)
    (m : ℕ) (h2 : 2 ≤ m) (hbound : 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254)
    (hxA0 : adv cfg.xA place self env.toEnvironment (offset + 1) = (m • P).x)
    (hyA0 : adv cfg.lambda1 place self env.toEnvironment offset = (m • P).y)
    (hxPBase : input.base.x.eval place env.toEnvironment = P.x)
    (hyPBase : input.base.y.eval place env.toEnvironment = P.y)
    (hWit : RegionOperations.ExtendsWitnesses place self env
      ((loop cfg input bits offset (n + 1)).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment
      ((loop cfg input bits offset (n + 1)).operations self) := by
  sorry

/-! ## The bundle contract

`Spec` exposes the round invariant. `Assumptions`/`ProverAssumptions` are the donor's incomplete-
addition preconditions (base on-curve; `A = [m]P`, `2 ≤ m`, `2^{n+2}(m+1) ≤ 2^{254}`).

The bits are a prover hint. To keep the region-level bundle's I/O verifier-visible, we take the
bit sequence as a *hint* read from the prover environment (`env.env.hint`) — the honest
witnesses `zWit`/`l1Wit`/… close over a fixed `BitsHint`; the bundle is parameterized by that
hint. This matches how the donor threads `input.bits` as an `UnconstrainedNative`. -/

/-- The scalar-mul incomplete-phase round predicate: the running-sum chain and, for any
`A = [m]P` in range, the output accumulator is the double-and-add result. -/
def RoundInvariant (n : ℕ) (input : Inputs Fp) (output : Output (n + 1) Fp)
    (bits : BitsHint) : Prop :=
  let base : Point Fp := input.base
  (output.zs[0] = 2 * input.z + (if bits 0 then 1 else 0) ∧
    ∀ b : Fin n, output.zs[b.val + 1] =
      2 * output.zs[b.val] + (if bits (b.val + 1) then 1 else 0)) ∧
  ∀ (m : ℕ),
    Point.ofCoords (input.xA, input.yA) = m • base →
    2 ≤ m → 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254 →
    Point.ofCoords (output.xA, output.yA) = (accScalar m bits (n + 1)) • base

/-! ## The gadget bundle

`incomplete::Config::<{n+1}>::double_and_add` (`CircuitVersion::AnchoredBase`). Instantiated at
`n = 124` for the `hi` half and `n = 125` for the `lo` half. Parameterized by the concrete
prover bit sequence `bits` (Rust hands `double_and_add` a known `&[Value<bool>]` slice); the
verifier-facing `Spec` still existentially quantifies a matching bit sequence, so soundness does
not depend on the prover's honesty about `bits`. -/

/-- The starting-cell copies emitted before the loop (`incomplete.rs:271-290`): the running sum
`z` into `cfg.z` at `offset`, and `y_a` into `cfg.λ₁` at `offset`, and `x_a` into `cfg.x_a` at
`offset + 1`. Split out so `synthesize`'s operation list decomposes cleanly. -/
def startCopies (cfg : Config) (input : Inputs (AssignedCell Fp)) (offset : ℕ) :
    RegionCircuit Fp Unit := do
  let _z ← copyAdvice input.z cfg.z offset
  let _yA ← copyAdvice input.yA cfg.lambda1 offset
  let _xA ← copyAdvice input.xA cfg.xA (offset + 1)
  return ()

def double_and_add (n : ℕ) (bits : BitsHint) :
    FormalRegionCircuit Fp
      (Column .advice × Column .advice × Column .advice × Column .advice ×
        Column .advice × Column .advice)
      Config Inputs (Output (n + 1)) where
  configure := fun (z, xA, xP, yP, lambda1, lambda2) =>
    configure z xA xP yP lambda1 lambda2

  synthesize cfg offset (input : Inputs (AssignedCell Fp)) := do
    -- starting copies
    startCopies cfg input offset
    -- q_mul_1 at `offset`, q_mul_2 at `offset+1 .. offset+n`, q_mul_3 at `offset+1+n`
    (qMul1Gate cfg).enable offset
    -- the per-bit round loop, in the `rangeCheckLoop` shape
    loop cfg input bits offset (n + 1)
    -- selectors for the interior rounds and the last round
    -- (enabled after the loop; enable order carries no semantic content)
    let _ ← (Vector.range n).mapM (fun i => (qMul2Gate cfg).enable (offset + 1 + i))
    (qMul3Gate cfg).enable (offset + 1 + n)
    -- the witnessed final y_a
    let _yAFinal ← assignAdvice cfg.lambda1 (offset + 1 + (n + 1)) (yAFinalWit n input bits)
    -- name the output cells (at fixed absolute rows). `cellAt` emits no op, it just names a
    -- cell reference at a known region-local row, so the region index is threaded implicitly.
    let xAOut ← cellAt cfg.xA (offset + 1 + n + 1)
    let yAOut ← cellAt cfg.lambda1 (offset + 1 + (n + 1))
    let zsOut ← (Vector.range (n + 1)).mapM (fun r => cellAt cfg.z (offset + 1 + r))
    return { xA := xAOut, yA := yAOut, zs := zsOut }

  -- base is a non-identity on-curve point (Rust exceptional-case check: A/Q not identity,
  -- x_p ≠ x_a across the run — subsumed by the range condition below on the honest side).
  Assumptions input :=
    let base : Point Fp := input.base
    base.OnCurve

  Spec input output _ :=
    ∃ bits' : BitsHint, RoundInvariant n input output bits'

  -- honest-prover precondition: base on-curve; accumulator is a small positive multiple of the
  -- base in the range where every incomplete addition is exceptional-case-free.
  ProverAssumptions input _ :=
    let base : Point Fp := input.base
    base.OnCurve ∧ ∃ m : ℕ,
      Point.ofCoords (input.xA, input.yA) = m • base ∧
      2 ≤ m ∧ 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254

  ProverSpec input output _ := RoundInvariant n input output bits

  -- ══ Soundness ══
  -- Framework half (mechanical, TACTIC GAP): `soundness_iff`, then split the synthesize op list
  --   startCopies ++ [q_mul_1] ++ loop ++ [q_mul_2…] ++ [q_mul_3] ++ [final y_a] ++ (output cells)
  -- via `RegionOperations.constraints_append`, land the starting-copy equalities on the input
  -- coords, and read the output cells (fixed rows) off the env. User half: feed the cleaned facts
  -- into `loop_zchain_sound` (running-sum chain) and `loop_acc_sound` (accumulator = `accScalar`),
  -- both of which route into the imported donor algebra. Deferred pending the split/eval tactic.
  soundness := by
    sorry

  -- ══ Completeness ══
  -- Framework half (mechanical, TACTIC GAP): `completeness_iff`, split the witness/constraint op
  -- lists the same way; the honest starting copies pin `z_0`/`y_a_0`/`x_a_0`, `loop_constraints_
  -- complete` discharges the loop's `Constraints`, the starting-copy + gate witnesses discharge
  -- the rest, and `ProverSpec` follows from the same donor algebra as soundness. Deferred.
  completeness := by
    sorry

end Halo2.Ironwood.Ecc.MulIncomplete
