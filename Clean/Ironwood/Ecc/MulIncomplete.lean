import Clean.Halo2
import Clean.Orchard.Specs.Pallas
import Clean.Ironwood.Ecc.Basic
import Clean.Orchard.Ecc.DoubleAndAdd
import Clean.Orchard.Ecc.Mul.Incomplete
import Clean.Orchard.Ecc.Mul.Assign

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
open Orchard.Ecc.Mul (kBits kNat tQNat)
open Orchard.Ecc.Mul.Incomplete.DoubleAndAdd
  (accScalar zRunValue stepPoint accVal lambdaCellsValue rowLambdaValue
   accScalar_two_le accScalar_le pow254_lt_card)
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

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

/-- `Y_A = (λ₁ + λ₂)(x_A − x_R)` at `rotation`, *without* the `1/2` (Rust `Y_A`,
`incomplete.rs:52-55`). The compiled gate multiplies this by `TWO_INV` (see `yA`). -/
def yAExpr (cfg : Config) (rot : Rotation) : Expression Fp Query :=
  let xA : Expression Fp Query := queryAdvice cfg.xA rot
  let l1 : Expression Fp Query := queryAdvice cfg.lambda1 rot
  let l2 : Expression Fp Query := queryAdvice cfg.lambda2 rot
  (l1 + l2) * (xA - xRExpr cfg rot)

/-- `y_a = Y_A · TWO_INV` at `rotation` — the actual per-row `y_a` the Rust gate uses (Rust
`y_a` closure, `incomplete.rs:114-116`: `Y_A(meta,rot) * TWO_INV`). `TWO_INV = (2 : Fp)⁻¹`,
placed on the RIGHT of `Y_A` as a field scalar, so the erasure is `.scaled Y_A TWO_INV` —
matching the VK fixture (which pins the raw `TWO_INV` scalar, `14474…169 = 1/2 mod p`). This
is the VK-faithful spelling; the earlier ×2-normalised form (which cleared the halving to stay
`ring`-friendly) does NOT match the pinned constraint system. -/
def yA (cfg : Config) (rot : Rotation) : Expression Fp Query :=
  yAExpr cfg rot * ((2 : Fp)⁻¹)

/-- The shared "for-loop" body of the `q_mul_{2,3}` gates (`incomplete.rs:121-169`),
VK-faithful (each `y_a` carries `.scaled … TWO_INV`, no ×2 clearing): booleanity of the bit
`k = z_cur − z_prev·2`, `gradient_1`, `secant_line`, `gradient_2`. `yANext` is the
caller-supplied next-row `y_a` (for `q_mul_2` it is `y_a(next) = Y_A(next)·TWO_INV`; for
`q_mul_3` it is the witnessed final `y` in the `λ₁` column at `next`, a bare query). -/
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
  -- k = z_cur − z_prev·2  (Rust `z_cur - z_prev * Base::from(2)`, `.scaled z_prev 2`)
  let k : Expression Fp Query := zCur - zPrev * (2 : Fp)
  -- `bool_check(k) = k·(1 − k)` (Rust `bool_check`), constant 1 on the LEFT.
  let boolCheck := k * ((1 : Fp) - k)
  -- λ₁·(x_A − x_P) − y_a + (k·2 − 1)·y_P   (Rust `gradient_1`, `incomplete.rs:152-153`),
  -- with `y_a = Y_A·TWO_INV` (`.scaled`) and `k·2 = .scaled k 2`; NO ×2 normalisation.
  let gradient1 :=
    l1 * (xACur - xPCur) - yA cfg 0
      + (k * (2 : Fp) - (1 : Fp)) * yPCur
  -- λ₂² − x_{A,next} − x_R − x_A  (Rust `secant_line`, `incomplete.rs:156-159`)
  let secantLine := l2 * l2 - xANext - xRExpr cfg 0 - xACur
  -- λ₂·(x_A − x_{A,next}) − y_a − y_a_next  (Rust `gradient_2`, `incomplete.rs:162`);
  -- `y_a_next` is the caller-supplied next-row `y_a` (scaled for q_mul_2, witnessed for q_mul_3).
  let gradient2 := l2 * (xACur - xANext) - yA cfg 0 - yANextDouble
  [ ("bool_check", boolCheck),
    ("gradient_1", gradient1),
    ("secant_line", secantLine),
    ("gradient_2", gradient2) ]

/-- The `q_mul_1 == 1` gate (`incomplete.rs:173-179`): the witnessed `y_a` (in the `λ₁` column
at the current row) equals the derived next-row `y_a`. VK-faithful: `y_a_witnessed − y_a(next)`
with `y_a(next) = Y_A(next)·TWO_INV` (`.scaled`); no ×2. -/
def qMul1Gate (cfg : Config) : Gate Fp where
  name := "q_mul_1 == 1 checks"
  selector := cfg.qMul1
  constraints :=
    let yAWitnessed : Expression Fp Query := queryAdvice cfg.lambda1 0
    Constraints.withSelector cfg.qMul1
      [("init y_a", yAWitnessed - yA cfg 1)]

/-- The `q_mul_2 == 1` gate (`incomplete.rs:183-209`): base-constancy checks `x_p`/`y_p` are the
same on the next row, plus the shared for-loop body with `y_a_next = y_a(next) = Y_A(next)·TWO_INV`. -/
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
        ++ forLoopPolys cfg (yA cfg 1))

/-- The `q_mul_3 == 1` gate (`incomplete.rs:213-217`): the for-loop body on the last row, with
`y_a_next = y_a_final` the WITNESSED final `y` in the `λ₁` column at `next` (a bare query, NOT a
derived `Y_A` — Rust `y_a_final = meta.query_advice(lambda_1, Rotation::next())`). -/
def qMul3Gate (cfg : Config) : Gate Fp where
  name := "q_mul_3 == 1 checks"
  selector := cfg.qMul3
  constraints :=
    let yAFinal : Expression Fp Query := queryAdvice cfg.lambda1 1
    Constraints.withSelector cfg.qMul3
      (forLoopPolys cfg yAFinal)

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

Mirrors the donor `DoubleAndAdd.Input`/`Output`, plus the scalar cell `alpha` the bits are
derived from (in the donor the bits were an `UnconstrainedNative` hint; here they are computed
from the cell — see `bitsOf`). The output is the final accumulator cells and all interstitial
running sums. -/

/-- Prover-side scalar bits, MSB-first, indexed from the first processed bit — the Ironwood
alias of the donor's `BitsHint`. -/
def BitsHint : Type := ℕ → Bool

instance : Inhabited BitsHint := ⟨fun _ => false⟩

/-- The verifier-visible inputs: the scalar cell `alpha` (the bit source — the working scalar's
bits are derived from it as `kBits alpha`, faithful to Rust `decompose_for_scalar_mul(alpha.value())`),
the (non-identity, on-curve) base point, and the accumulator `(x_a, y_a)` and running sum `z`
entering the phase, as already-assigned cells. There is NO prover-side `bits` parameter: the
per-round bit at global index `w + r` is `kBits alpha (w + r)`, computed inside the witness
closures via `readCell env alpha` (`w` is the bundle's window offset). -/
structure Inputs (F : Type) where
  alpha : F
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

The honest cell values are complex functions of the base/accumulator cells and the working
scalar's bits, so — like the donor's `witnessNative` — we express them via the witgen `native`
escape hatch (`WitgenIROver.native`), reading the placed prover environment. Each returns a
length-1 vector. The bits are NOT a prover-supplied `BitsHint`: they are derived from the
witnessed scalar cell `input.alpha` as `kBits (readCell env input.alpha)` (faithful to Rust
`decompose_for_scalar_mul(alpha.value())`), windowed by the bundle's window offset `w` (so the
per-round bit at loop index `r` is `kBits (alpha value) (w + r)`).

`readCell env c` reads the value of an already-assigned input cell `c` in the placed prover
environment `env` — the base coordinates, starting accumulator, and scalar cell the honest
values depend on. -/

/-- Read an input cell's value in a placed prover environment. -/
def readCell (env : Placed ProverEnvironment Fp) (c : AssignedCell Fp) : Fp :=
  c.eval env.place env.env.toEnvironment

/-- The `w`-shifted window of the working scalar's bits, as a function of the scalar value:
`kBitsWindow a w i = kBits a (w + i)` (see `kBitsWindow_eq_kBits`), i.e. bit `k_{254-(w+i)}` of
the unreduced working scalar `k = a.val + t_q` (Rust `decompose_for_scalar_mul`).

KERNEL-SAFETY (load-bearing spelling): the `t_q` addition is FLIPPED relative to the donor's
`kNat` (`tQNat + a.val`, not `a.val + tQNat`). `Nat.add` recurses on its SECOND argument, so a
kernel whnf reaching the donor spelling unfolds the ~2^125 literal unarily — "(kernel) deep
recursion detected". With the literal on the left, whnf is stuck immediately on the abstract
`a.val`, so this def is safe to have anywhere in kernel-checked proof terms. Bridge to the
donor's `kBits` (for the donor chain lemmas) via `kBitsWindow_eq_kBits` — a rewrite, never a
defeq. -/
def kBitsWindow (a : Fp) (w : ℕ) : BitsHint :=
  fun i => (tQNat + a.val).testBit (254 - (w + i))

/-- `kBitsWindow` is the `w`-shifted window of the donor's `kBits`. -/
theorem kBitsWindow_eq_kBits (a : Fp) (w i : ℕ) :
    kBitsWindow a w i = kBits a (w + i) := by
  unfold kBitsWindow kBits kNat
  rw [Nat.add_comm]

/-- `kBitsWindow` as a donor-`kBits` lambda — the shape the donor chain lemmas
(`chainNat_kBits`, `cells_kNat`, …) consume. -/
theorem kBitsWindow_as_kBits (a : Fp) (w : ℕ) :
    kBitsWindow a w = fun i => kBits a (w + i) :=
  funext fun i => kBitsWindow_eq_kBits a w i

/-- The zero-offset window is exactly the donor's `kBits`. -/
theorem kBitsWindow_zero (a : Fp) : kBitsWindow a 0 = kBits a :=
  funext fun i => by rw [kBitsWindow_eq_kBits, Nat.zero_add]

/-- The working-scalar bit family for this phase, derived from the scalar CELL in a placed
prover environment: `bitsOf input w env = kBitsWindow (alpha value) w` (Rust
`decompose_for_scalar_mul(alpha.value())`, then the `w`-shifted window). This is the ONLY
place the bits are computed; the loop plumbing below is abstract in an env-indexed bit
family `ebits`, and the bundle instantiates `ebits := bitsOf input w`. -/
def bitsOf (input : Inputs (AssignedCell Fp)) (w : ℕ) :
    Placed ProverEnvironment Fp → BitsHint :=
  fun env => kBitsWindow (readCell env input.alpha) w

/-- Honest `z` running-sum value at loop row `r` (`incomplete.rs:302-306`). -/
def zWit (input : Inputs (AssignedCell Fp)) (ebits : Placed ProverEnvironment Fp → BitsHint)
    (r : ℕ) : WitgenIR Fp 1 :=
  .native fun env => #v[zRunValue (readCell env input.z) (ebits env) r]

/-- Honest `λ₁` value at loop row `r`. -/
def l1Wit (input : Inputs (AssignedCell Fp)) (ebits : Placed ProverEnvironment Fp → BitsHint)
    (r : ℕ) : WitgenIR Fp 1 :=
  .native fun env => #v[
    (rowLambdaValue (readCell env input.base.x) (readCell env input.base.y)
      (readCell env input.xA) (readCell env input.yA) (ebits env) r).lambda1]

/-- Honest `λ₂` value at loop row `r`. -/
def l2Wit (input : Inputs (AssignedCell Fp)) (ebits : Placed ProverEnvironment Fp → BitsHint)
    (r : ℕ) : WitgenIR Fp 1 :=
  .native fun env => #v[
    (rowLambdaValue (readCell env input.base.x) (readCell env input.base.y)
      (readCell env input.xA) (readCell env input.yA) (ebits env) r).lambda2]

/-- Honest next-row `x_a` value after loop row `r` (`accVal … (r+1)`). -/
def xANextWit (input : Inputs (AssignedCell Fp)) (ebits : Placed ProverEnvironment Fp → BitsHint)
    (r : ℕ) : WitgenIR Fp 1 :=
  .native fun env => #v[
    (accVal (readCell env input.base.x) (readCell env input.base.y)
      (readCell env input.xA) (readCell env input.yA) (ebits env) (r + 1)).1]

/-- Honest final `y_a` value after `n + 1` rounds (`accVal … (n+1)`). -/
def yAFinalWit (n : ℕ) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint) : WitgenIR Fp 1 :=
  .native fun env => #v[
    (accVal (readCell env input.base.x) (readCell env input.base.y)
      (readCell env input.xA) (readCell env input.yA) (ebits env) (n + 1)).2]

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
def round (cfg : Config) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint)
    (offset n r : ℕ) : RegionCircuit Fp Unit := do
  let row := offset + 1 + r
  let _z ← assignAdvice cfg.z row (zWit input ebits r)
  -- x_p / y_p: anchored copy of `base` on the first loop row, plain assignment otherwise
  if r = 0 then
    let _xP ← copyAdvice input.base.x cfg.xP row
    let _yP ← copyAdvice input.base.y cfg.yP row
  else
    let _xP ← assignAdvice cfg.xP row (.ofFExpr (.expr input.base.x))
    let _yP ← assignAdvice cfg.yP row (.ofFExpr (.expr input.base.y))
  let _l1 ← assignAdvice cfg.lambda1 row (l1Wit input ebits r)
  let _l2 ← assignAdvice cfg.lambda2 row (l2Wit input ebits r)
  let _xANext ← assignAdvice cfg.xA (row + 1) (xANextWit input ebits r)
  -- the round's selector: `q_mul_2` on interior rows (`r < n`), `q_mul_3` on the last (`r = n`).
  -- Enabling inside the round is what lands each round's gate constraints in the loop's
  -- `Constraints`, so the loop lemmas can consume them by the same induction as range_check.
  if r = n then
    (qMul3Gate cfg).enable row
  else
    (qMul2Gate cfg).enable row
  return ()

/-- The double-and-add loop: `numRounds` rounds, structurally recursive. By the append-bind of
`RegionCircuit`, `(loop … (k+1)).operations self = (loop … k).operations self ++
(round … k).operations self` — the per-round decomposition the induction consumes. -/
def loop (cfg : Config) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint) (offset n : ℕ) :
    ℕ → RegionCircuit Fp Unit
  | 0 => pure ()
  | k + 1 => do
    loop cfg input ebits offset n k
    round cfg input ebits offset n k

/-- Per-round operations decomposition (holds by `rfl` via the monad's `operations_bind`): the
crux that makes the loop inductable. Mirrors `rangeCheckLoop_operations_succ`. -/
theorem loop_operations_succ (cfg : Config) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint)
    (offset n k : ℕ) (self : RegionIndex) :
    (loop cfg input ebits offset n (k + 1)).operations self
      = (loop cfg input ebits offset n k).operations self
        ++ (round cfg input ebits offset n k).operations self := rfl

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

/-- Name a whole vector of cells at fixed region-local rows (`rows i` for `i < len`), emitting
no op — the vector-valued analogue of `cellAt`, for the `Output.zs` running-sum cells. Returns
`Vector.ofFn` directly so its `output` is `rfl` and indexes by `Vector.getElem_ofFn` (avoiding a
`Vector.mapM`-over-`RegionCircuit` characterization). -/
def cellVec (col : Column .advice) (rows : ℕ → ℕ) (len : ℕ) :
    RegionCircuit Fp (Vector (AssignedCell Fp) len) :=
  fun self => (Vector.ofFn (fun i => AssignedCell.of self (rows i) col), [])

@[circuit_norm]
theorem operations_cellVec (col : Column .advice) (rows : ℕ → ℕ) (len : ℕ) (self : RegionIndex) :
    (cellVec col rows len).operations self = [] := rfl

@[circuit_norm]
theorem output_cellVec (col : Column .advice) (rows : ℕ → ℕ) (len : ℕ) (self : RegionIndex) :
    (cellVec col rows len).output self
      = Vector.ofFn (fun i => AssignedCell.of self (rows i) col) := rfl

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

section LoopFacts

variable (cfg : Config) (input : Inputs (AssignedCell Fp))
  (ebits : Placed ProverEnvironment Fp → BitsHint)
  (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset : ℕ)

/-- The per-row cell readers, as abbreviations over `adv` at the round's absolute row. -/
private def XAr (r : ℕ) : Fp := adv cfg.xA place self env (offset + 1 + r)
private def XPr (r : ℕ) : Fp := adv cfg.xP place self env (offset + 1 + r)
private def YPr (r : ℕ) : Fp := adv cfg.yP place self env (offset + 1 + r)
private def L1r (r : ℕ) : Fp := adv cfg.lambda1 place self env (offset + 1 + r)
private def L2r (r : ℕ) : Fp := adv cfg.lambda2 place self env (offset + 1 + r)
/-- The `z` running-sum reader at the round's row, and its predecessor (the `z` cell one
row earlier: for `r = 0` the start-copy at `offset`, otherwise the previous round's `z`). -/
private def Zr (r : ℕ) : Fp := adv cfg.z place self env (offset + 1 + r)
private def Zpr (r : ℕ) : Fp := adv cfg.z place self env (offset + r)
/-- The bit read off the running sum at round `r`: `k_r = z_r − 2·z_{r−1}`. -/
private def Kr (r : ℕ) : Fp := Zr cfg place self env offset r - Zpr cfg place self env offset r * 2
/-- The derived `Y_A` of row `r` (`(λ₁+λ₂)(x_A − x_R)`); at `r = n+1` we instead read the
witnessed doubled final `y` from the `λ₁` column at `offset+1+(n+1)`. -/
private def YADr (n r : ℕ) : Fp :=
  if r = n + 1 then 2 * adv cfg.lambda1 place self env (offset + 1 + (n + 1))
  else (L1r cfg place self env offset r + L2r cfg place self env offset r) *
    (XAr cfg place self env offset r -
      (L1r cfg place self env offset r * L1r cfg place self env offset r
        - XAr cfg place self env offset r - XPr cfg place self env offset r))

/-- **Extraction of the cleaned per-round gate facts.** From the loop's `Constraints`
(gate enables are inside `round`, so the round constraints live here), each round
`r < numRounds` yields the four shared `forLoopPolys` facts (booleanity, gradient_1,
secant_line, gradient_2), and — for interior rounds (`r ≠ n`) — the `x_p`/`y_p`
constancy. Proven by induction over `numRounds`, mirroring
`rangeCheck_loop_word_bounds`. -/
private theorem loop_gate_facts (n : ℕ) :
    ∀ numRounds : ℕ, numRounds ≤ n + 1 →
    RegionOperations.Constraints place self env
      ((loop cfg input ebits offset n numRounds).operations self) →
    ∀ r, r < numRounds →
      -- booleanity of the bit
      (IsBool (Kr cfg place self env offset r)) ∧
      -- gradient_1 (×2 form)
      (2 * L1r cfg place self env offset r *
          (XAr cfg place self env offset r - XPr cfg place self env offset r)
        + 2 * ((Kr cfg place self env offset r * 2 - 1) * YPr cfg place self env offset r)
        = YADr cfg place self env offset n r) ∧
      -- secant_line
      (L2r cfg place self env offset r * L2r cfg place self env offset r
        = XAr cfg place self env offset (r + 1)
          + (L1r cfg place self env offset r * L1r cfg place self env offset r
              - XAr cfg place self env offset r - XPr cfg place self env offset r)
          + XAr cfg place self env offset r) ∧
      -- gradient_2
      (2 * L2r cfg place self env offset r *
          (XAr cfg place self env offset r - XAr cfg place self env offset (r + 1))
        = YADr cfg place self env offset n r + YADr cfg place self env offset n (r + 1)) ∧
      -- x_p / y_p constancy on interior rounds
      (r ≠ n → XPr cfg place self env offset r = XPr cfg place self env offset (r + 1)
        ∧ YPr cfg place self env offset r = YPr cfg place self env offset (r + 1)) := by
  intro numRounds
  induction numRounds with
  | zero => intro _ _ r hr; omega
  | succ k ih =>
    intro hkb
    rw [loop_operations_succ, RegionOperations.constraints_append]
    rintro ⟨hLoop, hRound⟩ r hr
    have hrle : r ≤ n := by omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr' | rfl
    · exact ih (by omega) hLoop r hr'
    · -- the fresh round `r = k`. Reduce its gate constraints to the value-level facts.
      -- `2 ≠ 0` lets the gradient closers clear the `TWO_INV = 2⁻¹` in the VK-faithful `y_a`.
      have h2 : (2 : Fp) ≠ 0 := by decide
      -- The `z`-prev cell reads at `↑(place self + (offset+1+r)) - 1`; normalize it to the
      -- `Zpr` spelling `↑(place self + (offset+r))` (the single `offset+(k+1)` boundary quirk).
      have hzp : ((place self + (offset + 1 + r) : ℕ) : ℤ) - 1
          = ((place self + (offset + r) : ℕ) : ℤ) := by push_cast; ring
      -- YADr at `r` is always the derived form (since `r ≤ n < n+1`)
      have hYADr : YADr cfg place self env offset n r
          = (L1r cfg place self env offset r + L2r cfg place self env offset r) *
            (XAr cfg place self env offset r -
              (L1r cfg place self env offset r * L1r cfg place self env offset r
                - XAr cfg place self env offset r - XPr cfg place self env offset r)) := by
        rw [YADr, if_neg (by omega)]
      -- YADr at `r+1`: derived when `r ≠ n`, the witnessed doubled final `y` when `r = n`.
      have hYADr1n : YADr cfg place self env offset n (n + 1)
          = 2 * adv cfg.lambda1 place self env (offset + 1 + (n + 1)) := by rw [YADr, if_pos rfl]
      have hYADr1i : r ≠ n → YADr cfg place self env offset n (r + 1)
          = (L1r cfg place self env offset (r + 1) + L2r cfg place self env offset (r + 1)) *
            (XAr cfg place self env offset (r + 1) -
              (L1r cfg place self env offset (r + 1) * L1r cfg place self env offset (r + 1)
                - XAr cfg place self env offset (r + 1) - XPr cfg place self env offset (r + 1))) :=
        fun h => by rw [YADr, if_neg (by omega)]
      simp only [XAr, XPr, YPr, L1r, L2r, Zr, Zpr, Kr, adv] at hYADr hYADr1n hYADr1i ⊢
      -- resolve the round's `if r = 0` (anchored copy) split first, so its ops reduce
      by_cases hr0 : r = 0
      · -- first loop row: `x_p`/`y_p` are copies of `base`
        subst hr0
        by_cases hrn : (0 : ℕ) = n
        · -- single-round circuit: `q_mul_3` on row 0
          subst hrn
          rw [hYADr, hYADr1n]
          round_norm [round, qMul3Gate, forLoopPolys, yA, yAExpr, xRExpr] at hRound
          obtain ⟨_hxpc, _hypc, hbool, hg1, hsec, hg2⟩ := hRound
          refine ⟨?_, ?_, ?_, ?_, by intro h; exact absurd rfl h⟩
          · rcases mul_eq_zero.mp hbool with h | h
            · exact Or.inl (by linear_combination h)
            -- `bool_check = k·(1−k)`: the second factor is `1 − k` (sign flip vs `k − 1`).
            · exact Or.inr (by linear_combination -h)
          -- gate polys are now in VK-faithful (non-×2, `y_a = Y_A·TWO_INV`) form; the round
          -- Spec keeps the ×2 convention, so multiply each gradient constraint by 2 and clear
          -- the `2⁻¹` via `field_simp` (needs `h2 : 2 ≠ 0`).
          · linear_combination (norm := (field_simp; ring)) 2 * hg1
          · linear_combination hsec
          · linear_combination (norm := (field_simp; ring)) 2 * hg2
        · -- interior first row: `q_mul_2` on row 0
          rw [hYADr, hYADr1i hrn]
          round_norm [round, qMul2Gate, forLoopPolys, yA, yAExpr, xRExpr, if_neg hrn] at hRound
          obtain ⟨_hxpc, _hypc, hxpk, hypk, hbool, hg1, hsec, hg2⟩ := hRound
          refine ⟨?_, ?_, ?_, ?_,
            fun _ => ⟨by linear_combination hxpk, by linear_combination hypk⟩⟩
          · rcases mul_eq_zero.mp hbool with h | h
            · exact Or.inl (by linear_combination h)
            -- `bool_check = k·(1−k)`: the second factor is `1 − k` (sign flip vs `k − 1`).
            · exact Or.inr (by linear_combination -h)
          -- gate polys are now in VK-faithful (non-×2, `y_a = Y_A·TWO_INV`) form; the round
          -- Spec keeps the ×2 convention, so multiply each gradient constraint by 2 and clear
          -- the `2⁻¹` via `field_simp` (needs `h2 : 2 ≠ 0`).
          · linear_combination (norm := (field_simp; ring)) 2 * hg1
          · linear_combination hsec
          · linear_combination (norm := (field_simp; ring)) 2 * hg2
      · -- non-first loop row: `x_p`/`y_p` are plain assignments; `z`-prev normalizes via `hzp`
        by_cases hrn : r = n
        · -- last round: `q_mul_3`
          subst hrn
          rw [hYADr, hYADr1n]
          round_norm [round, qMul3Gate, forLoopPolys, yA, yAExpr, xRExpr, if_neg hr0] at hRound
          obtain ⟨hbool, hg1, hsec, hg2⟩ := hRound
          refine ⟨?_, ?_, ?_, ?_, by intro h; exact absurd rfl h⟩
          · rcases mul_eq_zero.mp hbool with h | h
            · exact Or.inl (by linear_combination h)
            -- `bool_check = k·(1−k)`: the second factor is `1 − k` (sign flip vs `k − 1`).
            · exact Or.inr (by linear_combination -h)
          -- gate polys are now in VK-faithful (non-×2, `y_a = Y_A·TWO_INV`) form; the round
          -- Spec keeps the ×2 convention, so multiply each gradient constraint by 2 and clear
          -- the `2⁻¹` via `field_simp` (needs `h2 : 2 ≠ 0`).
          · linear_combination (norm := (field_simp; ring)) 2 * hg1
          · linear_combination hsec
          · linear_combination (norm := (field_simp; ring)) 2 * hg2
        · -- interior round: `q_mul_2`
          rw [hYADr, hYADr1i hrn]
          -- ACCEPTANCE (C2a #1): `round_norm` bundles the gate `circuit_norm` reduction with the
          -- gate/def args AND the rotation-row cast (the hand `simp only [hzp]`, mechanized).
          round_norm [round, qMul2Gate, forLoopPolys, yA, yAExpr, xRExpr, if_neg hr0, if_neg hrn]
            at hRound
          obtain ⟨hxpk, hypk, hbool, hg1, hsec, hg2⟩ := hRound
          refine ⟨?_, ?_, ?_, ?_,
            fun _ => ⟨by linear_combination hxpk, by linear_combination hypk⟩⟩
          · rcases mul_eq_zero.mp hbool with h | h
            · exact Or.inl (by linear_combination h)
            -- `bool_check = k·(1−k)`: the second factor is `1 − k` (sign flip vs `k − 1`).
            · exact Or.inr (by linear_combination -h)
          -- gate polys are now in VK-faithful (non-×2, `y_a = Y_A·TWO_INV`) form; the round
          -- Spec keeps the ×2 convention, so multiply each gradient constraint by 2 and clear
          -- the `2⁻¹` via `field_simp` (needs `h2 : 2 ≠ 0`).
          · linear_combination (norm := (field_simp; ring)) 2 * hg1
          · linear_combination hsec
          · linear_combination (norm := (field_simp; ring)) 2 * hg2

/-- **Extraction of the round-0 anchor copies.** Round 0 anchors `x_p`/`y_p` at `offset + 1`
to the base point by copy (`CircuitVersion::AnchoredBase`). For any `numRounds ≥ 1` the loop's
`Constraints` therefore pin `x_p`/`y_p` at `offset + 1` to `base.x`/`base.y`. Proven by
induction over `numRounds`, peeling round 0 (the innermost round). -/
private theorem loop_anchor (n : ℕ) :
    ∀ numRounds : ℕ, 1 ≤ numRounds →
    RegionOperations.Constraints place self env
      ((loop cfg input ebits offset n numRounds).operations self) →
    adv cfg.xP place self env (offset + 1) = input.base.x.eval place env ∧
    adv cfg.yP place self env (offset + 1) = input.base.y.eval place env := by
  intro numRounds
  induction numRounds with
  | zero => intro h; omega
  | succ k ih =>
    intro _ hC
    rw [loop_operations_succ, RegionOperations.constraints_append] at hC
    obtain ⟨hLoop, hRound⟩ := hC
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · -- `numRounds = 1`: round 0 is the fresh round; read its anchor copies directly
      simp only [round, circuit_norm, adv] at hRound ⊢
      exact ⟨hRound.1, hRound.2.1⟩
    · exact ih hk hLoop

end LoopFacts

/-- **Round-invariant / accumulator lemma (soundness).** If the loop's constraints hold in the
ambient region, the base `P` is on-curve, and the starting accumulator reads `[m]P` at the
`x_a`/`λ₁` starting cells (`hxA0`/`hyA0`) with `m` in the exceptional-case-free range, then after
`n + 1` rounds the final `x_a` cell (row `offset + 1 + (n+1)`) is `([accScalar m bits' (n+1)]•P).x`,
for the bit sequence `bits'` read off the running sum by the `bool_check` gates (`hbit`).

This routes the cleaned round facts (from `loop_gate_facts`) into the donor's `soundness_aux`
(imported). `bits'` is the constraint-forced bit sequence (the same one `loop_zchain_sound`
exposes), so soundness does not depend on the witness bit family `ebits` at all. -/
theorem loop_acc_sound (cfg : Config) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint) (bits' : BitsHint)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset n : ℕ)
    (P : Point Fp) (hP : P.OnCurve)
    (m : ℕ) (h2 : 2 ≤ m) (hbound : 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254)
    (hxA0 : adv cfg.xA place self env (offset + 1) = (m • P).x)
    (hyA0 : adv cfg.lambda1 place self env offset = (m • P).y)
    (hxPBase : adv cfg.xP place self env (offset + 1) = P.x)
    (hyPBase : adv cfg.yP place self env (offset + 1) = P.y)
    (hbit : ∀ r, r ≤ n →
      adv cfg.z place self env (offset + 1 + r) - adv cfg.z place self env (offset + r) * 2
        = (if bits' r then 1 else 0))
    -- the `q_mul_1` gate (enabled at `offset` outside the loop, discharged by the bundle
    -- soundness): the derived `Y_A` of loop row 0 equals twice the copied starting `y_a`.
    (hInit :
      (adv cfg.lambda1 place self env (offset + 1) + adv cfg.lambda2 place self env (offset + 1)) *
        (adv cfg.xA place self env (offset + 1) -
          (adv cfg.lambda1 place self env (offset + 1) * adv cfg.lambda1 place self env (offset + 1)
            - adv cfg.xA place self env (offset + 1) - adv cfg.xP place self env (offset + 1)))
        = 2 * adv cfg.lambda1 place self env offset)
    (hLoop : RegionOperations.Constraints place self env
      ((loop cfg input ebits offset n (n + 1)).operations self)) :
    adv cfg.xA place self env (offset + 1 + n + 1)
      = ((accScalar m bits' (n + 1)) • P).x
    ∧ 2 * adv cfg.lambda1 place self env (offset + 1 + (n + 1))
      = 2 * ((accScalar m bits' (n + 1)) • P).y := by
  have hfacts := loop_gate_facts cfg input ebits place self env offset n (n + 1) le_rfl hLoop
  -- the per-row cell readers as `ℕ → Fp` functions, in `soundness_aux`'s shape
  set XA := fun r => adv cfg.xA place self env (offset + 1 + r) with hXA
  set XP := fun r => adv cfg.xP place self env (offset + 1 + r) with hXP
  set YP := fun r => adv cfg.yP place self env (offset + 1 + r) with hYP
  set L1 := fun r => adv cfg.lambda1 place self env (offset + 1 + r) with hL1
  set L2 := fun r => adv cfg.lambda2 place self env (offset + 1 + r) with hL2
  -- `YAD r` is the derived `Y_A` for `r ≤ n`, and `2·(witnessed final y)` at `r = n+1`
  set YAD := fun r => if r = n + 1 then 2 * adv cfg.lambda1 place self env (offset + 1 + (n + 1))
    else (L1 r + L2 r) * (XA r - (L1 r * L1 r - XA r - XP r)) with hYAD
  -- base-point constancy along the rows (from the `q_mul_2` constancy checks + the anchor)
  have hconst : ∀ r, r ≤ n → XP r = P.x ∧ YP r = P.y := by
    intro r
    induction r with
    | zero => intro _; exact ⟨by rw [hXP]; simpa using hxPBase, by rw [hYP]; simpa using hyPBase⟩
    | succ v ih =>
      intro hv
      obtain ⟨hx, hy⟩ := ih (by omega)
      obtain ⟨_, _, _, _, hconstv⟩ := hfacts v (by omega)
      obtain ⟨hcx, hcy⟩ := hconstv (by omega)
      simp only [XPr, YPr] at hcx hcy
      refine ⟨?_, ?_⟩
      · simp only [hXP] at hx ⊢; rw [← hcx]; exact hx
      · simp only [hYP] at hy ⊢; rw [← hcy]; exact hy
  have haux := Orchard.Ecc.Mul.Incomplete.DoubleAndAdd.soundness_aux n P hP m h2 hbound
    XA XP YP L1 L2 YAD bits' ?hxA0 ?hYAD0 ?hyad ?hxp ?hyp ?hg1 ?hsec ?hg2
  case hxA0 => rw [hXA]; simpa using hxA0
  case hYAD0 =>
    -- `YAD 0 = (L1 0 + L2 0)(XA 0 - x_R 0)`; the `q_mul_1` gate (`hInit`) forces it to
    -- `2·(λ₁ at offset)`, and the starting-cell copy `hyA0` reads that as `(m•P).y`.
    simp only [hYAD, if_neg (show ¬(0 = n + 1) by omega), hXA, hL1, hL2, hXP, Nat.add_zero]
    rw [hInit, hyA0]
  case hyad =>
    intro r hr; simp only [hYAD, if_neg (show ¬(r = n + 1) by omega)]
  case hxp => exact fun r hr => (hconst r hr).1
  case hyp => exact fun r hr => (hconst r hr).2
  case hg1 =>
    intro r hr
    obtain ⟨_, hg1, _, _, _⟩ := hfacts r (by omega)
    have hk := hbit r hr
    -- `hg1 : 2·L1·(XA−XP) + 2·((Kr·2−1)·YP) = YADr r`; `Kr r = if bits' r then 1 else 0` by `hbit`.
    simp only [XAr, XPr, YPr, L1r, L2r, Kr, Zr, Zpr, YADr, if_neg (by omega : ¬(r = n + 1))] at hg1
    simp only [hYAD, if_neg (show ¬(r = n + 1) by omega), hXA, hXP, hYP, hL1, hL2]
    rw [show adv cfg.z place self env (offset + 1 + r)
          - adv cfg.z place self env (offset + r) * 2 = (if bits' r then 1 else 0) from hk] at hg1
    linear_combination hg1
  case hsec =>
    intro r hr
    obtain ⟨_, _, hsec, _, _⟩ := hfacts r (by omega)
    simp only [XAr, XPr, L1r, L2r] at hsec
    simp only [hXA, hXP, hL1, hL2]
    linear_combination hsec
  case hg2 =>
    intro r hr
    obtain ⟨_, _, _, hg2, _⟩ := hfacts r (by omega)
    simp only [XAr, XPr, L1r, L2r, YADr] at hg2
    -- `hg2`'s RHS is `YADr r + YADr (r+1)`; the `r+1` branch is derived when `r < n+1`,
    -- the witnessed-final form when `r+1 = n+1`. `linear_combination` after matching the ifs.
    by_cases hrn : r + 1 = n + 1
    · simp only [hYAD, if_pos hrn, if_neg (show ¬(r = n + 1) by omega), hXA, hXP, hL1, hL2]
      simp only [if_pos hrn, if_neg (show ¬(r = n + 1) by omega)] at hg2
      linear_combination hg2
    · simp only [hYAD, if_neg hrn, if_neg (show ¬(r = n + 1) by omega), hXA, hXP, hL1, hL2]
      simp only [if_neg hrn, if_neg (show ¬(r = n + 1) by omega)] at hg2
      linear_combination hg2
  refine ⟨?_, ?_⟩
  · have h := haux.1; rw [hXA] at h; simpa using h
  · have h := haux.2
    simp only [hYAD, if_pos rfl] at h
    linear_combination h

/-- **z-chain lemma (soundness).** Under the loop constraints and the starting `z` copy, each
running-sum cell satisfies `z_{r} = 2·z_{r-1} + k_r` with `k_r ∈ {0,1}` — the chain the `Spec`'s
running-sum conjunct exposes. Stated fully; proof deferred (mechanical, from each round's
`bool_check` gate constraint). -/
theorem loop_zchain_sound (cfg : Config) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset n : ℕ)
    (hz0 : adv cfg.z place self env offset = input.z.eval place env)
    (hLoop : RegionOperations.Constraints place self env
      ((loop cfg input ebits offset n (n + 1)).operations self)) :
    ∃ bits' : BitsHint,
      -- per-round bit-match (the shape `loop_acc_sound.hbit` consumes)
      (∀ r, r ≤ n → adv cfg.z place self env (offset + 1 + r)
        - adv cfg.z place self env (offset + r) * 2 = (if bits' r then 1 else 0)) ∧
      adv cfg.z place self env (offset + 1)
        = 2 * input.z.eval place env + (if bits' 0 then 1 else 0) ∧
      ∀ r : Fin n, adv cfg.z place self env (offset + 1 + (r.val + 1))
        = 2 * adv cfg.z place self env (offset + 1 + r.val)
          + (if bits' (r.val + 1) then 1 else 0) := by
  have hfacts := loop_gate_facts cfg input ebits place self env offset n (n + 1) le_rfl hLoop
  -- the bit read off the running sum at each round, decided into a `BitsHint`
  refine ⟨fun j => decide (adv cfg.z place self env (offset + 1 + j)
      = 2 * adv cfg.z place self env (offset + j) + 1), ?_, ?_, ?_⟩
  · -- the `hbit` per-round match: from each round's `bool_check` (`IsBool (Kr …)`).
    intro r hr
    have hb := (hfacts r (by omega)).1
    simp only [Kr, Zr, Zpr] at hb ⊢
    split_ifs with hd
    · rw [decide_eq_true_eq] at hd
      rcases hb with h | h
      · exact absurd hd (fun hc => one_ne_zero (α := Fp) (by linear_combination h - hc))
      · linear_combination h
    · rcases hb with h | h
      · linear_combination h
      · exact absurd (by rw [decide_eq_true_eq]; linear_combination h) hd
  · -- round 0: `z`-prev is the start-copy `adv z offset = input.z.eval`
    have hb := (hfacts 0 (by omega)).1
    simp only [Kr, Zr, Zpr, Nat.add_zero] at hb ⊢
    split_ifs with hd
    · rw [decide_eq_true_eq] at hd
      rcases hb with h | h
      · exact absurd hd (fun hc => one_ne_zero (α := Fp) (by linear_combination h - hc))
      · linear_combination h + 2 * hz0
    · rcases hb with h | h
      · linear_combination h + 2 * hz0
      · exact absurd (by rw [decide_eq_true_eq]; linear_combination h) hd
  · intro r
    have hb := (hfacts (r.val + 1) (by omega)).1
    simp only [Kr, Zr, Zpr] at hb ⊢
    -- the round's `z`-prev cell is at `offset + (r+1)`; the goal spells it `offset + 1 + r`
    rw [show offset + 1 + r.val = offset + (r.val + 1) from by omega]
    split_ifs with hd
    · rw [decide_eq_true_eq] at hd
      rcases hb with h | h
      · exact absurd hd (by intro hc; exact one_ne_zero (α := Fp) (by linear_combination h - hc))
      · linear_combination h
    · rcases hb with h | h
      · linear_combination h
      · exact absurd (by rw [decide_eq_true_eq]; linear_combination h) hd

/-- **Honest row values (completeness).** The honest prover's `ExtendsWitnesses` of the loop pins
every row's `z`/`x_p`/`y_p`/`λ₁`/`λ₂`/`x_a(next)` cell to the donor's honest value
(`zRunValue`/`rowLambdaValue`/`accVal`), by induction over rounds. Standalone (in the raw
`input.*.eval` spelling) because a round's gate reads cells witnessed by *other* rounds
(`z`-predecessor, next-row constancy cells), and because the bundle completeness re-reads row 0
(for the `q_mul_1` gate) and the output rows off the same witnesses. -/
private theorem loop_row_values (cfg : Config) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment Fp) (offset n : ℕ) :
    ∀ numRounds : ℕ, numRounds ≤ n + 1 →
    RegionOperations.ExtendsWitnesses place self env
      ((loop cfg input ebits offset n numRounds).operations self) →
    ∀ r, r < numRounds →
      adv cfg.z place self env.toEnvironment (offset + 1 + r)
          = zRunValue (input.z.eval place env.toEnvironment) (ebits ⟨place, env⟩) r ∧
      adv cfg.xP place self env.toEnvironment (offset + 1 + r)
          = input.base.x.eval place env.toEnvironment ∧
      adv cfg.yP place self env.toEnvironment (offset + 1 + r)
          = input.base.y.eval place env.toEnvironment ∧
      adv cfg.lambda1 place self env.toEnvironment (offset + 1 + r)
          = (rowLambdaValue (input.base.x.eval place env.toEnvironment)
              (input.base.y.eval place env.toEnvironment) (input.xA.eval place env.toEnvironment)
              (input.yA.eval place env.toEnvironment) (ebits ⟨place, env⟩) r).lambda1 ∧
      adv cfg.lambda2 place self env.toEnvironment (offset + 1 + r)
          = (rowLambdaValue (input.base.x.eval place env.toEnvironment)
              (input.base.y.eval place env.toEnvironment) (input.xA.eval place env.toEnvironment)
              (input.yA.eval place env.toEnvironment) (ebits ⟨place, env⟩) r).lambda2 ∧
      adv cfg.xA place self env.toEnvironment (offset + 1 + (r + 1))
          = (accVal (input.base.x.eval place env.toEnvironment)
              (input.base.y.eval place env.toEnvironment) (input.xA.eval place env.toEnvironment)
              (input.yA.eval place env.toEnvironment) (ebits ⟨place, env⟩) (r + 1)).1 := by
  intro numRounds
  induction numRounds with
  | zero => intro _ _ r hr; omega
  | succ k ih =>
    intro hkb hW r hr
    rw [loop_operations_succ, RegionOperations.extendsWitnesses_append] at hW
    obtain ⟨hWloop, hWround⟩ := hW
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr' | rfl
    · exact ih (by omega) hWloop r hr'
    · -- the fresh round `r`'s own assignAdvice/copyAdvice witnesses (`r = 0`'s anchor copy and
      -- the interior assignment both reduce to the same honest value equations)
      simp only [adv, show offset + 1 + (r + 1) = offset + 1 + r + 1 from by omega]
      by_cases hr0 : r = 0 <;>
        [ simp only [round, hr0, circuit_norm, zWit, l1Wit, l2Wit, xANextWit, readCell,
            AssignedCell.eval, Witgen.WitgenIROver.eval, Witgen.WitgenIROver.ofFExpr,
            Witgen.VExprOver.eval, Witgen.evalSteps, reduceIte] at hWround ⊢;
          simp only [round, circuit_norm, zWit, l1Wit, l2Wit, xANextWit, readCell,
            AssignedCell.eval, Witgen.WitgenIROver.eval, Witgen.WitgenIROver.ofFExpr,
            Witgen.VExprOver.eval, Witgen.evalSteps, if_neg hr0] at hWround ⊢ ] <;>
        exact ⟨hWround.1, hWround.2.1, hWround.2.2.1, hWround.2.2.2.1,
          hWround.2.2.2.2.1, hWround.2.2.2.2.2.1⟩

/-- **Completeness loop lemma.** The honest prover's `ExtendsWitnesses` of the loop pins every
cell to the donor's honest value (`zRunValue`/`rowLambdaValue`/`accVal`), and the loaded round
gates then hold — the `Constraints` half of completeness. Routes into the donor's `honest_step`
/`accVal_eq_nsmul` (imported).

Three cells a round's gate reads live *outside* the loop's own ops, so their honest values are
hypotheses discharged by the bundle from the `startCopies`/final-`y_a` witnesses: the start-`z`
copy (`hz0`, round 0's `bool_check` predecessor), the start-`x_a` copy (`hxA0cell`, row 0's
current accumulator), and the witnessed final `y_a` (`hyAF`, the last round's `Y_A(next)`). -/
theorem loop_constraints_complete (cfg : Config) (input : Inputs (AssignedCell Fp))
    (ebits : Placed ProverEnvironment Fp → BitsHint)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment Fp) (offset n : ℕ)
    (bits : BitsHint) (hbits : bits = ebits ⟨place, env⟩)
    (P : Point Fp) (hP : P.OnCurve)
    (m : ℕ) (h2 : 2 ≤ m) (hbound : 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254)
    (hxA0 : input.xA.eval place env.toEnvironment = (m • P).x)
    (hyA0 : input.yA.eval place env.toEnvironment = (m • P).y)
    (hxPBase : input.base.x.eval place env.toEnvironment = P.x)
    (hyPBase : input.base.y.eval place env.toEnvironment = P.y)
    (hz0 : adv cfg.z place self env.toEnvironment offset = input.z.eval place env.toEnvironment)
    (hxA0cell : adv cfg.xA place self env.toEnvironment (offset + 1)
      = input.xA.eval place env.toEnvironment)
    (hyAF : adv cfg.lambda1 place self env.toEnvironment (offset + 1 + (n + 1))
      = (accVal (input.base.x.eval place env.toEnvironment)
          (input.base.y.eval place env.toEnvironment) (input.xA.eval place env.toEnvironment)
          (input.yA.eval place env.toEnvironment) bits (n + 1)).2)
    (hWit : RegionOperations.ExtendsWitnesses place self env
      ((loop cfg input ebits offset n (n + 1)).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment
      ((loop cfg input ebits offset n (n + 1)).operations self) := by
  -- honest accumulator in point coordinates: `accVal … r = (accScalar r • P)`
  have hAV : ∀ r, r ≤ n + 1 →
      accVal P.x P.y (input.xA.eval place env.toEnvironment)
          (input.yA.eval place env.toEnvironment) bits r
        = ((accScalar m bits r • P).x, (accScalar m bits r • P).y) := by
    rw [hxA0, hyA0]
    exact Orchard.Ecc.Mul.Incomplete.DoubleAndAdd.accVal_eq_nsmul hP bits h2 n hbound
  -- per-row `honest_step` bound (the accumulator's scalar stays in the scalar-field range)
  have hMbound : ∀ r, r ≤ n → 2 * accScalar m bits r + 1 < PALLAS_SCALAR_CARD := by
    intro r hr
    have hMle := accScalar_le (m := m) bits r
    have hpow : 2 ^ r * (m + 1) ≤ 2 ^ (n + 1) * (m + 1) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h254 := pow254_lt_card
    have hsplit : 2 ^ (n + 2) * (m + 1) = 2 * (2 ^ (n + 1) * (m + 1)) := by ring
    have hpos : 0 < 2 ^ r * (m + 1) := by positivity
    omega
  -- the honest row lambda cells in point coordinates
  have hRL : ∀ r, r ≤ n + 1 →
      rowLambdaValue P.x P.y (input.xA.eval place env.toEnvironment)
          (input.yA.eval place env.toEnvironment) bits r
        = lambdaCellsValue P.x P.y (accScalar m bits r • P).x (accScalar m bits r • P).y (bits r) := by
    intro r hr; simp only [rowLambdaValue, hAV r hr]
  -- the honest running-sum step in subtraction form
  have hZB : ∀ (z : Fp) (r : ℕ), zRunValue z bits r
      - (if r = 0 then z else zRunValue z bits (r - 1)) * 2 = (if bits r then 1 else 0) := by
    intro z r
    rcases r with _ | r'
    · rw [if_pos rfl]
      show 2 * z + (if bits 0 then 1 else 0) - z * 2 = _
      rcases Bool.dichotomy (bits 0) with hb | hb <;> rw [hb] <;> norm_num <;> ring
    · rw [if_neg (Nat.succ_ne_zero r'), Nat.add_sub_cancel]
      show 2 * zRunValue z bits r' + (if bits (r' + 1) then 1 else 0)
        - zRunValue z bits r' * 2 = _
      rcases Bool.dichotomy (bits (r' + 1)) with hb | hb <;> rw [hb] <;> norm_num <;> ring
  -- the witnessed final `y_a`, in point coordinates
  have hyAF' : adv cfg.lambda1 place self env.toEnvironment (offset + 1 + (n + 1))
      = (accScalar m bits (n + 1) • P).y := by
    rw [hyAF, hxPBase, hyPBase, hAV (n + 1) le_rfl]
  -- **global** honest cell values (`loop_row_values`), rewritten to `P`-coordinates. Needed
  -- because a round's gate reads cells (`z`-predecessor, next-row `x_p`/`y_p`/`x_a`) witnessed
  -- by *other* rounds.
  have hRowVals : ∀ numRounds : ℕ, numRounds ≤ n + 1 →
      RegionOperations.ExtendsWitnesses place self env
        ((loop cfg input ebits offset n numRounds).operations self) →
      ∀ r, r < numRounds →
        adv cfg.z place self env.toEnvironment (offset + 1 + r)
            = zRunValue (input.z.eval place env.toEnvironment) bits r ∧
        adv cfg.xP place self env.toEnvironment (offset + 1 + r) = P.x ∧
        adv cfg.yP place self env.toEnvironment (offset + 1 + r) = P.y ∧
        adv cfg.lambda1 place self env.toEnvironment (offset + 1 + r)
            = (rowLambdaValue P.x P.y (input.xA.eval place env.toEnvironment)
                (input.yA.eval place env.toEnvironment) bits r).lambda1 ∧
        adv cfg.lambda2 place self env.toEnvironment (offset + 1 + r)
            = (rowLambdaValue P.x P.y (input.xA.eval place env.toEnvironment)
                (input.yA.eval place env.toEnvironment) bits r).lambda2 ∧
        adv cfg.xA place self env.toEnvironment (offset + 1 + (r + 1))
            = (accVal P.x P.y (input.xA.eval place env.toEnvironment)
                (input.yA.eval place env.toEnvironment) bits (r + 1)).1 := by
    intro numRounds h1 hW r hr
    obtain ⟨h1', h2', h3', h4', h5', h6'⟩ :=
      loop_row_values cfg input ebits place self env offset n numRounds h1 hW r hr
    rw [← hbits] at h1' h4' h5' h6'
    rw [hxPBase] at h2'; rw [hyPBase] at h3'
    rw [hxPBase, hyPBase] at h4' h5' h6'
    exact ⟨h1', h2', h3', h4', h5', h6'⟩
  -- the per-round induction, discharging each round's gate constraints
  suffices h : ∀ numRounds : ℕ, numRounds ≤ n + 1 →
      RegionOperations.ExtendsWitnesses place self env
        ((loop cfg input ebits offset n numRounds).operations self) →
      RegionOperations.Constraints place self env.toEnvironment
        ((loop cfg input ebits offset n numRounds).operations self) from h (n + 1) le_rfl hWit
  intro numRounds
  induction numRounds with
  | zero => intro _ _; exact trivial
  | succ k ih =>
    intro hkb hW
    rw [loop_operations_succ, RegionOperations.extendsWitnesses_append] at hW
    rw [loop_operations_succ, RegionOperations.constraints_append]
    obtain ⟨hWloop, _⟩ := hW
    refine ⟨ih (by omega) hWloop, ?_⟩
    -- ══ discharge round `k`'s gate constraints from the honest cells + `honest_step` ══
    -- `2 ≠ 0` lets the gradient closers clear the `TWO_INV = 2⁻¹` in the VK-faithful `y_a`.
    have hp2 : (2 : Fp) ≠ 0 := by decide
    have hkn : k ≤ n := by omega
    -- honest_step at row `k` (accumulator scalar `M := accScalar m bits k`)
    obtain ⟨hHSg1, hHSyad, hHSxnext, hHSg2⟩ :=
      Orchard.Ecc.Mul.Incomplete.DoubleAndAdd.honest_step hP bits
        (accScalar_two_le h2 bits k) (hMbound k hkn) k
    -- fold honest_step's raw `2M + 2k − 1` scalar into `accScalar m bits (k+1)` (definitional)
    rw [show (2 * accScalar m bits k + (if bits k then 1 else 0) * 2 - 1)
        = accScalar m bits (k + 1) from rfl] at hHSxnext hHSg2
    -- the conditionally-negated per-bit `y` (donor `hSy`)
    have hSy : (stepPoint P (bits k)).y = ((if bits k then 1 else 0) * 2 - 1) * P.y := by
      unfold stepPoint
      rcases Bool.dichotomy (bits k) with hb | hb <;> rw [hb]
      · show (-P).y = _; rw [Orchard.Point.neg_y]; norm_num
      · show P.y = _; norm_num
    -- honest cell values of row `k`, in point coordinates
    obtain ⟨hVz, hVxp, hVyp, hVl1, hVl2, hVxa⟩ := hRowVals (n + 1) le_rfl hWit k (by omega)
    rw [hRL k (by omega)] at hVl1 hVl2
    simp only [accVal, hAV k (by omega)] at hVxa
    rw [hHSxnext] at hVxa
    -- `xANext`'s defining identity (the row engine's `x_R` form), donor `hXdef`
    have hXnext' : (accScalar m bits (k + 1) • P).x
        = (lambdaCellsValue P.x P.y (accScalar m bits k • P).x (accScalar m bits k • P).y
            (bits k)).lambda2
          * (lambdaCellsValue P.x P.y (accScalar m bits k • P).x (accScalar m bits k • P).y
              (bits k)).lambda2
          - (accScalar m bits k • P).x
          - ((lambdaCellsValue P.x P.y (accScalar m bits k • P).x (accScalar m bits k • P).y
                (bits k)).lambda1
              * (lambdaCellsValue P.x P.y (accScalar m bits k • P).x (accScalar m bits k • P).y
                  (bits k)).lambda1
              - (accScalar m bits k • P).x - P.x) := hHSxnext.symm.trans rfl
    -- `hHSg2` with `xANext` in point form
    rw [show (lambdaCellsValue P.x P.y (accScalar m bits k • P).x (accScalar m bits k • P).y
        (bits k)).xANext = (accScalar m bits (k + 1) • P).x from hHSxnext] at hHSg2
    -- current-row `x_a` (row 0: the start copy; row `k ≥ 1`: round `k−1`'s next-`x_a` witness)
    have hVXcur : adv cfg.xA place self env.toEnvironment (offset + 1 + k)
        = (accScalar m bits k • P).x := by
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simpa [accScalar] using hxA0cell.trans hxA0
      · have h := (hRowVals (n + 1) le_rfl hWit (k - 1) (by omega)).2.2.2.2.2
        rw [show k - 1 + 1 = k from by omega] at h
        rw [h, hAV k (by omega)]
    -- the honest `z`-step at row `k` (`z_k − 2·z_{k−1} = bit k`)
    have hZprev : adv cfg.z place self env.toEnvironment (offset + k)
        = (if k = 0 then input.z.eval place env.toEnvironment
            else zRunValue (input.z.eval place env.toEnvironment) bits (k - 1)) := by
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · simpa using hz0
      · rw [if_neg (by omega), show offset + k = offset + 1 + (k - 1) from by omega]
        exact (hRowVals (n + 1) le_rfl hWit (k - 1) (by omega)).1
    have hZstep : adv cfg.z place self env.toEnvironment (offset + 1 + k)
        - adv cfg.z place self env.toEnvironment (offset + k) * 2 = (if bits k then 1 else 0) := by
      rw [hVz, hZprev]
      have := hZB (input.z.eval place env.toEnvironment) k
      rcases Nat.eq_zero_or_pos k with rfl | hkpos <;> simpa using this
    -- expose the raw `env.advice` spellings the reduced gate polys use
    simp only [adv] at hVxp hVyp hVl1 hVl2 hVxa hVXcur hZstep hyAF'
    have hzp : ((place self + (offset + 1 + k) : ℕ) : ℤ) - 1
        = ((place self + (offset + k) : ℕ) : ℤ) := by push_cast; ring
    by_cases hrn : k = n
    · -- ── last round: `q_mul_3` (`Y_A(next)` = 2·witnessed final `y_a`; no constancy checks) ──
      subst hrn
      by_cases hr0 : k = 0
      · -- single-round circuit: anchor copies + `q_mul_3` at row 0
        subst hr0
        simp only [Nat.add_zero] at hVxp hVyp hVl1 hVl2 hVXcur hZstep
        simp only [round, circuit_norm, qMul3Gate, forLoopPolys, yA, yAExpr, xRExpr,
          Constraints.withSelector]
        rw [hZstep, hVxp, hVyp, hVl1, hVl2, hVXcur,
          show offset + 2 = offset + 1 + (0 + 1) from by omega, hVxa, hyAF']
        refine ⟨hxPBase.symm, hyPBase.symm, ?_, ?_, ?_, ?_⟩
        · split_ifs <;> ring
        · field_simp; linear_combination -hHSg1 + hHSyad - 2 * hSy
        · linear_combination -hXnext'
        · field_simp; linear_combination 2 * hHSg2 + hHSyad
      · -- last row of a longer run: `q_mul_3` only
        simp only [round, circuit_norm, qMul3Gate, forLoopPolys, yA, yAExpr, xRExpr,
          Constraints.withSelector, if_neg hr0]
        rw [hzp, hZstep, hVxp, hVyp, hVl1, hVl2, hVXcur,
          show offset + 1 + k + 1 = offset + 1 + (k + 1) from by omega, hVxa, hyAF']
        refine ⟨?_, ?_, ?_, ?_⟩
        · split_ifs <;> ring
        · field_simp; linear_combination -hHSg1 + hHSyad - 2 * hSy
        · linear_combination -hXnext'
        · field_simp; linear_combination 2 * hHSg2 + hHSyad
    · -- ── interior round: `q_mul_2` (constancy checks; `Y_A(next)` derived at row `k+1`) ──
      -- next row's honest cells (in-loop, from `hRowVals (k+1)`), in point coordinates
      obtain ⟨_, hVxp1, hVyp1, hVl1', hVl2', _⟩ :=
        hRowVals (n + 1) le_rfl hWit (k + 1) (by omega)
      rw [hRL (k + 1) (by omega)] at hVl1' hVl2'
      -- honest_step at row `k+1` — its `Y_A` identity pins the next row's derived `Y_A`
      obtain ⟨_, hHSyad1, _, _⟩ :=
        Orchard.Ecc.Mul.Incomplete.DoubleAndAdd.honest_step hP bits
          (accScalar_two_le h2 bits (k + 1)) (hMbound (k + 1) (by omega)) (k + 1)
      simp only [adv] at hVxp1 hVyp1 hVl1' hVl2'
      by_cases hr0 : k = 0
      · subst hr0
        simp only [Nat.add_zero] at hVxp hVyp hVl1 hVl2 hVXcur hZstep
        simp only [round, circuit_norm, qMul2Gate, forLoopPolys, yA, yAExpr, xRExpr,
          Constraints.withSelector, if_neg hrn]
        rw [hZstep, hVxp, hVyp, hVl1, hVl2, hVXcur,
          show offset + 2 = offset + 1 + (0 + 1) from by omega, hVxa,
          hVxp1, hVyp1, hVl1', hVl2']
        refine ⟨hxPBase.symm, hyPBase.symm, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · ring
        · ring
        · split_ifs <;> ring
        · field_simp; linear_combination -hHSg1 + hHSyad - 2 * hSy
        · linear_combination -hXnext'
        · field_simp; linear_combination 2 * hHSg2 + hHSyad + hHSyad1
      · simp only [round, circuit_norm, qMul2Gate, forLoopPolys, yA, yAExpr, xRExpr,
          Constraints.withSelector, if_neg hrn, if_neg hr0]
        rw [hzp, hZstep, hVxp, hVyp, hVl1, hVl2, hVXcur,
          show offset + 1 + k + 1 = offset + 1 + (k + 1) from by omega, hVxa,
          hVxp1, hVyp1, hVl1', hVl2']
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · ring
        · ring
        · split_ifs <;> ring
        · field_simp; linear_combination -hHSg1 + hHSyad - 2 * hSy
        · linear_combination -hXnext'
        · field_simp; linear_combination 2 * hHSg2 + hHSyad + hHSyad1

/-! ## The bundle contract

`Spec` exposes the round invariant. `Assumptions`/`ProverAssumptions` are the donor's incomplete-
addition preconditions (base on-curve; `A = [m]P`, `2 ≤ m`, `2^{n+2}(m+1) ≤ 2^{254}`).

There is NO prover-side `bits` parameter (the "no prover information at synthesis" rule). The
working scalar's bits are DERIVED from the scalar cell `input.alpha` inside the witness closures
(`kBits (readCell env input.alpha) (w + ·)`, faithful to Rust `decompose_for_scalar_mul(alpha
.value())`), where `w` is the bundle's window offset (0 for the hi half, 125 for the lo half — the
global bit index of this phase's first round). The verifier-facing `Spec` existentially quantifies
a matching bit sequence; `ProverSpec` pins the honest sequence to `kBits alpha (w + ·)`. -/

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
`n = 124` for the `hi` half and `n = 125` for the `lo` half. Parameterized by the window offset
`w : ℕ` (the global index of this phase's first bit); the witness closures derive each round's bit
from `input.alpha` as `kBits (alpha value) (w + ·)`. The verifier-facing `Spec` existentially
quantifies a matching bit sequence, so soundness does not depend on the prover. -/

/-- The starting-cell copies emitted before the loop (`incomplete.rs:271-290`): the running sum
`z` into `cfg.z` at `offset`, and `y_a` into `cfg.λ₁` at `offset`, and `x_a` into `cfg.x_a` at
`offset + 1`. Split out so `synthesize`'s operation list decomposes cleanly. -/
def startCopies (cfg : Config) (input : Inputs (AssignedCell Fp)) (offset : ℕ) :
    RegionCircuit Fp Unit := do
  let _z ← copyAdvice input.z cfg.z offset
  let _yA ← copyAdvice input.yA cfg.lambda1 offset
  let _xA ← copyAdvice input.xA cfg.xA (offset + 1)
  return ()

def double_and_add (n : ℕ) (w : ℕ) :
    FormalRegionCircuit Fp
      (Column .advice × Column .advice × Column .advice × Column .advice ×
        Column .advice × Column .advice)
      Config Inputs (Output (n + 1)) where
  configure := fun (z, xA, xP, yP, lambda1, lambda2) =>
    configure z xA xP yP lambda1 lambda2

  synthesize cfg offset (input : Inputs (AssignedCell Fp)) := do
    -- starting copies
    startCopies cfg input offset
    -- q_mul_1 at `offset` (outside the loop rows). The per-round selectors q_mul_2 (interior)
    -- and q_mul_3 (last row) are enabled inside `round`, so each round's gate constraints land
    -- in the loop's `Constraints` — the shape the loop lemmas consume by induction.
    (qMul1Gate cfg).enable offset
    -- the per-bit round loop, in the `rangeCheckLoop` shape. The bit family is derived from
    -- the scalar cell `input.alpha` (`bitsOf input w`, i.e. `kBits (alpha value) (w + ·)`),
    -- NOT a prover hint.
    loop cfg input (bitsOf input w) offset n (n + 1)
    -- the witnessed final y_a
    let _yAFinal ← assignAdvice cfg.lambda1 (offset + 1 + (n + 1))
      (yAFinalWit n input (bitsOf input w))
    -- name the output cells (at fixed absolute rows). `cellAt` emits no op, it just names a
    -- cell reference at a known region-local row, so the region index is threaded implicitly.
    let xAOut ← cellAt cfg.xA (offset + 1 + n + 1)
    let yAOut ← cellAt cfg.lambda1 (offset + 1 + (n + 1))
    let zsOut ← cellVec cfg.z (fun r => offset + 1 + r) (n + 1)
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

  -- honest bits are derived from the scalar cell: `kBits alpha (w + ·)` — the same sequence the
  -- witness closures compute via `readCell env input.alpha` (no external `bits` hint).
  ProverSpec input output _ :=
    RoundInvariant n input output (kBitsWindow input.alpha w)

  -- ══ Soundness ══
  -- Framework half (mechanical, TACTIC GAP): `soundness_iff`, then split the synthesize op list
  --   startCopies ++ [q_mul_1] ++ loop ++ [q_mul_2…] ++ [q_mul_3] ++ [final y_a] ++ (output cells)
  -- via `RegionOperations.constraints_append`, land the starting-copy equalities on the input
  -- coords, and read the output cells (fixed rows) off the env. User half: feed the cleaned facts
  -- into `loop_zchain_sound` (running-sum chain) and `loop_acc_sound` (accumulator = `accScalar`),
  -- both of which route into the imported donor algebra. Deferred pending the split/eval tactic.
  soundness := by
    -- loop-based composite: `circuit_proof_start` runs the universal prefix (intro + `soundness_iff`
    -- + house names, the synthesize op-list peel below, and `provable_type_simp`); the folded loop
    -- chunk keeps the goal composite, so the leaf-only finish is skipped and `hc`/`h_input`/
    -- `h_output` survive for the running-sum/accumulator induction below.
    -- peel the synthesize op list: startCopies (3) ++ q_mul_1 ++ loop ++ (output cells, no ops).
    circuit_proof_start [RegionCircuit.operations_bind, RegionCircuit.output_bind,
      operations_copyAdvice, output_cellAt, operations_cellAt, operations_cellVec,
      operations_enable, operations_assignAdvice,
      RegionOperations.constraints_append, startCopies]
    obtain ⟨hCopyZ, hCopyYA, hCopyXA, hQMul1, hLoop⟩ := hc
    -- q_mul_1 gate ⇒ `hInit` (derived `Y_A` of loop row 0 = `2·(λ₁ at offset)`)
    simp only [qMul1Gate, Constraints.withSelector, circuit_norm, yA, yAExpr, xRExpr] at hQMul1
    have hOutXA : output.xA = adv cfg.xA env.place self env.env (offset + 1 + n + 1) := by
      rw [← h_output]; rfl
    have hOutYA : output.yA = adv cfg.lambda1 env.place self env.env (offset + 1 + (n + 1)) := by
      rw [← h_output]; rfl
    have hOutZs : ∀ (i : ℕ) (hi : i < n + 1),
        output.zs[i] = adv cfg.z env.place self env.env (offset + 1 + i) := by
      intro i hi
      rw [← h_output,
        ProvableType.eval_cells (M := fields (n + 1)) { place := env.place, env := env.env } _]
      simp only [ProvableType.eval, ProvableType.toElements, ProvableType.fromElements,
        AssignedCell.of, Cell.of, AssignedCell.eval, Vector.getElem_map, Vector.getElem_ofFn,
        adv, circuit_norm]
    clear h_output
    -- fold `env.advice cfg.col ↑(place self + row)` into `adv` (the loop lemmas' spelling)
    have hadv : ∀ (col : Column .advice) (row : ℕ),
        env.env.advice col ((env.place self + row : ℕ) : ℤ) = adv col env.place self env.env row :=
      fun _ _ => rfl
    simp only [hadv] at hCopyZ hCopyYA hCopyXA hQMul1
    -- reconstruct the input record (as `provable_type_simp` destructured it) so the loop lemmas'
    -- `input` argument matches `hLoop`'s spelling
    set inp : Inputs (AssignedCell Fp) :=
      { alpha := input_var_alpha, base := { x := input_var_base_x, y := input_var_base_y },
        xA := input_var_xA, yA := input_var_yA, z := input_var_z } with hinp
    -- the `input.*.eval` cell reads, resolved to the input values via `h_input`
    obtain ⟨hIalpha, ⟨hBx, hBy⟩, hIxA, hIyA, hIz⟩ := h_input
    -- z-chain + per-round bit match from `loop_zchain_sound` (its `bits'` is the witness)
    obtain ⟨bits', hbit, hz0chain, hzchain⟩ :=
      loop_zchain_sound cfg inp (bitsOf inp w) env.place self env.env offset n hCopyZ hLoop
    refine ⟨bits', ?_, ?_⟩
    · -- running-sum chain conjunct of `RoundInvariant`
      refine ⟨?_, ?_⟩
      · -- z_0 = 2·input.z + bit 0
        rw [hOutZs 0 (by omega)]
        simpa only [Nat.add_zero, hinp, AssignedCell.eval, hIz] using hz0chain
      · intro b
        rw [hOutZs (b.val + 1) (by omega), hOutZs b.val (by omega)]
        exact hzchain b
    · -- accumulator conjunct: route `loop_acc_sound` into `Point.ofCoords`
      intro m hm h2 hbound
      -- the anchor copies pin `x_p`/`y_p` at `offset + 1` to `base.x`/`base.y`
      obtain ⟨hAnchorX, hAnchorY⟩ := loop_anchor cfg inp (bitsOf inp w) env.place self env.env offset n
        (n + 1) (by omega) hLoop
      simp only [hinp, AssignedCell.eval, hBx, hBy] at hAnchorX hAnchorY
      -- the accumulator hypothesis `ofCoords (xA, yA) = m • base` ⇒ coordinate equalities
      have hAccX : input_xA = (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x :=
        congrArg Point.x hm
      have hAccY : input_yA = (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y :=
        congrArg Point.y hm
      have hacc := loop_acc_sound cfg inp (bitsOf inp w) bits' env.place self env.env offset n
        { x := input_base_x, y := input_base_y } hA m h2 hbound
        (by rw [hCopyXA]; simp only [hIxA]; exact hAccX)
        (by rw [hCopyYA]; simp only [hIyA]; exact hAccY)
        hAnchorX hAnchorY hbit
        -- q_mul_1 is now `y_a_witnessed − Y_A(next)·TWO_INV = 0` (VK-faithful, `.scaled 2⁻¹`);
        -- clear the `2⁻¹` (via `2·2⁻¹ = 1`) to recover `Y_A(next) = 2·y_a_witnessed` (`hInit`).
        (by
          have hinv : (2 : Fp) * (2 : Fp)⁻¹ = 1 := mul_inv_cancel₀ (by decide : (2 : Fp) ≠ 0)
          linear_combination (-2 : Fp) * hQMul1
            - (adv cfg.lambda1 env.place self env.env (offset + 1) +
                adv cfg.lambda2 env.place self env.env (offset + 1)) *
              (adv cfg.xA env.place self env.env (offset + 1) -
                (adv cfg.lambda1 env.place self env.env (offset + 1) *
                    adv cfg.lambda1 env.place self env.env (offset + 1)
                  - adv cfg.xA env.place self env.env (offset + 1)
                  - adv cfg.xP env.place self env.env (offset + 1))) * hinv)
        hLoop
      obtain ⟨hx, hy2⟩ := hacc
      -- reconstruct the output point from its coordinates
      have hy : adv cfg.lambda1 env.place self env.env (offset + 1 + (n + 1))
          = (accScalar m bits' (n + 1) • ({ x := input_base_x, y := input_base_y } : Point Fp)).y :=
        mul_left_cancel₀ Orchard.two_ne_zero hy2
      rw [hOutXA, hOutYA, hx, hy]
      -- `ofCoords (p.x, p.y) = p`
      rfl

  -- ══ Completeness ══
  -- Mirrors `soundness`: split the synthesize witness/constraint op list, pin the start copies
  -- and the final `y_a` from their witnesses, discharge the loop via `loop_constraints_complete`
  -- and the `q_mul_1` gate via `honest_step`'s row-0 `Y_A` identity, and read `RoundInvariant`
  -- off the honest row values (`loop_row_values`) + `accVal_eq_nsmul`.
  completeness := by
    -- loop-based composite: the universal prefix (intro + `completeness_iff` + house names, the
    -- witness/op-list peel below, and `provable_type_simp`) runs; the folded loop witness chunk
    -- keeps the goal composite, so the leaf-only finish is skipped and `hwit`/`h_input`/`h_output`/
    -- `hPA` survive for the honest-row induction below.
    circuit_proof_start [RegionCircuit.operations_bind, RegionCircuit.output_bind,
      operations_copyAdvice, output_cellAt, operations_cellAt, operations_cellVec,
      output_cellVec, operations_enable, operations_assignAdvice,
      RegionOperations.extendsWitnesses_append, RegionOperations.constraints_append,
      startCopies, yAFinalWit, readCell,
      Witgen.WitgenIROver.eval, Witgen.WitgenIROver.ofFExpr, Witgen.VExprOver.eval,
      Witgen.evalSteps]
    obtain ⟨hWz, hWyA, hWxA, hWloop, hWyF⟩ := hwit
    -- (`input`/`output` are already destructured — incl. the `zs` vector field inside `h_output` —
    -- by the prefix's `provable_type_simp`, so the output cells read straight off the env)
    have hOutXA : output.xA = adv cfg.xA env.place self env.env (offset + 1 + n + 1) := by
      rw [← h_output]; rfl
    have hOutYA : output.yA = adv cfg.lambda1 env.place self env.env (offset + 1 + (n + 1)) := by
      rw [← h_output]; rfl
    have hOutZs : ∀ (i : ℕ) (hi : i < n + 1),
        output.zs[i] = adv cfg.z env.place self env.env (offset + 1 + i) := by
      intro i hi
      rw [← h_output,
        ProvableType.eval_cells (M := fields (n + 1))
          { place := env.place, env := env.env.toEnvironment } _]
      simp only [ProvableType.eval, ProvableType.toElements, ProvableType.fromElements,
        AssignedCell.of, Cell.of, AssignedCell.eval, Vector.getElem_map, Vector.getElem_ofFn,
        adv, circuit_norm]
    clear h_output
    -- reconstruct the input record (as `provable_type_simp` destructured it) so the loop lemmas'
    -- `input` argument matches `hWloop`'s spelling
    set inp : Inputs (AssignedCell Fp) :=
      { alpha := input_var_alpha, base := { x := input_var_base_x, y := input_var_base_y },
        xA := input_var_xA, yA := input_var_yA, z := input_var_z } with hinp
    obtain ⟨hIalpha, ⟨hBx, hBy⟩, hIxA, hIyA, hIz⟩ := h_input
    obtain ⟨hPbase, m, hm, h2m, hbnd⟩ := hPA
    -- the honest bit sequence: derived from the scalar cell (`ProverSpec` target), and equal to
    -- the family the witness closures compute (`bitsOf inp w`, at this placed environment)
    set bits : BitsHint := kBitsWindow input_alpha w with hbitsdef
    have hbits : bits = bitsOf inp w ⟨env.place, env.env⟩ :=
      congrArg (fun a => kBitsWindow a w) hIalpha.symm
    rw [← hbits] at hWyF
    have hAccX : input_xA = (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x :=
      congrArg Point.x hm
    have hAccY : input_yA = (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y :=
      congrArg Point.y hm
    -- the honest row values (the loop witnesses), with the input reads resolved, folded onto
    -- the honest `bits` (the opaque-family occurrences rewritten via `hbits`)
    have hRows := loop_row_values cfg inp (bitsOf inp w) env.place self env.env offset n (n + 1)
      le_rfl hWloop
    simp only [← hbits] at hRows
    -- expose the raw `env.advice` spellings everywhere
    simp only [adv] at hOutXA hOutYA hOutZs
    -- the scalar-field bound at row 0 (`2m + 1 < |scalar field|`), from the range assumption
    have hMb0 : 2 * m + 1 < PALLAS_SCALAR_CARD := by
      have h254 := pow254_lt_card
      have hsplit : 2 ^ (n + 2) * (m + 1) = 2 * (2 ^ (n + 1) * (m + 1)) := by ring
      have hpow : m + 1 ≤ 2 ^ (n + 1) * (m + 1) :=
        Nat.le_mul_of_pos_left _ (by positivity)
      omega
    -- `honest_step` at row 0: its `Y_A` identity is exactly the `q_mul_1` gate (ascribed with the
    -- base coordinates spelled as the destructured values; definitional)
    have hHS0yad : 2 * (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y
        = ((lambdaCellsValue input_base_x input_base_y
              (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x
              (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y (bits 0)).lambda1
            + (lambdaCellsValue input_base_x input_base_y
                (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x
                (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y (bits 0)).lambda2)
          * ((m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x
            - ((lambdaCellsValue input_base_x input_base_y
                  (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x
                  (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y (bits 0)).lambda1
                * (lambdaCellsValue input_base_x input_base_y
                    (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x
                    (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).y (bits 0)).lambda1
                - (m • ({ x := input_base_x, y := input_base_y } : Point Fp)).x - input_base_x)) :=
      (Orchard.Ecc.Mul.Incomplete.DoubleAndAdd.honest_step hPbase bits h2m hMb0 0).2.1
    -- row-0 honest cells, resolved to the destructured input values and point coordinates
    obtain ⟨_, hR0xp, _, hR0l1, hR0l2, _⟩ := hRows 0 (by omega)
    simp only [hinp, adv, AssignedCell.eval, hBx, hBy, hIxA, hIyA, Nat.add_zero,
      rowLambdaValue, accVal] at hR0xp hR0l1 hR0l2
    rw [hAccX, hAccY] at hR0l1 hR0l2
    refine ⟨⟨hWz, hWyA, hWxA, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · -- ── the `q_mul_1` gate: `y_a(copied) = Y_A(row 0)·TWO_INV`, the honest-row `Y_A` identity ──
      simp only [qMul1Gate, Constraints.withSelector, circuit_norm, yA, yAExpr, xRExpr]
      rw [hWyA, hIyA, hAccY, hR0l1, hR0l2, hWxA, hIxA, hAccX, hR0xp]
      -- VK-faithful gate carries `.scaled … TWO_INV`; clear it (needs `2 ≠ 0`).
      have hp2 : (2 : Fp) ≠ 0 := by decide
      field_simp
      linear_combination hHS0yad
    · -- ── the loop's `Constraints`: `loop_constraints_complete` on the honest start values ──
      exact loop_constraints_complete cfg inp (bitsOf inp w) env.place self env.env offset n
        bits hbits { x := input_base_x, y := input_base_y } hPbase m h2m hbnd
        (by simp only [hinp, AssignedCell.eval, hIxA]; exact hAccX)
        (by simp only [hinp, AssignedCell.eval, hIyA]; exact hAccY)
        (by simp only [hinp, AssignedCell.eval, hBx])
        (by simp only [hinp, AssignedCell.eval, hBy])
        (by simp only [adv, hinp, AssignedCell.eval]; exact hWz)
        (by simp only [adv, hinp, AssignedCell.eval]; exact hWxA)
        (by simp only [adv, hinp, AssignedCell.eval]; exact hWyF)
        hWloop
    · -- ── `RoundInvariant`, z-chain conjunct, round 0 ──
      rw [hOutZs 0 (by omega)]
      have h := (hRows 0 (by omega)).1
      simp only [hinp, adv, AssignedCell.eval, hIz] at h
      rw [h]
      rfl
    · -- ── z-chain conjunct, interior rounds ──
      intro b
      rw [hOutZs (b.val + 1) (by omega), hOutZs b.val (by omega)]
      have h1 := (hRows (b.val + 1) (by omega)).1
      have h0 := (hRows b.val (by omega)).1
      simp only [hinp, adv, AssignedCell.eval, hIz] at h1 h0
      rw [h1, h0]
      rfl
    · -- ── `RoundInvariant`, accumulator conjunct: `accVal_eq_nsmul` on the output cells ──
      intro m' hm' h2' hbnd'
      have hAccX' : input_xA = (m' • ({ x := input_base_x, y := input_base_y } : Point Fp)).x :=
        congrArg Point.x hm'
      have hAccY' : input_yA = (m' • ({ x := input_base_x, y := input_base_y } : Point Fp)).y :=
        congrArg Point.y hm'
      -- the honest accumulator after `n + 1` rounds, in point coordinates (ascribed; definitional)
      have hAV' : accVal input_base_x input_base_y
            (m' • ({ x := input_base_x, y := input_base_y } : Point Fp)).x
            (m' • ({ x := input_base_x, y := input_base_y } : Point Fp)).y bits (n + 1)
          = ((accScalar m' bits (n + 1) • ({ x := input_base_x, y := input_base_y } : Point Fp)).x,
             (accScalar m' bits (n + 1) • ({ x := input_base_x, y := input_base_y } : Point Fp)).y) :=
        Orchard.Ecc.Mul.Incomplete.DoubleAndAdd.accVal_eq_nsmul hPbase bits h2' n hbnd'
          (n + 1) le_rfl
      -- output `x_a`: the last round's next-`x_a` witness
      have hx := (hRows n (by omega)).2.2.2.2.2
      simp only [hinp, adv, AssignedCell.eval, hBx, hBy, hIxA, hIyA] at hx
      rw [hAccX', hAccY', hAV'] at hx
      -- output `y_a`: the witnessed final `y_a`
      rw [hBx, hBy, hIxA, hIyA, hAccX', hAccY', hAV'] at hWyF
      rw [hOutXA, hOutYA, show offset + 1 + n + 1 = offset + 1 + (n + 1) from by omega, hx, hWyF]
      rfl

end Halo2.Ironwood.Ecc.MulIncomplete
