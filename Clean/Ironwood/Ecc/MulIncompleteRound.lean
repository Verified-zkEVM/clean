import Clean.Halo2
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.DoubleAndAdd
import Clean.Ironwood.Ecc.MulIncompleteTheorems
import Clean.Ironwood.Ecc.MulAssignTheorems
import Clean.Halo2.CircuitTypeDeriving

/-!
Variable-base scalar multiplication, *incomplete* phase. For each scalar bit, one merged
double-and-add round over the `x_a / x_p / λ₁ / λ₂` column layout, with `q_mul` selectors at three
rotations, a running `z` column (`z_i = 2·z_{i+1} + k_i`), and the round relation
`acc_{i+1} = (acc_i + (2k−1)P) + acc_i` (specialized round gate `Y_A = (λ₁+λ₂)(x_A − x_R)`).

Generic over the bit count `n + 1`: the `hi`/`lo` halves of `mul.rs` are two instantiations of this
one `Config`, differing only in the advice columns and `NUM_BITS` (125 / 126).

The value-level `Fp`/`Point` algebra lives in `Halo2.Ironwood.Ecc.Mul.Incomplete`; the framework
wiring (`Config`/gates/`configure`, the `synthesize` loop, the `FormalRegionCircuit` bundle) is
here.

Reference: `halo2_gadgets/src/ecc/chip/mul/incomplete.rs`.
-/

namespace Halo2.Ironwood.Ecc.MulIncomplete

open Halo2.Ironwood (Point)
open Halo2.Ironwood.Ecc (DoubleAndAddRow)
open Halo2.Ironwood.Ecc.Mul (kBits kNat tQNat)
open Halo2.Ironwood.Ecc.Mul.Incomplete.DoubleAndAdd
  (accScalar zRunValue stepPoint accVal lambdaCellsValue rowLambdaValue
   accScalar_two_le accScalar_le pow254_lt_card step_nsmul honest_step)
open CompElliptic.Fields.Pasta (PALLAS_SCALAR_CARD)

/-! ## Config

Rust `incomplete::Config<NUM_BITS>`, flattened. `NUM_BITS` is a Rust const generic; here it is the
bit-count parameter `n + 1` on the *bundle*, not a `Config` field. -/

structure Config where
  -- Selector constraining the first row of incomplete addition.
  qMul1 : Selector
  -- Selector constraining the main loop of incomplete addition.
  qMul2 : Selector
  -- Selector constraining the last row of incomplete addition.
  qMul3 : Selector
  -- Cumulative sum used to decompose the scalar.
  z : Column .advice
  -- x-coordinate of the accumulator in each double-and-add iteration.
  xA : Column .advice
  -- note: no `yA` column, it's derived from the lambdas below
  -- x-coordinate of the point being added in each double-and-add iteration.
  xP : Column .advice
  -- y-coordinate of the point being added in each double-and-add iteration.
  yP : Column .advice
  -- lambda1 in each double-and-add iteration.
  lambda1 : Column .advice
  -- lambda2 in each double-and-add iteration.
  lambda2 : Column .advice

/-! ## Gates

One double-and-add iteration per row: `acc' = (acc + (2k−1)·P) + acc`, where `k` is the scalar
bit read off the running sum `z`. The accumulator is `(x_A, y_A)` at the current row, `acc'` the
same at the next row; `P = (x_P, y_P)` is constant on all rows. Only x-coordinates and the two
addition slopes `λ₁, λ₂` get cells: the intermediate point's x is the derived `x_R`, and the
accumulator's y is the derived `y_a = (λ₁ + λ₂)(x_A − x_R) / 2` — so the loop needs no y_a
column, and the boundary gates `q_mul_1`/`q_mul_3` tie the derived form to real cells at the
start/end. -/

/-- `x_R = λ₁² − x_A − x_P` at `rot`. -/
def xRExpr (cfg : Config) (rot : Rotation) : Expression Fp Query :=
  let xA : Expression Fp Query := queryAdvice cfg.xA rot
  let xP : Expression Fp Query := queryAdvice cfg.xP rot
  let l1 : Expression Fp Query := queryAdvice cfg.lambda1 rot
  l1 * l1 - xA - xP

/-- `y_a = (λ₁ + λ₂)(x_A − x_R) · TWO_INV` at `rot`. The trailing `TWO_INV = (2 : Fp)⁻¹` factor
matches the compiled Rust gate (VK-faithful). -/
def yA (cfg : Config) (rot : Rotation) : Expression Fp Query :=
  let xA : Expression Fp Query := queryAdvice cfg.xA rot
  let l1 : Expression Fp Query := queryAdvice cfg.lambda1 rot
  let l2 : Expression Fp Query := queryAdvice cfg.lambda2 rot
  (l1 + l2) * (xA - xRExpr cfg rot) * (2 : Fp)⁻¹

/-- Constraints used for `q_mul_{2,3} == 1`. `yANext` is the next-row `y_a`: derived
(`yA cfg 1`) for `q_mul_2`, the witnessed final `y` for `q_mul_3`. -/
def forLoopPolys (cfg : Config) (yANext : Expression Fp Query) :
    List (String × Expression Fp Query) :=
  -- z_i
  let zCur : Expression Fp Query := queryAdvice cfg.z 0
  -- z_{i+1}
  let zPrev : Expression Fp Query := queryAdvice cfg.z (-1)
  -- x_{A,i}
  let xACur : Expression Fp Query := queryAdvice cfg.xA 0
  -- x_{A,i-1}
  let xANext : Expression Fp Query := queryAdvice cfg.xA 1
  -- x_{P,i}
  let xPCur : Expression Fp Query := queryAdvice cfg.xP 0
  -- y_{P,i}
  let yPCur : Expression Fp Query := queryAdvice cfg.yP 0
  -- λ_{1,i}
  let l1 : Expression Fp Query := queryAdvice cfg.lambda1 0
  -- λ_{2,i}
  let l2 : Expression Fp Query := queryAdvice cfg.lambda2 0
  -- The current bit in the scalar decomposition, k_i = z_i - 2⋅z_{i+1}.
  -- Recall that we assigned the cumulative variable `z_i` in descending order,
  -- i from n down to 0. So z_{i+1} corresponds to the `z_prev` query.
  let k : Expression Fp Query := zCur - zPrev * 2
  -- Check booleanity of decomposition.
  let boolCheck := k * (1 - k)
  -- λ_{1,i}⋅(x_{A,i} − x_{P,i}) − y_{A,i} + (2k_i - 1) y_{P,i} = 0
  let gradient1 := l1 * (xACur - xPCur) - yA cfg 0 + (k * 2 - 1) * yPCur
  -- λ_{2,i}^2 − x_{A,i-1} − x_{R,i} − x_{A,i} = 0
  let secantLine := l2 * l2 - xANext - xRExpr cfg 0 - xACur
  -- λ_{2,i}⋅(x_{A,i} − x_{A,i-1}) − y_{A,i} − y_{A,i-1} = 0
  let gradient2 := l2 * (xACur - xANext) - yA cfg 0 - yANext
  [ ("bool_check", boolCheck),
    ("gradient_1", gradient1),
    ("secant_line", secantLine),
    ("gradient_2", gradient2) ]

/-- The `q_mul_1` gate: the witnessed `y_a` (in the `λ₁` column at the current row) equals the
derived next-row `y_a`. -/
def qMul1Gate (cfg : Config) : Gate Fp where
  name := "q_mul_1 == 1 checks"
  selector := cfg.qMul1
  constraints :=
    let yAWitnessed : Expression Fp Query := queryAdvice cfg.lambda1 0
    Constraints.withSelector cfg.qMul1
      [("init y_a", yAWitnessed - yA cfg 1)]

/-- The `q_mul_2` gate: `x_p`/`y_p` are constant on the next row, plus the shared loop body with the
next-row `y_a` derived. -/
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

/-- The `q_mul_3` gate: the loop body on the last row, with the next-row `y_a` the WITNESSED final
`y` in the `λ₁` column (a bare query, not a derived `Y_A`). -/
def qMul3Gate (cfg : Config) : Gate Fp where
  name := "q_mul_3 == 1 checks"
  selector := cfg.qMul3
  constraints :=
    let yAFinal : Expression Fp Query := queryAdvice cfg.lambda1 1
    Constraints.withSelector cfg.qMul3 (forLoopPolys cfg yAFinal)

/-- Rust `Config::configure`: enable equality on `z` and `λ₁`, allocate the three selectors, and
register the three gates. The columns are handed down by `mul.rs` (different for `hi`/`lo`). -/
def configure (z xA xP yP lambda1 lambda2 : Column .advice) : Configure Fp Config := do
  enableEquality z
  enableEquality lambda1
  let qMul1 ← selector
  let qMul2 ← selector
  let qMul3 ← selector
  let cfg : Config := { qMul1, qMul2, qMul3, z, xA, xP, yP, lambda1, lambda2 }
  createGate (qMul1Gate cfg)
  createGate (qMul2Gate cfg)
  createGate (qMul3Gate cfg)
  return cfg

/-! ## Inputs / Output

Mirrors `DoubleAndAdd.Input`/`Output`, plus the scalar cell `alpha` the bits derive from. -/

/-- Prover-side scalar bits, MSB-first, indexed from the first processed bit. -/
def BitsHint : Type := ℕ → Bool

instance : Inhabited BitsHint := ⟨fun _ => false⟩

/-- The bundle inputs. The working scalar's bits are derived from the cell `alpha`
(`decompose_for_scalar_mul(alpha.value())`); the `round`/`loop` children receive only its
reading *program* (their scalar input is `Unconstrained field`, matching the Rust
`Value` dataflow). -/
structure Inputs (F : Type) where
  -- The scalar's reading program — a prover hint (the Rust source passes it as `Value`);
  -- the scalar cell is NOT constrained by this phase, its bits only enter the running-sum
  -- witnesses.
  alpha : Unconstrained field F
  -- The (non-identity, on-curve) base point.
  base : Point F
  -- The accumulator entering the phase.
  acc : Point F
  -- The running sum entering the phase.
  z : F
deriving CircuitType

/-- The final accumulator cells and the `numBits` interstitial running sums. -/
structure Output (numBits : ℕ) (F : Type) where
  -- The final accumulator.
  acc : Point F
  -- The interstitial running sums.
  zs : Vector F numBits
deriving ProvableStruct

-- `readCell` (reading an input cell in a prover env) lives in the framework (`Basic.lean`).

/-- The `w`-shifted window of the working scalar's bits: `kBitsWindow a w i = kBits a (w + i)`,
i.e. bit `k_{254-(w+i)}` of the unreduced working scalar `k = a.val + t_q`.

KERNEL-SAFETY (load-bearing spelling): `t_q` is added on the LEFT (`tQNat + a.val`, flipped vs
`kNat`). `Nat.add` recurses on its SECOND argument, so with the ~2^125 literal on the left
kernel whnf is stuck immediately on the abstract `a.val` — the `kNat` spelling would unfold the
literal unarily ("(kernel) deep recursion detected"). Bridge to `kBits` via
`kBitsWindow_eq_kBits`, a rewrite, never a defeq. -/
def kBitsWindow (a : Fp) (w : ℕ) : BitsHint :=
  fun i => (tQNat + a.val).testBit (254 - (w + i))

/-- `kBitsWindow` is the `w`-shifted window of `kBits`. -/
theorem kBitsWindow_eq_kBits (a : Fp) (w i : ℕ) :
    kBitsWindow a w i = kBits a (w + i) := by
  unfold kBitsWindow kBits kNat
  rw [Nat.add_comm]

/-- `kBitsWindow` as a `kBits` lambda. -/
theorem kBitsWindow_as_kBits (a : Fp) (w : ℕ) :
    kBitsWindow a w = fun i => kBits a (w + i) :=
  funext fun i => kBitsWindow_eq_kBits a w i

/-- The zero-offset window is exactly `kBits`. -/
theorem kBitsWindow_zero (a : Fp) : kBitsWindow a 0 = kBits a :=
  funext fun i => by rw [kBitsWindow_eq_kBits, Nat.zero_add]

/-! ## The double-and-add state

One row of the loop's positional state: the previous running sum, and the current row's
accumulator/base cells. The accumulator's y has no cell; it is virtually represented by
`(λ₁, λ₂, x_A, x_P)` (see `State.yA2`). -/

structure State (F : Type) where
  -- Running sum, one row above the accumulator cells.
  z : F
  -- x-coordinate of the accumulator.
  xA : F
  -- Slope cells whose combination represents the accumulator's y.
  lambda1 : F
  lambda2 : F
  -- The base point (x_p / y_p columns).
  base : Point F
deriving ProvableStruct

/-- `x_R = λ₁² − x_A − x_P` of the state's row. -/
def State.xR (s : State Fp) : Fp := s.lambda1 * s.lambda1 - s.xA - s.base.x

/-- `2·y_A = (λ₁ + λ₂)(x_A − x_R)`: the doubled virtual y of the accumulator. -/
def State.yA2 (s : State Fp) : Fp := (s.lambda1 + s.lambda2) * (s.xA - s.xR)

/-- The accumulator point of a state. -/
def State.acc (s : State Fp) : Point Fp := { x := s.xA, y := s.yA2 * (2 : Fp)⁻¹ }

/-- The state is the honest row for accumulator multiple `m` and scalar bit `k`: on-curve
base, accumulator `[m]·base` in the exceptional-case-free range (one step of headroom —
the gate reads the *next* row's derived y, an honesty fact about `2m ± 1`), and the true
double-and-add slopes for bit `k`. -/
def State.Honest (s : State Fp) (m : ℕ) (k : Bool) : Prop :=
  s.base.OnCurve ∧ 2 ≤ m ∧ 4 * m + 3 < PALLAS_SCALAR_CARD ∧
  s.xA = (m • s.base).x ∧
  s.lambda1 = (lambdaCellsValue s.base.x s.base.y (m • s.base).x (m • s.base).y k).lambda1 ∧
  s.lambda2 = (lambdaCellsValue s.base.x s.base.y (m • s.base).x (m • s.base).y k).lambda2

/-- The honest next state: the Rust iteration's assignment formulas over the current row's
cells. `k` is this round's scalar bit, `k'` the next round's (the next row's λ's are the
*following* round's slopes — the price of the virtual-y representation). -/
def State.step (s : State Fp) (k k' : Bool) : State Fp :=
  let xANew := s.lambda2 * s.lambda2 - s.xR - s.xA
  let yANew := s.lambda2 * (s.xA - xANew) - s.yA2 * (2 : Fp)⁻¹
  let l := lambdaCellsValue s.base.x s.base.y xANew yANew k'
  { z := 2 * s.z + (if k then 1 else 0)
    xA := xANew
    lambda1 := l.lambda1
    lambda2 := l.lambda2
    base := s.base }

/-- Iterated honest steps: the state after `r` rounds starting at bit index 0 of `bits`. -/
def State.iter (s : State Fp) (bits : ℕ → Bool) : ℕ → State Fp
  | 0 => s
  | r + 1 => (s.iter bits r).step (bits r) (bits (r + 1))

/-- The scalar's bit family from the cell value, at window offset `w`. -/
def bitsFrom (alpha : Fp) (w : ℕ) : ℕ → Bool :=
  fun j => kBitsWindow alpha 0 (w + j)

/-- The running-sum chain: each interstitial `z` doubles its predecessor and absorbs a bit. -/
def zChain {n : ℕ} (zIn : Fp) (zs : Vector Fp n) (bits : ℕ → Bool) : Prop :=
  ∀ j : Fin n, zs[j] = 2 * (if h : j.val = 0 then zIn else zs[j.val - 1]) +
    (if bits j.val then 1 else 0)

/-! ## The round bundle

One interior double-and-add round, as a formal circuit sharing the parent's `Config`. Its
gate reads the *adjacent* cells of the previous round — a positional neighborhood, not an
`Input` — so those live in the `Witness`/`extract` slot: `reads` is the public positional
interface, and `Spec`/`ProverAssumptions` are stated over its values. The only genuine
input is the scalar cell `alpha` (bit source for the witnesses). -/

/-- The adjacent cells round `i`'s gate reads but does not own: the previous running sum at
the round's own `offset`, and the accumulator/base cells at the gate row `offset + 1`
(assigned by the previous round, or by `double_and_add`'s init block). The round's output
state is `reads cfg (offset + 1)` — the next round's neighborhood, chaining by `rfl`. -/
def reads (cfg : Config) (offset : ℕ) (self : RegionIndex) : State (AssignedCell Fp) where
  z := .of self offset cfg.z
  xA := .of self (offset + 1) cfg.xA
  lambda1 := .of self (offset + 1) cfg.lambda1
  lambda2 := .of self (offset + 1) cfg.lambda2
  base := { x := .of self (offset + 1) cfg.xP, y := .of self (offset + 1) cfg.yP }

/-- Name the neighborhood cells inside `synthesize` (no ops emitted). -/
def readState (cfg : Config) (offset : ℕ) : RegionCircuit Fp (State (AssignedCell Fp)) :=
  fun self => (reads cfg offset self, [])

@[circuit_norm]
theorem operations_readState (cfg : Config) (offset : ℕ) (self : RegionIndex) :
    (readState cfg offset).operations self = [] := rfl

@[circuit_norm]
theorem output_readState (cfg : Config) (offset : ℕ) (self : RegionIndex) :
    (readState cfg offset).output self = reads cfg offset self := rfl

/-- Bit `i` of the working scalar, from the scalar's witness program (the prover-only
`Value` the Rust source decomposes). -/
def bitWit (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) (i : ℕ)
    (env : Placed ProverEnvironment Fp) : Bool :=
  kBitsWindow (Witgen.MOver.eval (value := field) env alpha) 0 i

/-- The bit closure, over the program's evaluation (the spelling `h_input` lands on). -/
@[circuit_norm]
theorem bitWit_eval (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp)) (i : ℕ)
    (env : Placed ProverEnvironment Fp) :
    bitWit alpha i env
      = kBitsWindow (Witgen.MOver.eval (value := field) env alpha) 0 i := rfl

/-- The neighborhood values in a prover environment. -/
@[circuit_norm]
def readsValue (w : State (AssignedCell Fp)) (env : Placed ProverEnvironment Fp) : State Fp where
  z := readCell env w.z
  xA := readCell env w.xA
  lambda1 := readCell env w.lambda1
  lambda2 := readCell env w.lambda2
  base := { x := readCell env w.base.x, y := readCell env w.base.y }

-- TODO make all these witness programs non-native (exportable IR instead of `.native`
-- closures). Prerequisites: the `Witgen.M` let-step builder monad (the λ-formulas need
-- shared intermediates; `Clean/Halo2/WitnessIR.lean` defers that port), plus
-- `UnconstrainedNat` and vector-level IR hints for the bit decomposition
-- (`kBitsWindow` is Nat-level: `(tQNat + a.val).testBit …` — NExpr has
-- shiftR/land/mod, so it is expressible once the builder lands).

/-- The y-coordinate the step leaves at the new accumulator (bit-free: the second
addition's y-law over the current row's cells) — the value the final row witnesses. -/
def State.stepY (s : State Fp) : Fp :=
  s.lambda2 * (s.xA - (s.lambda2 * s.lambda2 - (s.lambda1 * s.lambda1 - s.xA - s.base.x)
    - s.xA)) - s.yA2 * (2 : Fp)⁻¹

/-- Honest witness reading a function of the neighborhood (no step). -/
def readWit (w : State (AssignedCell Fp)) (f : State Fp → Fp) : WitgenIR Fp 1 :=
  .native fun env => #v[f (readsValue w env)]

@[circuit_norm]
theorem readWit_eval (w : State (AssignedCell Fp)) (f : State Fp → Fp)
    (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    ((readWit w f).eval env)[j] = f (readsValue w env) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [readWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-- Honest witness for one output cell of round `i`: the corresponding field of
`State.step` over the neighborhood readings. -/
def stepWit (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp))
    (w : State (AssignedCell Fp)) (i : ℕ)
    (f : State Fp → Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    #v[f ((readsValue w env).step (bitWit alpha i env) (bitWit alpha (i + 1) env))]

/-- Evaluation of the round's witness closures, in one step and without exposing the
native-eval plumbing: the peel reduces every assigned value directly to a folded
`step`-projection. (Keyed on `getElem`, per the lazy-vector convention.) -/
@[circuit_norm]
theorem stepWit_eval (alpha : Witgen.MOver Fp (AssignedCell Fp) (FExpr Fp))
    (w : State (AssignedCell Fp)) (i : ℕ)
    (f : State Fp → Fp) (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    ((stepWit alpha w i f).eval env)[j]
      = f ((readsValue w env).step (bitWit alpha i env) (bitWit alpha (i + 1) env)) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [stepWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

@[circuit_norm]
theorem readCell_of (env : Placed ProverEnvironment Fp) (self : RegionIndex) (row : ℕ)
    (col : Column .advice) :
    readCell env (AssignedCell.of self row col)
      = env.env.advice col ((env.place self + row : ℕ) : ℤ) := rfl

/-- The gate identities of one row force the double-and-add step, in point form:
`step_nsmul` + `coordinates_of_constraints` applied to a single constrained row.
Stated over the raw cell values so the bundle's peeled soundness goal unifies with it. -/
private theorem sound_step {z xA l1 l2 bx yb oz oxA ol1 ol2 obx oby : Fp} {obase : Point Fp}
    (hbase : ({ x := obx, y := oby } : Point Fp) = obase)
    (hxpc : bx - obx = 0) (hypc : yb - oby = 0)
    (hbool : (oz - z * 2) * (1 - (oz - z * 2)) = 0)
    (hg1 : l1 * (xA - bx) - (l1 + l2) * (xA - (l1 * l1 - xA - bx)) * (2 : Fp)⁻¹
      + ((oz - z * 2) * 2 - 1) * yb = 0)
    (hsec : l2 * l2 - oxA - (l1 * l1 - xA - bx) - xA = 0)
    (hg2 : l2 * (xA - oxA) - (l1 + l2) * (xA - (l1 * l1 - xA - bx)) * (2 : Fp)⁻¹
      - (ol1 + ol2) * (oxA - (ol1 * ol1 - oxA - obx)) * (2 : Fp)⁻¹ = 0) :
    ∃ k : Bool, oz = 2 * z + (if k then 1 else 0) ∧
      obase = { x := bx, y := yb } ∧
      ∀ m : ℕ, ({ x := bx, y := yb } : Point Fp).OnCurve →
        ({ x := xA, y := (l1 + l2) * (xA - (l1 * l1 - xA - bx)) * (2 : Fp)⁻¹ } : Point Fp)
          = m • { x := bx, y := yb } →
        2 ≤ m → 2 * m + 1 < PALLAS_SCALAR_CARD →
        ({ x := oxA, y := (ol1 + ol2) * (oxA - (ol1 * ol1 - oxA - obase.x)) * (2 : Fp)⁻¹ }
            : Point Fp)
          = (2 * m + (if k then 1 else 0) * 2 - 1) • { x := bx, y := yb } := by
  subst hbase
  have h2 : (2 : Fp) ≠ 0 := by decide
  have hobx : bx = obx := by linear_combination hxpc
  have hoby : yb = oby := by linear_combination hypc
  subst hobx hoby
  -- the shared point-level core, abstracted over the bit value
  have core : ∀ k : Bool, oz - z * 2 = (if k then 1 else 0) →
      ∀ m : ℕ, ({ x := bx, y := yb } : Point Fp).OnCurve →
        ({ x := xA, y := (l1 + l2) * (xA - (l1 * l1 - xA - bx)) * (2 : Fp)⁻¹ } : Point Fp)
          = m • { x := bx, y := yb } →
        2 ≤ m → 2 * m + 1 < PALLAS_SCALAR_CARD →
        ({ x := oxA, y := (ol1 + ol2) * (oxA - (ol1 * ol1 - oxA - bx)) * (2 : Fp)⁻¹ }
            : Point Fp)
          = (2 * m + (if k then 1 else 0) * 2 - 1) • { x := bx, y := yb } := by
    intro k hkv m hOn hacc h2m hMb
    -- abstract the base point: all algebra below is over `P.x`/`P.y` atoms
    obtain ⟨P, hPx, hPy⟩ : ∃ P : Point Fp, P.x = bx ∧ P.y = yb :=
      ⟨{ x := bx, y := yb }, rfl, rfl⟩
    subst hPx hPy
    rw [show ({ x := P.x, y := P.y } : Point Fp) = P from rfl] at hacc hOn ⊢
    have hax : xA = (m • P).x := congrArg Point.x hacc
    have hay : (l1 + l2) * (xA - (l1 * l1 - xA - P.x)) * (2 : Fp)⁻¹ = (m • P).y :=
      congrArg Point.y hacc
    -- the non-degenerate step at the point level
    have hstep := step_nsmul hOn (fun _ => k) h2m hMb 0
    -- the row equations in the lift's shape
    have hXP : P.x = (stepPoint P k).x := by
      unfold stepPoint; rcases k with _ | _ <;> rfl
    have hYP : 2 * (m • P).y - 2 * l1 * ((m • P).x - P.x) = 2 * (stepPoint P k).y := by
      unfold stepPoint
      rcases k with _ | _ <;>
        simp only [Bool.false_eq_true, if_false, if_true] at hkv ⊢
      · show _ = 2 * (-P).y
        rw [Point.neg_y]
        linear_combination (-2) * hg1 - 2 * hay + 2 * l1 * hax + 4 * P.y * hkv
      · show _ = 2 * P.y
        linear_combination (-2) * hg1 - 2 * hay + 2 * l1 * hax + 4 * P.y * hkv
    have hYA : 2 * (m • P).y = (l1 + l2) * ((m • P).x - (l1 * l1 - (m • P).x - P.x)) := by
      rw [← hax]
      linear_combination (norm := (field_simp; ring)) (-2) * hay
    have hSec : l2 * l2 = oxA + (l1 * l1 - (m • P).x - P.x) + (m • P).x := by
      rw [← hax]; linear_combination hsec
    have hYC : 4 * l2 * ((m • P).x - oxA)
        = 4 * (m • P).y + 2 * ((ol1 + ol2) * (oxA - (ol1 * ol1 - oxA - P.x))) := by
      rw [← hax]
      linear_combination (norm := (field_simp; ring)) 4 * hg2 + 4 * hay
    have hstep' : Point.doubleAndAdd (m • P) (stepPoint P k)
        = some ((2 * m + (if k then 1 else 0) * 2 - 1) • P) := hstep
    obtain ⟨hxB, hYB⟩ := Halo2.Ironwood.Ecc.DoubleAndAdd.coordinates_of_constraints
      hstep' hYP hXP hYA hSec hYC
    -- assemble the output point
    have hyB : (ol1 + ol2) * (oxA - (ol1 * ol1 - oxA - P.x)) * (2 : Fp)⁻¹
        = ((2 * m + (if k then 1 else 0) * 2 - 1) • P).y := by
      field_simp
      linear_combination hYB
    rw [hyB, hxB]
  rcases mul_eq_zero.mp hbool with hk | hk
  · exact ⟨false, by simp only [Bool.false_eq_true, if_false]; linear_combination hk,
      rfl, core false (by simp only [Bool.false_eq_true, if_false]; linear_combination hk)⟩
  · exact ⟨true, by simp only [if_true]; linear_combination -hk,
      rfl, core true (by simp only [if_true]; linear_combination -hk)⟩

/-- The step keeps the base point. -/
private theorem step_base (w : State Fp) (k k' : Bool) : (w.step k k').base = w.base := rfl

/-- The step's running sum absorbs the bit. -/
private theorem step_z (w : State Fp) (k k' : Bool) :
    (w.step k k').z = 2 * w.z + (if k then 1 else 0) := rfl

/-- The step's accumulator x, by the secant formula (definitional). -/
private theorem step_xA_eq (w : State Fp) (k k' : Bool) :
    (w.step k k').xA
      = w.lambda2 * w.lambda2 - (w.lambda1 * w.lambda1 - w.xA - w.base.x) - w.xA := rfl

/-- An honest row's derived doubled y is the accumulator's true y. -/
theorem honest_yA2 {w : State Fp} {m : ℕ} {k : Bool} (hH : w.Honest m k) :
    w.yA2 = 2 * (m • w.base).y := by
  obtain ⟨hOn, h2m, hMb, hxA, hl1, hl2⟩ := hH
  have hMb1 : 2 * m + 1 < PALLAS_SCALAR_CARD := by omega
  have hs2 := (honest_step hOn (fun _ => k) h2m hMb1 0).2.1
  simp only [State.yA2, State.xR]
  rw [hxA, hl1, hl2]
  linear_combination -hs2

/-- The step's cells land on the stepped accumulator's coordinates: the identities
(3)/(4) routed through the step formulas. -/
private theorem step_coords {w : State Fp} {m : ℕ} {k : Bool} (k' : Bool)
    (hH : w.Honest m k) :
    (w.step k k').xA = ((2 * m + (if k then 1 else 0) * 2 - 1) • w.base).x ∧
    (w.step k k').lambda1 = (lambdaCellsValue w.base.x w.base.y
      ((2 * m + (if k then 1 else 0) * 2 - 1) • w.base).x
      ((2 * m + (if k then 1 else 0) * 2 - 1) • w.base).y k').lambda1 ∧
    (w.step k k').lambda2 = (lambdaCellsValue w.base.x w.base.y
      ((2 * m + (if k then 1 else 0) * 2 - 1) • w.base).x
      ((2 * m + (if k then 1 else 0) * 2 - 1) • w.base).y k').lambda2 := by
  obtain ⟨hOn, h2m, hMb, hxA, hl1, hl2⟩ := hH
  have h2 : (2 : Fp) ≠ 0 := by decide
  have hMb1 : 2 * m + 1 < PALLAS_SCALAR_CARD := by omega
  obtain ⟨hs1, hs2, hs3, hs4⟩ := honest_step hOn (fun _ => k) h2m hMb1 0
  set P := w.base with hPdef
  set l := lambdaCellsValue P.x P.y (m • P).x (m • P).y k with hldef
  set m' := 2 * m + (if k then 1 else 0) * 2 - 1 with hm'
  have hxan : l.xANext
      = l.lambda2 * l.lambda2 - (l.lambda1 * l.lambda1 - (m • P).x - P.x) - (m • P).x := by
    rw [hldef]; simp only [lambdaCellsValue]; ring
  simp only [State.step, State.xR, State.yA2]
  rw [show w.base = P from hPdef.symm]
  rw [hxA, hl1, hl2]
  have hxanew : l.lambda2 * l.lambda2
      - (l.lambda1 * l.lambda1 - (m • P).x - P.x) - (m • P).x = (m' • P).x :=
    hxan.symm.trans hs3
  have hyanew : l.lambda2 * ((m • P).x
        - (l.lambda2 * l.lambda2 - (l.lambda1 * l.lambda1 - (m • P).x - P.x) - (m • P).x))
      - (l.lambda1 + l.lambda2) * ((m • P).x - (l.lambda1 * l.lambda1 - (m • P).x - P.x))
        * (2 : Fp)⁻¹
      = (m' • P).y := by
    rw [← hxan]
    have h4 := hs4
    field_simp
    linear_combination 2 * h4 + hs2
  exact ⟨hxanew, by rw [hyanew, hxanew], by rw [hyanew, hxanew]⟩

/-- Honesty propagates through the step: the honest row for `(m, k)` steps to the honest
row for `(2m + 2k − 1, k')` — the loop's chaining lemma. -/
private theorem step_honest {w : State Fp} {m : ℕ} {k : Bool} (k' : Bool)
    (hH : w.Honest m k) (hBound' : 4 * (2 * m + (if k then 1 else 0) * 2 - 1) + 3
      < PALLAS_SCALAR_CARD) :
    (w.step k k').Honest (2 * m + (if k then 1 else 0) * 2 - 1) k' := by
  obtain ⟨hc1, hc2, hc3⟩ := step_coords k' hH
  obtain ⟨hOn, h2m, hMb, -, -, -⟩ := hH
  refine ⟨?_, ?_, hBound', ?_, ?_, ?_⟩
  · rw [step_base]; exact hOn
  · rcases k with _ | _ <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
  · rw [hc1, step_base]
  · rw [hc2, step_base]
  · rw [hc3, step_base]

/-- The honest step satisfies the gate polynomials: the completeness counterpart of
`sound_step`, over one row's values. Unfolds `step`/`lambdaCellsValue` exactly once, here —
witgen defs stay folded everywhere else. -/
private theorem step_gates {w : State Fp} {m : ℕ} {k k' : Bool} (hH : w.Honest m k) :
    w.base.x - (w.step k k').base.x = 0 ∧
    w.base.y - (w.step k k').base.y = 0 ∧
    ((w.step k k').z - w.z * 2) * (1 - ((w.step k k').z - w.z * 2)) = 0 ∧
    w.lambda1 * (w.xA - w.base.x)
      - (w.lambda1 + w.lambda2) * (w.xA - (w.lambda1 * w.lambda1 - w.xA - w.base.x)) * (2 : Fp)⁻¹
      + (((w.step k k').z - w.z * 2) * 2 - 1) * w.base.y = 0 ∧
    w.lambda2 * w.lambda2 - (w.step k k').xA
      - (w.lambda1 * w.lambda1 - w.xA - w.base.x) - w.xA = 0 ∧
    w.lambda2 * (w.xA - (w.step k k').xA)
      - (w.lambda1 + w.lambda2) * (w.xA - (w.lambda1 * w.lambda1 - w.xA - w.base.x)) * (2 : Fp)⁻¹
      - ((w.step k k').lambda1 + (w.step k k').lambda2)
          * ((w.step k k').xA - ((w.step k k').lambda1 * (w.step k k').lambda1
              - (w.step k k').xA - (w.step k k').base.x)) * (2 : Fp)⁻¹ = 0 := by
  have hcoords := step_coords k' hH
  obtain ⟨hOn, h2m, hMb, hxA, hl1, hl2⟩ := hH
  have h2 : (2 : Fp) ≠ 0 := by decide
  have hMb1 : 2 * m + 1 < PALLAS_SCALAR_CARD := by omega
  obtain ⟨hs1, hs2, hs3, hs4⟩ := honest_step hOn (fun _ => k) h2m hMb1 0
  set P := w.base with hPdef
  set l := lambdaCellsValue P.x P.y (m • P).x (m • P).y k with hldef
  set m' := 2 * m + (if k then 1 else 0) * 2 - 1 with hm'
  have h2m' : 2 ≤ m' := by
    rcases k with _ | _ <;> simp only [Bool.false_eq_true, if_false, if_true, hm'] <;> omega
  have hMb1' : 2 * m' + 1 < PALLAS_SCALAR_CARD := by
    rcases k with _ | _ <;> simp only [Bool.false_eq_true, if_false, if_true, hm'] <;> omega
  have hs2' := (honest_step hOn (fun _ => k') h2m' hMb1' 0).2.1
  rw [hs3] at hs4
  refine ⟨by rw [step_base]; ring, by rw [step_base]; ring, ?_, ?_, ?_, ?_⟩
  · -- bool_check
    rw [step_z]
    rcases k with _ | _ <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring
  · -- gradient_1
    rw [step_z, hxA, hl1, hl2]
    rcases k with _ | _ <;>
      simp only [Bool.false_eq_true, if_false, if_true] at hs1 ⊢
    · rw [show (stepPoint P false).y = -P.y from by unfold stepPoint; simp [Point.neg_y]] at hs1
      linear_combination (norm := (field_simp; ring))
        (-(2 : Fp)⁻¹) * hs1 + (2 : Fp)⁻¹ * hs2
    · rw [show (stepPoint P true).y = P.y from rfl] at hs1
      linear_combination (norm := (field_simp; ring))
        (-(2 : Fp)⁻¹) * hs1 + (2 : Fp)⁻¹ * hs2
  · -- secant_line
    rw [step_xA_eq, hxA, hl1, hl2]
    ring
  · -- gradient_2
    rw [hcoords.1, hcoords.2.1, hcoords.2.2, step_base]
    rw [show w.base = P from hPdef.symm, hxA, hl1, hl2]
    linear_combination (norm := (field_simp; ring))
      hs4 + (2 : Fp)⁻¹ * hs2 + (2 : Fp)⁻¹ * hs2'

/-- One interior double-and-add round at global bit index `i`. Enables `q_mul_2` at its gate
row `offset + 1`; assigns this row's running sum and the next row's state cells. -/
def round (i : ℕ) : FormalRegionCircuit Fp Config Config (Unconstrained field) State where
  configure := pure

  synthesize cfg offset (alpha : Var (Unconstrained field) Fp) := do
    let w ← readState cfg offset
    (qMul2Gate cfg).enable (offset + 1)
    let _z ← assignAdvice cfg.z (offset + 1) (stepWit alpha w i (·.z))
    let _xA ← assignAdvice cfg.xA (offset + 2) (stepWit alpha w i (·.xA))
    let _l1 ← assignAdvice cfg.lambda1 (offset + 2) (stepWit alpha w i (·.lambda1))
    let _l2 ← assignAdvice cfg.lambda2 (offset + 2) (stepWit alpha w i (·.lambda2))
    let _xP ← assignAdvice cfg.xP (offset + 2) (stepWit alpha w i (·.base.x))
    let _yP ← assignAdvice cfg.yP (offset + 2) (stepWit alpha w i (·.base.y))
    readState cfg (offset + 1)

  Witness := State
  extract cfg offset _ self env := eval env (reads cfg offset self)

  -- One constrained double-and-add step, in point language: some boolean scalar bit `k`
  -- enters the running sum, the base propagates, and — whenever the entering accumulator
  -- is a small multiple of the on-curve base in the exceptional-case-free range — the
  -- outgoing accumulator is `[2m + 2k − 1]·base`.
  Spec _ out w :=
    ∃ k : Bool,
      out.z = 2 * w.z + (if k then 1 else 0) ∧
      out.base = w.base ∧
      ∀ m : ℕ, w.base.OnCurve → w.acc = m • w.base →
        2 ≤ m → 2 * m + 1 < PALLAS_SCALAR_CARD →
        out.acc = (2 * m + (if k then 1 else 0) * 2 - 1) • w.base

  -- Honest neighborhood: the entering row is the honest row for some in-range multiple.
  ProverAssumptions alpha w _ :=
    ∃ m : ℕ, w.Honest m (kBitsWindow alpha 0 i)

  ProverSpec alpha out w _ :=
    out = w.step (kBitsWindow alpha 0 i) (kBitsWindow alpha 0 (i + 1))

  soundness := by
    circuit_proof_start2 [qMul2Gate, forLoopPolys, yA, xRExpr, reads,
      State.acc, State.yA2, State.xR]
    obtain ⟨hxpc, hypc, hbool, hg1, hsec, hg2⟩ := region_0
    obtain ⟨-, -, -, -, hbase⟩ := output_eq
    exact sound_step hbase hxpc hypc hbool hg1 hsec hg2

  completeness := by
    circuit_proof_start2 [qMul2Gate, forLoopPolys, yA, xRExpr, reads]
    obtain ⟨m, hH⟩ := prover_assumptions
    obtain ⟨-, -, -, -, hbase⟩ := output_eq
    -- substitute the witnessed cells: every out-row cell is a field of `w.step`
    simp only [region_0, region_1, region_2, region_3, region_4, region_5, ← hbase]
    exact ⟨step_gates hH, trivial⟩

/-- Witness equations chain into the iterated step. -/
theorem iter_of_steps {n : ℕ} (st : ℕ → State Fp) (bits : ℕ → Bool)
    (hstep : ∀ i : Fin n, st (i.val + 1) = (st i.val).step (bits i.val) (bits (i.val + 1))) :
    ∀ r, r ≤ n → st r = (st 0).iter bits r := by
  intro r hr
  induction r with
  | zero => rfl
  | succ v ih =>
    rw [hstep ⟨v, by omega⟩, ih (by omega)]
    rfl

/-- Honesty chains along the witness equations, with the global budget supplying each
round's headroom. -/
theorem honest_of_steps {n : ℕ} (st : ℕ → State Fp) (bits : ℕ → Bool)
    (hstep : ∀ i : Fin n, st (i.val + 1) = (st i.val).step (bits i.val) (bits (i.val + 1)))
    (m : ℕ) (hH0 : (st 0).Honest m (bits 0))
    (hbudget : 2 ^ (n + 2) * (m + 1) ≤ 2 ^ 254) :
    ∀ r, r ≤ n → (st r).Honest (accScalar m bits r) (bits r) := by
  have h2 : 2 ≤ m := hH0.2.1
  intro r hr
  induction r with
  | zero => exact hH0
  | succ v ih =>
    have hv : v < n := by omega
    have hprev := ih (by omega)
    -- headroom for the stepped multiple, from the global budget
    have hMle : accScalar m bits v ≤ 2 ^ v * (m + 1) - 1 := accScalar_le bits v
    have hM2 : 2 ≤ accScalar m bits v := accScalar_two_le h2 bits v
    have hp : 8 * (2 ^ v * (m + 1)) ≤ 2 ^ (n + 2) * (m + 1) := by
      have hexp : (8 : ℕ) * 2 ^ v = 2 ^ (v + 3) := by rw [pow_add]; ring
      calc 8 * (2 ^ v * (m + 1)) = 2 ^ (v + 3) * (m + 1) := by rw [← hexp]; ring
        _ ≤ 2 ^ (n + 2) * (m + 1) :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hBound' : 4 * (2 * accScalar m bits v + (if bits v then 1 else 0) * 2 - 1) + 3
        < PALLAS_SCALAR_CARD := by
      have h254 := pow254_lt_card
      rcases hb : bits v <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
    have := step_honest (bits (v + 1)) hprev hBound'
    rw [← hstep ⟨v, hv⟩] at this
    simpa [accScalar] using this

/-- The final row's gate identities force the last double-and-add step, with the witnessed
y landing directly on the stepped accumulator's y (`q_mul_3`'s shape: no constancy checks,
`y_a(next)` a bare witnessed cell). -/
theorem sound_last_step {z xA l1 l2 bx yb oz oxA oy : Fp}
    (hbool : (oz - z * 2) * (1 - (oz - z * 2)) = 0)
    (hg1 : l1 * (xA - bx) - (l1 + l2) * (xA - (l1 * l1 - xA - bx)) * (2 : Fp)⁻¹
      + ((oz - z * 2) * 2 - 1) * yb = 0)
    (hsec : l2 * l2 - oxA - (l1 * l1 - xA - bx) - xA = 0)
    (hg2 : l2 * (xA - oxA) - (l1 + l2) * (xA - (l1 * l1 - xA - bx)) * (2 : Fp)⁻¹ - oy = 0) :
    ∃ k : Bool, oz = 2 * z + (if k then 1 else 0) ∧
      ∀ m : ℕ, ({ x := bx, y := yb } : Point Fp).OnCurve →
        ({ x := xA, y := (l1 + l2) * (xA - (l1 * l1 - xA - bx)) * (2 : Fp)⁻¹ } : Point Fp)
          = m • { x := bx, y := yb } →
        2 ≤ m → 2 * m + 1 < PALLAS_SCALAR_CARD →
        ({ x := oxA, y := oy } : Point Fp)
          = (2 * m + (if k then 1 else 0) * 2 - 1) • { x := bx, y := yb } := by
  have h2 : (2 : Fp) ≠ 0 := by decide
  have core : ∀ k : Bool, oz - z * 2 = (if k then 1 else 0) →
      ∀ m : ℕ, ({ x := bx, y := yb } : Point Fp).OnCurve →
        ({ x := xA, y := (l1 + l2) * (xA - (l1 * l1 - xA - bx)) * (2 : Fp)⁻¹ } : Point Fp)
          = m • { x := bx, y := yb } →
        2 ≤ m → 2 * m + 1 < PALLAS_SCALAR_CARD →
        ({ x := oxA, y := oy } : Point Fp)
          = (2 * m + (if k then 1 else 0) * 2 - 1) • { x := bx, y := yb } := by
    intro k hkv m hOn hacc h2m hMb
    obtain ⟨P, hPx, hPy⟩ : ∃ P : Point Fp, P.x = bx ∧ P.y = yb :=
      ⟨{ x := bx, y := yb }, rfl, rfl⟩
    subst hPx hPy
    rw [show ({ x := P.x, y := P.y } : Point Fp) = P from rfl] at hacc hOn ⊢
    have hax : xA = (m • P).x := congrArg Point.x hacc
    have hay : (l1 + l2) * (xA - (l1 * l1 - xA - P.x)) * (2 : Fp)⁻¹ = (m • P).y :=
      congrArg Point.y hacc
    have hstep := step_nsmul hOn (fun _ => k) h2m hMb 0
    have hXP : P.x = (stepPoint P k).x := by
      unfold stepPoint; rcases k with _ | _ <;> rfl
    have hYP : 2 * (m • P).y - 2 * l1 * ((m • P).x - P.x) = 2 * (stepPoint P k).y := by
      unfold stepPoint
      rcases k with _ | _ <;>
        simp only [Bool.false_eq_true, if_false, if_true] at hkv ⊢
      · show _ = 2 * (-P).y
        rw [Point.neg_y]
        linear_combination (-2) * hg1 - 2 * hay + 2 * l1 * hax + 4 * P.y * hkv
      · show _ = 2 * P.y
        linear_combination (-2) * hg1 - 2 * hay + 2 * l1 * hax + 4 * P.y * hkv
    have hYA : 2 * (m • P).y = (l1 + l2) * ((m • P).x - (l1 * l1 - (m • P).x - P.x)) := by
      rw [← hax]
      linear_combination (norm := (field_simp; ring)) (-2) * hay
    have hSec : l2 * l2 = oxA + (l1 * l1 - (m • P).x - P.x) + (m • P).x := by
      rw [← hax]; linear_combination hsec
    have hYC : 4 * l2 * ((m • P).x - oxA) = 4 * (m • P).y + 2 * (2 * oy) := by
      linear_combination (norm := (field_simp; ring)) 4 * hg2 + 4 * hay - 4 * l2 * hax
    have hstep' : Point.doubleAndAdd (m • P) (stepPoint P k)
        = some ((2 * m + (if k then 1 else 0) * 2 - 1) • P) := hstep
    obtain ⟨hxB, hYB⟩ := Halo2.Ironwood.Ecc.DoubleAndAdd.coordinates_of_constraints
      hstep' hYP hXP hYA hSec hYC
    have hyB : oy = ((2 * m + (if k then 1 else 0) * 2 - 1) • P).y := by
      field_simp at hYB
      linear_combination hYB
    rw [hyB, hxB]
  rcases mul_eq_zero.mp hbool with hk | hk
  · exact ⟨false, by simp only [Bool.false_eq_true, if_false]; linear_combination hk,
      core false (by simp only [Bool.false_eq_true, if_false]; linear_combination hk)⟩
  · exact ⟨true, by simp only [if_true]; linear_combination -hk,
      core true (by simp only [if_true]; linear_combination -hk)⟩

/-- The honest final row satisfies `q_mul_3`'s polynomials (completeness counterpart). -/
theorem last_gates {w : State Fp} {m : ℕ} {k k' : Bool} (hH : w.Honest m k) :
    ((w.step k k').z - w.z * 2) * (1 - ((w.step k k').z - w.z * 2)) = 0 ∧
    w.lambda1 * (w.xA - w.base.x)
      - (w.lambda1 + w.lambda2) * (w.xA - (w.lambda1 * w.lambda1 - w.xA - w.base.x)) * (2 : Fp)⁻¹
      + (((w.step k k').z - w.z * 2) * 2 - 1) * w.base.y = 0 ∧
    w.lambda2 * w.lambda2 - (w.step k k').xA
      - (w.lambda1 * w.lambda1 - w.xA - w.base.x) - w.xA = 0 ∧
    w.lambda2 * (w.xA - (w.step k k').xA)
      - (w.lambda1 + w.lambda2) * (w.xA - (w.lambda1 * w.lambda1 - w.xA - w.base.x)) * (2 : Fp)⁻¹
      - w.stepY = 0 := by
  obtain ⟨h1, h2', h3, h4, -, -⟩ := step_gates (k' := k') hH
  refine ⟨h3, h4, ?_, ?_⟩
  · simpa using step_gates (k' := k') hH |>.2.2.2.2.1
  · simp only [State.stepY, step_xA_eq, State.yA2, State.xR]
    ring

/-- The round's output variable: the next row's neighborhood (position-determined). -/
@[circuit_norm]
theorem round_output (i : ℕ) (cfg : Config) (o : ℕ)
    (iv : Var (Unconstrained field) Fp) (self : RegionIndex) :
    (Halo2.Ironwood.Ecc.MulIncomplete.round i).output cfg o iv self
      = reads cfg (o + 1) self := rfl

end Halo2.Ironwood.Ecc.MulIncomplete
