import Clean.Halo2
import Clean.Ironwood.Specs.Pallas
import Clean.Ironwood.Specs.Sinsemilla
import Clean.Ironwood.Ecc.DoubleAndAdd
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Sinsemilla.Basic

/-!
Sinsemilla hash: one word round of `hash_piece`, as a formal circuit. The per-word row assigns
`x_p, λ₁, λ₂` and the next-row `x_a`/`z`, runs the generator lookup, and enables the Sinsemilla
gate on adjacent pairs.

The round's input state is row `r`'s cells (`z`, `x_a`, `x_p`, `λ₁`, `λ₂` — the accumulator's `y`
is virtual: `2·acc.y = Y_A(row)`); its outputs are row `r+1`'s. So the round assigns row `r+1`'s
running sum `z_{r+1}`, the stepped accumulator's `x_a`, and — as in `MulIncomplete` — the next
word's slope cells `x_p, λ₁, λ₂` (the virtual-y representation makes them part of this round's
output). Cells land at the same (column, row) as the Rust iteration; only assignment attribution
moves, which is VK-neutral.

Reference: `halo2_gadgets/src/sinsemilla/chip/hash_to_point.rs`.
-/

namespace Zcash.Circuits.Sinsemilla.HashPiece

open Halo2
open Ecc (DoubleAndAddRow)
open Ecc.DoubleAndAdd (xR yA)
open Specs.Sinsemilla (Generators step hashToPoint)
open Specs (K)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Sinsemilla
  (GeneratorTableConfig GeneratorTableLoaded pieceWord pieceZ rowValue accAfter nextYA
   pieceWord_lt pieceZ_zero pieceZ_succ pieceZ_last chain_eq_sum piece_recombine
   chain_eq_suffix_sum step_coordinates_of_constraints step_honest accAfter_eq_chain)

/-! ## Config -/

structure Config where
  -- `q_sinsemilla1`: the Sinsemilla gate selector.
  qS1 : Selector
  -- `q_sinsemilla2`: a fixed column taking values `0/1/2`, queried inside gate polynomials and the
  -- lookup input.
  qS2 : Column .fixed
  -- `q_sinsemilla4`: the init-gate selector.
  qS4 : Selector
  -- Loads `y_Q` for the init gate.
  fixedYQ : Column .fixed
  -- x-coordinate of the accumulator in each double-and-add row.
  xA : Column .advice
  -- x-coordinate of the generator point being added.
  xP : Column .advice
  -- λ₁ in each double-and-add row.
  lambda1 : Column .advice
  -- λ₂ in each double-and-add row.
  lambda2 : Column .advice
  -- The running-sum `z` column.
  bits : Column .advice
  -- The advice column message pieces are witnessed in.
  witnessPieces : Column .advice
  -- The generator table columns.
  generatorTable : GeneratorTableConfig

/-! ## Gate expression builders

`x_r`, `Y_A` are pure functions of the double-and-add columns at a rotation, inlined as
`Expression` builders over the config columns. -/

/-- `x_r = λ₁² − x_a − x_p` at `rot` (Rust `DoubleAndAdd::x_r`). -/
@[selector_free, query_correct]
def xRExpr (cfg : Config) (rot : Rotation) : Expression Fp Query :=
  let xA : Expression Fp Query := queryAdvice cfg.xA rot
  let xP : Expression Fp Query := queryAdvice cfg.xP rot
  let l1 : Expression Fp Query := queryAdvice cfg.lambda1 rot
  l1 * l1 - xA - xP

/-- `Y_A = (λ₁ + λ₂)(x_a − x_r)` at `rot` (Rust `DoubleAndAdd::Y_A`). -/
@[selector_free, query_correct]
def yAExpr (cfg : Config) (rot : Rotation) : Expression Fp Query :=
  let xA : Expression Fp Query := queryAdvice cfg.xA rot
  let l1 : Expression Fp Query := queryAdvice cfg.lambda1 rot
  let l2 : Expression Fp Query := queryAdvice cfg.lambda2 rot
  (l1 + l2) * (xA - xRExpr cfg rot)

/-- The `y_p` derivation used in the lookup input: `y_p = Y_A/2 − λ₁·(x_a − x_p)`, at rotation 0. -/
@[query_correct]
def yPExpr (cfg : Config) : Expression Fp Query :=
  let xA : Expression Fp Query := queryAdvice cfg.xA 0
  let xP : Expression Fp Query := queryAdvice cfg.xP 0
  let l1 : Expression Fp Query := queryAdvice cfg.lambda1 0
  yAExpr cfg 0 * (.const ((2 : Fp)⁻¹)) - l1 * (xA - xP)

/-! ## The two gates as standalone defs

`Initial y_Q` and the `Sinsemilla gate`. -/

/-- The `"Initial y_Q"` gate, gated by `q_sinsemilla4`: initializes the
accumulator `y` to `y_Q` via `2·y_Q − Y_{A,cur} = 0`. Here `y_Q` is the `fixed_y_q` column at
rotation 0 (the non-`allow_init_from_private_point` branch, which the action circuit uses). -/
def initialYQGate (cfg : Config) : Gate Fp :=
  -- `y_q` (fixed) first, then `Y_A(cur)`'s atoms (xA/λ₁/λ₂/xP @ cur).
  Gate.withSelector "Initial y_Q" cfg.qS4
    [ queryFixed cfg.fixedYQ,
      queryAdvice cfg.xA 0, queryAdvice cfg.lambda1 0, queryAdvice cfg.lambda2 0,
      queryAdvice cfg.xP 0 ] <|
    let yQ : Expression Fp Query := queryFixed cfg.fixedYQ
    [("init y_q", yQ * (2 : Fp) - yAExpr cfg 0)]

/-- The synthetic selector `q_s3 = q_s2·(q_s2 − 1)`: `0` when `q_s2 ∈ {0,1}`, `2` when
`q_s2 = 2` (final piece). -/
@[selector_free, query_correct]
def qS3Expr (cfg : Config) : Expression Fp Query :=
  let qS2 : Expression Fp Query := queryFixed cfg.qS2
  qS2 * (qS2 - (1 : Fp))

/-- The `"Sinsemilla gate"`, gated by `q_sinsemilla1`. Two constraints:

- **secant line**: `λ₂² − (x_{a,next} + x_r + x_{a,cur}) = 0`.
- **y check**:
  `4·λ₂·(x_{a,cur} − x_{a,next}) − [2·Y_{A,cur} + (2 − q_s3)·Y_{A,next} + 2·q_s3·λ₁_next] = 0`. -/
def sinsemillaGate (cfg : Config) : Gate Fp :=
  -- `q_s3` registers `q_s2` (fixed) first; then the closure's four lets; then `x_r(cur)`
  -- adds x_p/λ₁ @ cur and `Y_A(next)` adds λ₂/xP @ next.
  Gate.withSelector "Sinsemilla gate" cfg.qS1
    [ queryFixed cfg.qS2,
      queryAdvice cfg.lambda1 1, queryAdvice cfg.lambda2 0,
      queryAdvice cfg.xA 0, queryAdvice cfg.xA 1,
      queryAdvice cfg.xP 0, queryAdvice cfg.lambda1 0,
      queryAdvice cfg.lambda2 1, queryAdvice cfg.xP 1 ] <|
    let l2Cur : Expression Fp Query := queryAdvice cfg.lambda2 0
    let xACur : Expression Fp Query := queryAdvice cfg.xA 0
    let xANext : Expression Fp Query := queryAdvice cfg.xA 1
    let l1Next : Expression Fp Query := queryAdvice cfg.lambda1 1
    let secant := l2Cur * l2Cur - (xANext + xRExpr cfg 0 + xACur)
    let yCheck :=
      l2Cur * (4 : Fp) * (xACur - xANext)
        - (yAExpr cfg 0 * (2 : Fp)
            + ((2 : Fp) - qS3Expr cfg) * yAExpr cfg 1
            + qS3Expr cfg * (2 : Fp) * l1Next)
    [("secant line", secant), ("y check", yCheck)]

/-! ## The 3-tuple generator lookup

The input tuple (gated by `q_s1` and `q_run = q_s2 − q_s3`):

  `[ q_s1·word,                       ↦ table_idx
     q_s1·x_p + (1 − q_s1)·init_x,    ↦ table_x
     q_s1·y_p + (1 − q_s1)·init_y ]   ↦ table_y`

with `word = z_cur − q_run·z_next·2^K` (`z` = the `bits` column), `y_p = Y_A/2 − λ₁·(x_a − x_p)`
(`yPExpr`), and `(init_x, init_y) = S(0)`. -/
@[query_correct]
def generatorLookup (G : Generators) (cfg : Config) : LookupArgument Fp where
  inputs :=
    let qS1 : Expression Fp Query := querySelector cfg.qS1
    let qRun : Expression Fp Query := queryFixed cfg.qS2 - qS3Expr cfg
    let zCur : Expression Fp Query := queryAdvice cfg.bits 0
    let zNext : Expression Fp Query := queryAdvice cfg.bits 1
    let word : Expression Fp Query := zCur - qRun * zNext * (.const ((2 : Fp) ^ K))
    let xP : Expression Fp Query := queryAdvice cfg.xP 0
    let initX : Expression Fp Query := .const (G.S 0).x
    let initY : Expression Fp Query := .const (G.S 0).y
    [ qS1 * word,
      qS1 * xP + ((1 : Fp) - qS1) * initX,
      qS1 * yPExpr cfg + ((1 : Fp) - qS1) * initY ]
  tables :=
    [ queryFixed cfg.generatorTable.tableIdx.inner,
      queryFixed cfg.generatorTable.tableX.inner,
      queryFixed cfg.generatorTable.tableY.inner ]
  tablesFree := by simp [Expression.SelectorFree, queryFixed]
  arity := rfl

/-! ## Configure

VK-exact registration order: equality-enable all five double-and-add advices, allocate
`q_sinsemilla1` (complex), `q_sinsemilla2` (a fixed column), `q_sinsemilla4` (simple), register the
3-tuple lookup BEFORE the `Initial y_Q` and `Sinsemilla` gates. `fixed_y_q` and the generator table
columns are handed down (the table is loaded separately by `Basic.load`); the
`allow_init_from_private_point = false` branch is the one ported. -/
def configure (G : Generators) (xA xP bits lambda1 lambda2 : Column .advice)
    (witnessPieces : Column .advice) (fixedYQ : Column .fixed)
    (genTable : GeneratorTableConfig) : Configure Fp Config := do
  -- equality on all advice columns, `advices` index order
  enableEquality xA.toAny
  enableEquality xP.toAny
  enableEquality bits.toAny
  enableEquality lambda1.toAny
  enableEquality lambda2.toAny
  -- q_s1 complex, q_s2 a fresh fixed column, q_s4 simple
  let qS1 ← complexSelector
  let qS2 ← fixedColumn
  let qS4 ← selector
  let cfg : Config :=
    { qS1, qS2, qS4, fixedYQ, xA, xP, lambda1, lambda2, bits, witnessPieces,
      generatorTable := genTable }
  -- the 3-tuple generator lookup, registered before the gates. The closure queries
  -- `q_s2` (fixed, via `q_s3`), then `bits` cur/next, `x_p`, and the `y_p` block's
  -- λ₁/x_a @ cur plus λ₂ @ cur (from `Y_A`).
  lookup [queryFixed cfg.qS2, queryAdvice cfg.bits 0, queryAdvice cfg.bits 1,
          queryAdvice cfg.xP 0, queryAdvice cfg.lambda1 0, queryAdvice cfg.xA 0,
          queryAdvice cfg.lambda2 0]
    [((generatorLookup G cfg).inputs[0]!, genTable.tableIdx),
          ((generatorLookup G cfg).inputs[1]!, genTable.tableX),
          ((generatorLookup G cfg).inputs[2]!, genTable.tableY)]
  createGate (initialYQGate cfg)
  createGate (sinsemillaGate cfg)
  return cfg

set_option synthInstance.maxSize 2048 in
@[reducible] private def configureElaborated
    (G : Generators) (xA xP bits lambda1 lambda2 : Column .advice)
    (witnessPieces : Column .advice) (fixedYQ : Column .fixed)
    (genTable : GeneratorTableConfig) :
    ElaboratedConfigure
      (configure G xA xP bits lambda1 lambda2 witnessPieces fixedYQ genTable) := by
  unfold configure
  infer_instance

instance (G : Generators) (xA xP bits lambda1 lambda2 : Column .advice)
    (witnessPieces : Column .advice) (fixedYQ : Column .fixed)
    (genTable : GeneratorTableConfig) :
    ElaboratedConfigure
      (configure G xA xP bits lambda1 lambda2 witnessPieces fixedYQ genTable) :=
  { configureElaborated G xA xP bits lambda1 lambda2 witnessPieces fixedYQ
      genTable with
    selectorRequirements _ := True
    selectorsAllocated := by
      intro counts _
      constructor
      · simp [configure, initialYQGate, sinsemillaGate, Gate.withSelector]
      · simp [configure, generatorLookup, yPExpr, yAExpr, qS3Expr,
          xRExpr, Expression.selectorBound] }

/-- The boundary `q_s2` value: `0` between pieces, `2` on the message's final piece
(`hash_to_point.rs::hash_piece`, `final_piece`). Deliberately NOT `@[simp]`: proofs keep it
as an atom so `linear_combination` can consume `qS2Boundary_run` without case-splitting on
`final`. -/
def qS2Boundary (final : Bool) : Fp := if final then 2 else 0

/-- For both boundary values, the running-word coefficient `q_run = q_s2 − q_s3` vanishes:
`c − c·(c − 1) = 0` for `c ∈ {0, 2}` — the last-row word is `z_w` itself either way. -/
theorem qS2Boundary_run (final : Bool) :
    qS2Boundary final - qS2Boundary final * (qS2Boundary final - 1) = 0 := by
  cases final <;> norm_num [qS2Boundary]

/-! ## The hash-word state

One row of the word loop's positional state: the running sum and the double-and-add cells
at that row. The accumulator's y has no cell; it is virtually represented by the row
(`2·acc.y = Y_A(row)`). -/

structure State (F : Type) where
  -- Running sum `z_r` (the `bits` column).
  z : F
  -- The double-and-add cells `x_a, x_p, λ₁, λ₂`.
  row : DoubleAndAddRow F
deriving ProvableStruct

/-- The accumulator's virtual y: `acc.y = Y_A(row) / 2`. -/
def State.accY (s : State Fp) : Fp := yA s.row * (2 : Fp)⁻¹

/-- The stepped accumulator's coordinates and the next word's slopes, as standalone defs
(NOT `let`s inside `step`: a let-chain here zeta-expands exponentially under projection
whnf — sharing must go through def applications to keep the kernel calm). -/
def State.stepXA (s : State Fp) : Fp :=
  s.row.lambda2 * s.row.lambda2 - s.row.xA - xR s.row

def State.stepYA (s : State Fp) : Fp :=
  s.row.lambda2 * (s.row.xA - s.stepXA) - s.accY

def State.stepL1 (s : State Fp) (g' : Fp × Fp) : Fp :=
  (s.stepYA - g'.2) * (s.stepXA - g'.1)⁻¹

def State.stepL2 (s : State Fp) (g' : Fp × Fp) : Fp :=
  2 * s.stepYA * (s.stepXA - (s.stepL1 g' * s.stepL1 g' - s.stepXA - g'.1))⁻¹ - s.stepL1 g'

/-- The honest next state: the Rust iteration's assignment formulas over the current row's
cells, at the next word's generator `g'` and running sum `z'` (both derived off the piece
cell by the witness programs — the price of the virtual-y representation is that this
round's output accumulator carries the *next* word's slopes). -/
def State.step (s : State Fp) (g' : Fp × Fp) (z' : Fp) : State Fp :=
  { z := z', row := { xA := s.stepXA, xP := g'.1, lambda1 := s.stepL1 g', lambda2 := s.stepL2 g' } }

/-- The state is the honest row `r` of piece `p` entering at accumulator `A`: the running
sum is `z_r`, and the double-and-add cells hold the chained accumulator's x, the word's
generator x, and the true slopes. -/
def State.Honest (G : Generators) (s : State Fp) (p : Fp) (A : Point Fp) (r : ℕ) : Prop :=
  s.z = pieceZ p r ∧
  s.row.xA = (accAfter G (A.x, A.y) p r).1 ∧
  s.row.xP = (G.S (pieceWord p r)).x ∧
  s.row.lambda1 = (rowValue (accAfter G (A.x, A.y) p r)
    ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1 ∧
  s.row.lambda2 = (rowValue (accAfter G (A.x, A.y) p r)
    ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.1

/-! ## The positional neighborhood -/

/-- The adjacent cells round `r`'s gate/lookup read but does not own: row `offset`'s state
(assigned by the previous round, or by the piece's init block). The round's output state is
`reads cfg (offset + 1)` — the next round's neighborhood, chaining by `rfl`. -/
def reads (cfg : Config) (offset : ℕ) (self : RegionIndex) : State (AssignedCell Fp) where
  z := .of self offset cfg.bits
  row := { xA := .of self offset cfg.xA, xP := .of self offset cfg.xP,
           lambda1 := .of self offset cfg.lambda1, lambda2 := .of self offset cfg.lambda2 }

/-- Name the neighborhood cells inside `synthesize` (no ops emitted). -/
def readState (cfg : Config) (offset : ℕ) : RegionCircuit Fp (State (AssignedCell Fp)) :=
  fun self => (reads cfg offset self, [])

@[circuit_norm]
theorem operations_readState (cfg : Config) (offset : ℕ) (self : RegionIndex) :
    (readState cfg offset).operations self = [] := rfl

@[circuit_norm]
theorem output_readState (cfg : Config) (offset : ℕ) (self : RegionIndex) :
    (readState cfg offset).output self = reads cfg offset self := rfl

/-! ## Honest witness programs -/

/-- Read an input cell's value in a placed prover environment. -/
def readCell (env : Placed ProverEnvironment Fp) (c : AssignedCell Fp) : Fp :=
  c.eval env.place env.env.toEnvironment

@[circuit_norm]
theorem readCell_of (env : Placed ProverEnvironment Fp) (self : RegionIndex) (row : ℕ)
    (col : Column .advice) :
    readCell env (AssignedCell.of self row col)
      = env.env.advice col ((env.place self + row : ℕ) : ℤ) := rfl

/-- The neighborhood values in a prover environment. -/
@[circuit_norm]
def readsValue (w : State (AssignedCell Fp)) (env : Placed ProverEnvironment Fp) : State Fp where
  z := readCell env w.z
  row := { xA := readCell env w.row.xA, xP := readCell env w.row.xP,
           lambda1 := readCell env w.row.lambda1, lambda2 := readCell env w.row.lambda2 }

/-- Honest running sum `z_r = ↑(piece.val ≫ (K·r))` at word `r` (`pieceZ` as a witgen program):
cast to ℕ, shift right by `K·r` bits, cast back. -/
def zWit (piece : AssignedCell Fp) (r : ℕ) : WitgenIR Fp 1 :=
  .ofFExpr (.ofNat (.div (.val (.expr piece)) (.const (2 ^ (K * r)))))

/-- The running-sum witness evaluates to the honest `pieceZ` of the piece cell's value —
spelled over the folded `AssignedCell.eval` cell read, the form `h_input` lands on (the
`bitWit_eval` pattern). -/
@[circuit_norm]
theorem zWit_eval (piece : AssignedCell Fp) (r : ℕ) (env : Placed ProverEnvironment Fp)
    (j : ℕ) (hj : j < 1) :
    ((zWit piece r).eval env)[j]
      = pieceZ (AssignedCell.eval env.place env.env.toEnvironment piece) r := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [zWit, Witgen.WitgenIROver.getElem_eval_ofFExpr]
  rfl

/-- Honest witness for one output cell of round `i`: the corresponding field of
`State.step` over the neighborhood readings, at the next word's generator and running sum
(read off the piece cell). -/
def stepWit (G : Generators) (piece : AssignedCell Fp) (w : State (AssignedCell Fp)) (i : ℕ)
    (f : State Fp → Fp) : WitgenIR Fp 1 :=
  .native fun env =>
    let p := readCell env piece
    #v[f ((readsValue w env).step
      ((G.S (pieceWord p (i + 1))).x, (G.S (pieceWord p (i + 1))).y) (pieceZ p (i + 1)))]

/-- Evaluation of the round's witness closures, in one step and without exposing the
native-eval plumbing: the peel reduces every assigned value directly to a folded
`step`-projection. (Keyed on `getElem`, per the lazy-vector convention.) -/
@[circuit_norm]
theorem stepWit_eval (G : Generators) (piece : AssignedCell Fp) (w : State (AssignedCell Fp))
    (i : ℕ) (f : State Fp → Fp) (env : Placed ProverEnvironment Fp) (j : ℕ) (hj : j < 1) :
    ((stepWit G piece w i f).eval env)[j]
      = f ((readsValue w env).step
          ((G.S (pieceWord (AssignedCell.eval env.place env.env.toEnvironment piece) (i + 1))).x,
           (G.S (pieceWord (AssignedCell.eval env.place env.env.toEnvironment piece) (i + 1))).y)
          (pieceZ (AssignedCell.eval env.place env.env.toEnvironment piece) (i + 1))) := by
  have hj0 : j = 0 := by omega
  subst hj0
  simp only [stepWit, Witgen.WitgenIROver.eval_native_apply]
  rfl

/-! ## The value-level round lemmas

`sound_step` routes the row's constraint equations into the round `Spec` (via
`step_coordinates_of_constraints`); `honest_yA`, `step_honest_state` and `step_gates` are the
completeness counterparts over an honest row (`rowValue`/`accAfter` algebra + `step_honest`). -/

/-- `rowValue` projection identities (definitional): the next-row coordinates and the
slopes, spelled over the projections themselves so proofs can treat them as atoms. -/
private theorem rowValue_lambda1 (acc gen : Fp × Fp) :
    (rowValue acc gen).1 = (acc.2 - gen.2) * (acc.1 - gen.1)⁻¹ := rfl

private theorem rowValue_lambda2 (acc gen : Fp × Fp) :
    (rowValue acc gen).2.1
      = 2 * acc.2 * (acc.1 - ((rowValue acc gen).1 * (rowValue acc gen).1 - acc.1 - gen.1))⁻¹
        - (rowValue acc gen).1 := rfl

private theorem rowValue_xANext (acc gen : Fp × Fp) :
    (rowValue acc gen).2.2.1
      = (rowValue acc gen).2.1 * (rowValue acc gen).2.1 - acc.1
        - ((rowValue acc gen).1 * (rowValue acc gen).1 - acc.1 - gen.1) := rfl

private theorem rowValue_yANext (acc gen : Fp × Fp) :
    (rowValue acc gen).2.2.2
      = (rowValue acc gen).2.1 * (acc.1 - (rowValue acc gen).2.2.1) - acc.2 := rfl

/-- `State.step` projection identities (definitional). -/
theorem step_z (s : State Fp) (g' : Fp × Fp) (z' : Fp) : (s.step g' z').z = z' := rfl

theorem step_row_xP (s : State Fp) (g' : Fp × Fp) (z' : Fp) :
    (s.step g' z').row.xP = g'.1 := rfl

theorem step_row_xA (s : State Fp) (g' : Fp × Fp) (z' : Fp) :
    (s.step g' z').row.xA = s.row.lambda2 * s.row.lambda2 - s.row.xA - xR s.row := rfl

theorem step_yA_eq (s : State Fp) (g' : Fp × Fp) (z' : Fp) :
    s.stepYA = s.row.lambda2 * (s.row.xA - (s.step g' z').row.xA) - s.accY := rfl

theorem step_row_lambda1 (s : State Fp) (g' : Fp × Fp) (z' : Fp) :
    (s.step g' z').row.lambda1
      = (s.row.lambda2 * (s.row.xA - (s.step g' z').row.xA) - s.accY - g'.2)
        * ((s.step g' z').row.xA - g'.1)⁻¹ := rfl

theorem step_row_lambda2 (s : State Fp) (g' : Fp × Fp) (z' : Fp) :
    (s.step g' z').row.lambda2
      = 2 * (s.row.lambda2 * (s.row.xA - (s.step g' z').row.xA) - s.accY)
          * ((s.step g' z').row.xA
              - ((s.step g' z').row.lambda1 * (s.step g' z').row.lambda1
                 - (s.step g' z').row.xA - g'.1))⁻¹
        - (s.step g' z').row.lambda1 := rfl

/-- The row's lookup/gate equations force one constrained Sinsemilla step, in point
language. Stated over the raw cell values so the bundle's peeled soundness goal unifies
with it. `oxP/ol1/ol2` are the next row's slope cells (this round's own assignments); the
gate's next-row `Y_A` is derived from them. -/
private theorem sound_step (G : Generators) {m : ℕ}
    {z xA xP l1 l2 oz oxA oxP ol1 ol2 : Fp}
    (hword : z - 2 ^ K * oz = (m : Fp))
    (hxp : xP = (G.S m).x)
    (hyp : (l1 + l2) * (xA - (l1 * l1 - xA - xP)) * (2 : Fp)⁻¹ - l1 * (xA - xP) = (G.S m).y)
    (hsec : l2 * l2 - (oxA + (l1 * l1 - xA - xP) + xA) = 0)
    (hyck : 4 * l2 * (xA - oxA)
      - (2 * ((l1 + l2) * (xA - (l1 * l1 - xA - xP)))
          + 2 * ((ol1 + ol2) * (oxA - (ol1 * ol1 - oxA - oxP)))) = 0) :
    z = (m : Fp) + 2 ^ K * oz ∧
    xP = (G.S m).x ∧
    (l1 + l2) * (xA - (l1 * l1 - xA - xP)) * (2 : Fp)⁻¹ - l1 * (xA - xP) = (G.S m).y ∧
    ∀ A : Point Fp, A.OnCurve → A.x = xA →
      2 * A.y = (l1 + l2) * (xA - (l1 * l1 - xA - xP)) →
      ∀ B, step G.S m A = some B →
        oxA = B.x ∧ 2 * B.y = (ol1 + ol2) * (oxA - (ol1 * ol1 - oxA - oxP)) := by
  refine ⟨by linear_combination hword, hxp, hyp, ?_⟩
  intro A hAon hAx hAyA B hstep
  have h2 : (2 : Fp) ≠ 0 := by decide
  -- clear the halving in the `y_p` derivation
  have hyp2 : (l1 + l2) * (xA - (l1 * l1 - xA - xP)) - 2 * (l1 * (xA - xP))
      = 2 * (G.S m).y := by
    linear_combination (norm := (field_simp; ring)) 2 * hyp
  have hpin := step_coordinates_of_constraints G.S hstep
    (xp := xP) (lambda1 := l1) (lambda2 := l2) (xa' := oxA)
    (YA' := (ol1 + ol2) * (oxA - (ol1 * ol1 - oxA - oxP)))
    (by linear_combination hyp2 + hAyA - 2 * l1 * hAx)
    hxp
    (by linear_combination hAyA - 2 * (l1 + l2) * hAx)
    (by linear_combination hsec)
    (by linear_combination hyck + 4 * l2 * hAx - 2 * hAyA)
  exact ⟨hpin.1, hpin.2.symm⟩

/-- An honest row's derived `Y_A` is twice the accumulator's true y — the `Y_A`
invariant, given the step at this word is defined. -/
theorem honest_yA (G : Generators) {s : State Fp} {p : Fp} {A : Point Fp} {r : ℕ}
    {Ar B : Point Fp}
    (hH : s.Honest G p A r)
    (hAr : accAfter G (A.x, A.y) p r = (Ar.x, Ar.y))
    (hstep : step G.S (pieceWord p r) Ar = some B) :
    yA s.row = 2 * Ar.y := by
  obtain ⟨-, hxA, hxP, hl1, hl2⟩ := hH
  have hh := step_honest G.S hstep
    (l1 := (rowValue (Ar.x, Ar.y) ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1)
    (l2 := (rowValue (Ar.x, Ar.y) ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.1)
    (xa' := (rowValue (Ar.x, Ar.y) ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2.1)
    (ya' := (rowValue (Ar.x, Ar.y) ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2.2)
    rfl rfl rfl rfl
  simp only [yA, xR]
  rw [hxA, hxP, hl1, hl2, hAr]
  exact hh.2.1.symm

/-- A defined chain restricts to every prefix. Donor `HashPiece.range_prefix_some`. -/
theorem range_prefix_some (S : ℕ → Point Fp) (Q : Point Fp) (f : ℕ → ℕ) {n : ℕ} {B : Point Fp}
    (hn : hashToPoint S Q ((List.range n).map f) = some B)
    {r : ℕ} (hr : r ≤ n) :
    ∃ C, hashToPoint S Q ((List.range r).map f) = some C := by
  obtain ⟨k, rfl⟩ : ∃ k, n = r + k := ⟨n - r, by omega⟩
  rw [List.range_add, List.map_append, Specs.Sinsemilla.hashToPoint_append] at hn
  cases hc : hashToPoint S Q ((List.range r).map f) with
  | none => rw [hc] at hn; simp at hn
  | some C => exact ⟨C, rfl⟩

/-- Peel the last step off a defined `(r+1)`-prefix chain. -/
theorem prefix_step_some (S : ℕ → Point Fp) (Q : Point Fp) (f : ℕ → ℕ) {r : ℕ}
    {Ar Ar1 : Point Fp}
    (hAr : hashToPoint S Q ((List.range r).map f) = some Ar)
    (hAr1 : hashToPoint S Q ((List.range (r + 1)).map f) = some Ar1) :
    step S (f r) Ar = some Ar1 := by
  rw [List.range_succ] at hAr1
  simp only [List.map_append, List.map_cons, List.map_nil] at hAr1
  rw [Specs.Sinsemilla.hashToPoint_concat, hAr] at hAr1
  exact hAr1

/-- The step of an honest row lands on the honest next row (the round's chaining lemma),
and the honest row satisfies the constraint equations — the completeness counterpart of
`sound_step`. The gate equations are stated in the *raw* polynomial spelling (no `yA`/`xR`
atoms): converting `yA (s.step …).row` to its polynomial after the fact is kernel-hostile
(deep instance defeq), so the raw form is produced here directly, via the `rowValue`
route. Requires the spec-level chain defined through word `r + 1` (the gate's next-row
`Y_A` invariant reads the *next* word's slopes). -/
private theorem step_gates (G : Generators) {s : State Fp} {p : Fp} {A B : Point Fp} {r : ℕ}
    (hH : s.Honest G p A r)
    (hchain : hashToPoint G.S A ((List.range (r + 2)).map (pieceWord p)) = some B) :
    (s.row.lambda1 + s.row.lambda2)
        * (s.row.xA - (s.row.lambda1 * s.row.lambda1 - s.row.xA - s.row.xP)) * (2 : Fp)⁻¹
      - s.row.lambda1 * (s.row.xA - s.row.xP) = (G.S (pieceWord p r)).y ∧
    (s.step ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)
        (pieceZ p (r + 1))).Honest G p A (r + 1) ∧
    s.row.lambda2 * s.row.lambda2
      - ((s.step ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)
            (pieceZ p (r + 1))).row.xA
          + (s.row.lambda1 * s.row.lambda1 - s.row.xA - s.row.xP) + s.row.xA) = 0 ∧
    4 * s.row.lambda2 * (s.row.xA
        - (s.step ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)
            (pieceZ p (r + 1))).row.xA)
      - (2 * ((s.row.lambda1 + s.row.lambda2)
            * (s.row.xA - (s.row.lambda1 * s.row.lambda1 - s.row.xA - s.row.xP)))
          + 2 * (((s.step ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)
                    (pieceZ p (r + 1))).row.lambda1
                  + (s.step ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)
                      (pieceZ p (r + 1))).row.lambda2)
                * ((s.step ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)
                      (pieceZ p (r + 1))).row.xA
                    - ((s.step ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)
                          (pieceZ p (r + 1))).row.lambda1
                        * (s.step ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)
                            (pieceZ p (r + 1))).row.lambda1
                      - (s.step ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)
                          (pieceZ p (r + 1))).row.xA
                      - (s.step ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)
                          (pieceZ p (r + 1))).row.xP)))) = 0 := by
  -- prefix chain points and the two step facts
  obtain ⟨Ar, hAr⟩ := range_prefix_some G.S A (pieceWord p) hchain (show r ≤ r + 2 by omega)
  obtain ⟨Ar1, hAr1⟩ :=
    range_prefix_some G.S A (pieceWord p) hchain (show r + 1 ≤ r + 2 by omega)
  have hstep_r : step G.S (pieceWord p r) Ar = some Ar1 :=
    prefix_step_some G.S A (pieceWord p) hAr hAr1
  have hstep_r1 : step G.S (pieceWord p (r + 1)) Ar1 = some B :=
    prefix_step_some G.S A (pieceWord p) hAr1 hchain
  have hAcc_r : accAfter G (A.x, A.y) p r = (Ar.x, Ar.y) := accAfter_eq_chain G p hAr
  have hAcc_r1 : accAfter G (A.x, A.y) p (r + 1) = (Ar1.x, Ar1.y) :=
    accAfter_eq_chain G p hAr1
  -- the Y_A invariant at row r (uses hH intact)
  have hyA_r : yA s.row = 2 * Ar.y := honest_yA G hH hAcc_r hstep_r
  have hyA_r_raw : (s.row.lambda1 + s.row.lambda2)
      * (s.row.xA - (s.row.lambda1 * s.row.lambda1 - s.row.xA - s.row.xP)) = 2 * Ar.y := by
    rw [show (s.row.lambda1 + s.row.lambda2)
        * (s.row.xA - (s.row.lambda1 * s.row.lambda1 - s.row.xA - s.row.xP))
        = yA s.row from rfl]
    exact hyA_r
  obtain ⟨hz, hxA, hxP, hl1, hl2⟩ := hH
  rw [hAcc_r] at hxA hl1 hl2
  -- the honest-step facts at word r, over the `rowValue` slopes
  have hhr := step_honest G.S hstep_r
    (l1 := (rowValue (Ar.x, Ar.y) ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1)
    (l2 := (rowValue (Ar.x, Ar.y) ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.1)
    (xa' := (rowValue (Ar.x, Ar.y) ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2.1)
    (ya' := (rowValue (Ar.x, Ar.y) ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2.2)
    rfl rfl rfl rfl
  obtain ⟨hline, hYAinv, hxNext, hyNext⟩ := hhr
  have h2 : (2 : Fp) ≠ 0 := by decide
  have haccY : s.accY = Ar.y := by
    simp only [State.accY]
    rw [hyA_r]
    field_simp
  -- notation for this word's generator pair and the next state
  set g' : Fp × Fp :=
    ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y) with hg'
  -- the step's accumulator coordinates land on `(Ar1.x, Ar1.y)`
  have hxAnew : (s.step g' (pieceZ p (r + 1))).row.xA = Ar1.x := by
    rw [step_row_xA]
    simp only [xR]
    rw [hxA, hxP, hl1, hl2, ← hxNext, rowValue_xANext]
  have hyAnew : s.row.lambda2 * (s.row.xA - (s.step g' (pieceZ p (r + 1))).row.xA)
      - s.accY = Ar1.y := by
    rw [hxAnew, hl2, hxA, haccY, ← hyNext, rowValue_yANext, hxNext]
  have hyAnew' : s.row.lambda2 * (s.row.xA - Ar1.x) - s.accY = Ar1.y := by
    rw [← hxAnew]
    exact hyAnew
  -- the stepped slopes land on the next row's `rowValue` slopes
  have hl1next : (s.step g' (pieceZ p (r + 1))).row.lambda1
      = (rowValue (Ar1.x, Ar1.y) g').1 := by
    rw [step_row_lambda1, hxAnew, hyAnew', rowValue_lambda1]
  have hl2next : (s.step g' (pieceZ p (r + 1))).row.lambda2
      = (rowValue (Ar1.x, Ar1.y) g').2.1 := by
    rw [step_row_lambda2, hxAnew, hyAnew', hl1next, rowValue_lambda2 (Ar1.x, Ar1.y) g']
  -- honesty of the stepped state
  have hHnext : (s.step g' (pieceZ p (r + 1))).Honest G p A (r + 1) := by
    refine ⟨step_z .., ?_, step_row_xP .., ?_, ?_⟩
    · rw [hxAnew, hAcc_r1]
    · rw [hl1next, hAcc_r1]
    · rw [hl2next, hAcc_r1]
  -- the next row's Y_A invariant, in raw spelling (via the `rowValue` route — never via
  -- the `yA` atom, whose conversion at a step row is kernel-hostile)
  have hhr1 := step_honest G.S hstep_r1
    (l1 := (rowValue (Ar1.x, Ar1.y)
      ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)).1)
    (l2 := (rowValue (Ar1.x, Ar1.y)
      ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)).2.1)
    (xa' := (rowValue (Ar1.x, Ar1.y)
      ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)).2.2.1)
    (ya' := (rowValue (Ar1.x, Ar1.y)
      ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)).2.2.2)
    rfl rfl rfl rfl
  have hyA_r1_raw : ((s.step g' (pieceZ p (r + 1))).row.lambda1
        + (s.step g' (pieceZ p (r + 1))).row.lambda2)
      * ((s.step g' (pieceZ p (r + 1))).row.xA
          - ((s.step g' (pieceZ p (r + 1))).row.lambda1
              * (s.step g' (pieceZ p (r + 1))).row.lambda1
            - (s.step g' (pieceZ p (r + 1))).row.xA
            - (s.step g' (pieceZ p (r + 1))).row.xP)) = 2 * Ar1.y := by
    rw [hl1next, hl2next, hxAnew, step_row_xP]
    exact hhr1.2.1.symm
  refine ⟨?_, hHnext, ?_, ?_⟩
  · -- the `y_p` derivation: the halved Y_A invariant + the line fact
    have hhalf : (s.row.lambda1 + s.row.lambda2)
        * (s.row.xA - (s.row.lambda1 * s.row.lambda1 - s.row.xA - s.row.xP)) * (2 : Fp)⁻¹
        = Ar.y := by
      rw [hyA_r_raw]
      field_simp
    rw [hhalf, hl1, hxA, hxP]
    exact hline
  · -- secant: definitional over the step's xA
    rw [step_row_xA]
    simp only [xR]
    ring
  · -- y check: the two raw Y_A invariants + the y-law of the step
    rw [hyA_r_raw, hyA_r1_raw]
    linear_combination 4 * hyAnew + 4 * haccY

/-- Public chaining/exit lemma: an honest row at word `r` with the chain defined through
word `r` steps to the honest row at `r + 1`, whose accumulator lands on the chain point
`B` — plus the row identities a composing circuit consumes (the lookup's `y_p` fact and
the y-law of the step). Only needs the `(r+1)`-prefix chain (no next-word gate here). -/
theorem step_exit (G : Generators) {s : State Fp} {p : Fp} {A B : Point Fp} {r : ℕ}
    (hH : s.Honest G p A r)
    (hchain : hashToPoint G.S A ((List.range (r + 1)).map (pieceWord p)) = some B) :
    (s.step ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)
        (pieceZ p (r + 1))).Honest G p A (r + 1) ∧
    (s.step ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)
        (pieceZ p (r + 1))).row.xA = B.x ∧
    s.row.lambda2 * (s.row.xA
        - (s.step ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y)
            (pieceZ p (r + 1))).row.xA) - s.accY = B.y ∧
    (s.row.lambda1 + s.row.lambda2)
        * (s.row.xA - (s.row.lambda1 * s.row.lambda1 - s.row.xA - s.row.xP)) * (2 : Fp)⁻¹
      - s.row.lambda1 * (s.row.xA - s.row.xP) = (G.S (pieceWord p r)).y := by
  obtain ⟨Ar, hAr⟩ := range_prefix_some G.S A (pieceWord p) hchain (show r ≤ r + 1 by omega)
  have hstep_r : step G.S (pieceWord p r) Ar = some B :=
    prefix_step_some G.S A (pieceWord p) hAr hchain
  have hAcc_r : accAfter G (A.x, A.y) p r = (Ar.x, Ar.y) := accAfter_eq_chain G p hAr
  have hAcc_r1 : accAfter G (A.x, A.y) p (r + 1) = (B.x, B.y) := accAfter_eq_chain G p hchain
  have hyA_r : yA s.row = 2 * Ar.y := honest_yA G hH hAcc_r hstep_r
  have hyA_r_raw : (s.row.lambda1 + s.row.lambda2)
      * (s.row.xA - (s.row.lambda1 * s.row.lambda1 - s.row.xA - s.row.xP)) = 2 * Ar.y := by
    rw [show (s.row.lambda1 + s.row.lambda2)
        * (s.row.xA - (s.row.lambda1 * s.row.lambda1 - s.row.xA - s.row.xP))
        = yA s.row from rfl]
    exact hyA_r
  obtain ⟨hz, hxA, hxP, hl1, hl2⟩ := hH
  rw [hAcc_r] at hxA hl1 hl2
  have hhr := step_honest G.S hstep_r
    (l1 := (rowValue (Ar.x, Ar.y) ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1)
    (l2 := (rowValue (Ar.x, Ar.y) ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.1)
    (xa' := (rowValue (Ar.x, Ar.y) ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2.1)
    (ya' := (rowValue (Ar.x, Ar.y) ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2.2)
    rfl rfl rfl rfl
  obtain ⟨hline, hYAinv, hxNext, hyNext⟩ := hhr
  have h2 : (2 : Fp) ≠ 0 := by decide
  have haccY : s.accY = Ar.y := by
    simp only [State.accY]
    rw [hyA_r]
    field_simp
  set g' : Fp × Fp :=
    ((G.S (pieceWord p (r + 1))).x, (G.S (pieceWord p (r + 1))).y) with hg'
  have hxAnew : (s.step g' (pieceZ p (r + 1))).row.xA = B.x := by
    rw [step_row_xA]
    simp only [xR]
    rw [hxA, hxP, hl1, hl2, ← hxNext, rowValue_xANext]
  have hyAnew : s.row.lambda2 * (s.row.xA - (s.step g' (pieceZ p (r + 1))).row.xA)
      - s.accY = B.y := by
    rw [hxAnew, hl2, hxA, haccY, ← hyNext, rowValue_yANext, hxNext]
  have hyAnew' : s.row.lambda2 * (s.row.xA - B.x) - s.accY = B.y := by
    rw [← hxAnew]
    exact hyAnew
  have hl1next : (s.step g' (pieceZ p (r + 1))).row.lambda1
      = (rowValue (B.x, B.y) g').1 := by
    rw [step_row_lambda1, hxAnew, hyAnew', rowValue_lambda1]
  have hl2next : (s.step g' (pieceZ p (r + 1))).row.lambda2
      = (rowValue (B.x, B.y) g').2.1 := by
    rw [step_row_lambda2, hxAnew, hyAnew', hl1next, rowValue_lambda2 (B.x, B.y) g']
  refine ⟨⟨step_z .., ?_, step_row_xP .., ?_, ?_⟩, hxAnew, hyAnew, ?_⟩
  · rw [hxAnew, hAcc_r1]
  · rw [hl1next, hAcc_r1]
  · rw [hl2next, hAcc_r1]
  · have hhalf : (s.row.lambda1 + s.row.lambda2)
        * (s.row.xA - (s.row.lambda1 * s.row.lambda1 - s.row.xA - s.row.xP)) * (2 : Fp)⁻¹
        = Ar.y := by
      rw [hyA_r_raw]
      field_simp
    rw [hhalf, hl1, hxA, hxP]
    exact hline

/-- The round's constraint goal, in one goal-shaped package (the MulIncomplete
`step_gates` convention): membership + secant + y-check exactly as the peeled
completeness goal spells them — over the *folded* step projections (`stepWit_eval`'s
normal form), so the bundle application unifies syntactically, with no premises. The
kernel stays calm because `State.step` is never zeta-expanded. -/
private theorem complete_gates (G : Generators)
    (usable : ℕ) (tIdx tX tY : ℕ → Fp)
    {p : Fp} {A B : Point Fp} {i : ℕ} {s : State Fp}
    (hH : s.Honest G p A i)
    (hchain : hashToPoint G.S A ((List.range (i + 2)).map (pieceWord p)) = some B)
    (hUsable : 2 ^ K ≤ usable)
    (hBlock : ∀ r : ℕ, r < 2 ^ K → tIdx r = (r : Fp) ∧ tX r = (G.S r).x ∧ tY r = (G.S r).y) :
    (∃ tableRow < usable,
      [s.z - (1 - (1 - 1)) * pieceZ p (i + 1) * 2 ^ K,
       s.row.xP + (1 - 1) * (G.S 0).x,
       (s.row.lambda1 + s.row.lambda2)
           * (s.row.xA - (s.row.lambda1 * s.row.lambda1 - s.row.xA - s.row.xP)) * (2 : Fp)⁻¹
         - s.row.lambda1 * (s.row.xA - s.row.xP) + (1 - 1) * (G.S 0).y]
        = [tIdx tableRow, tX tableRow, tY tableRow]) ∧
    s.row.lambda2 * s.row.lambda2
      - ((s.step ((G.S (pieceWord p (i + 1))).x, (G.S (pieceWord p (i + 1))).y)
            (pieceZ p (i + 1))).row.xA
          + (s.row.lambda1 * s.row.lambda1 - s.row.xA - s.row.xP) + s.row.xA) = 0 ∧
    s.row.lambda2 * 4 * (s.row.xA
        - (s.step ((G.S (pieceWord p (i + 1))).x, (G.S (pieceWord p (i + 1))).y)
            (pieceZ p (i + 1))).row.xA)
      - ((s.row.lambda1 + s.row.lambda2)
            * (s.row.xA - (s.row.lambda1 * s.row.lambda1 - s.row.xA - s.row.xP)) * 2
          + (2 - (1 - 1))
              * (((s.step ((G.S (pieceWord p (i + 1))).x, (G.S (pieceWord p (i + 1))).y)
                    (pieceZ p (i + 1))).row.lambda1
                  + (s.step ((G.S (pieceWord p (i + 1))).x, (G.S (pieceWord p (i + 1))).y)
                      (pieceZ p (i + 1))).row.lambda2)
                * ((s.step ((G.S (pieceWord p (i + 1))).x, (G.S (pieceWord p (i + 1))).y)
                      (pieceZ p (i + 1))).row.xA
                    - ((s.step ((G.S (pieceWord p (i + 1))).x, (G.S (pieceWord p (i + 1))).y)
                          (pieceZ p (i + 1))).row.lambda1
                        * (s.step ((G.S (pieceWord p (i + 1))).x, (G.S (pieceWord p (i + 1))).y)
                            (pieceZ p (i + 1))).row.lambda1
                      - (s.step ((G.S (pieceWord p (i + 1))).x, (G.S (pieceWord p (i + 1))).y)
                          (pieceZ p (i + 1))).row.xA
                      - (s.step ((G.S (pieceWord p (i + 1))).x, (G.S (pieceWord p (i + 1))).y)
                          (pieceZ p (i + 1))).row.xP)))
          + (1 - 1) * 2
              * (s.step ((G.S (pieceWord p (i + 1))).x, (G.S (pieceWord p (i + 1))).y)
                  (pieceZ p (i + 1))).row.lambda1) = 0 := by
  obtain ⟨hyp_fact, hHnext, hsec_fact, hyck_fact⟩ := step_gates G hH hchain
  have hz := hH.1
  have hxP := hH.2.2.1
  obtain ⟨hb_idx, hb_x, hb_y⟩ := hBlock (pieceWord p i) (pieceWord_lt p i)
  refine ⟨⟨pieceWord p i, lt_of_lt_of_le (pieceWord_lt p i) hUsable, ?_⟩, ?_, ?_⟩
  · simp only [List.cons.injEq, and_true]
    refine ⟨?_, ?_, ?_⟩
    · rw [hb_idx]
      linear_combination hz + pieceZ_succ p i
    · rw [hb_x]
      linear_combination hxP
    · rw [hb_y]
      linear_combination hyp_fact
  · linear_combination hsec_fact
  · linear_combination hyck_fact

/-- One interior hash-word round at word index `i`, at its own row `offset`. Assigns row
`offset + 1`'s cells (running sum, stepped accumulator x, next word's slopes), enables the
generator lookup and the Sinsemilla gate at `offset`. -/
def round (G : Generators) (i : ℕ) : FormalRegionCircuit Fp Config Config field State where
  configure := pure
  elaborated :=
    { keygenRequirements :=
        { gates cfg _ := [sinsemillaGate cfg]
          lookups cfg _ := [generatorLookup G cfg] } }

  synthesize cfg offset (piece : AssignedCell Fp) := do
    let w ← readState cfg offset
    -- interior word row: `q_s2 = 1` (Rust `hash_piece`'s per-row `assign_fixed`)
    let _q ← assignFixed cfg.qS2 offset 1
    let _z ← assignAdvice cfg.bits (offset + 1) (zWit piece (i + 1))
    let _xP ← assignAdvice cfg.xP (offset + 1) (stepWit G piece w i (·.row.xP))
    let _l1 ← assignAdvice cfg.lambda1 (offset + 1) (stepWit G piece w i (·.row.lambda1))
    let _l2 ← assignAdvice cfg.lambda2 (offset + 1) (stepWit G piece w i (·.row.lambda2))
    let _xA ← assignAdvice cfg.xA (offset + 1) (stepWit G piece w i (·.row.xA))
    (generatorLookup G cfg).enable [cfg.qS1] offset
    (sinsemillaGate cfg).enable offset
    readState cfg (offset + 1)

  Witness := State
  extract cfg offset _ self env := eval env (reads cfg offset self)

  EnvAssumptions cfg env := GeneratorTableLoaded G cfg.generatorTable env.env

  -- One constrained Sinsemilla word, in point language: some `< 2^K` word `m` enters the
  -- running sum, the row's `x_p`/`y_p` land on the generator `S(m)`, and — whenever the
  -- entering row carries an on-curve accumulator — the outgoing row carries the stepped
  -- accumulator `(A ⸭ S(m)) ⸭ A`.
  Spec _ out w :=
    ∃ m : ℕ, m < 2 ^ K ∧
      w.z = (m : Fp) + 2 ^ K * out.z ∧
      w.row.xP = (G.S m).x ∧
      yA w.row * (2 : Fp)⁻¹ - w.row.lambda1 * (w.row.xA - w.row.xP) = (G.S m).y ∧
      ∀ A : Point Fp, A.OnCurve → A.x = w.row.xA → 2 * A.y = yA w.row →
        ∀ B, step G.S m A = some B → out.row.xA = B.x ∧ 2 * B.y = yA out.row

  -- Honest neighborhood: the entering row is the honest row `i` of the piece, with the
  -- spec-level chain defined through word `i + 1`.
  ProverAssumptions piece w _ :=
    ∃ A B : Point Fp, A.OnCurve ∧ w.Honest G piece A i ∧
      hashToPoint G.S A ((List.range (i + 2)).map (pieceWord piece)) = some B

  ProverSpec piece out w _ :=
    out = w.step ((G.S (pieceWord piece (i + 1))).x, (G.S (pieceWord piece (i + 1))).y)
      (pieceZ piece (i + 1))

  soundness := by
    circuit_proof_start2 [generatorLookup, sinsemillaGate, yPExpr, yAExpr, xRExpr, qS3Expr,
      reads, readState]
    obtain ⟨t, ht, hmem⟩ := region_1
    simp only [List.cons.injEq, and_true] at hmem
    obtain ⟨h0, h1, h2y⟩ := hmem
    obtain ⟨-, hSpec, -⟩ := env_assumptions
    obtain ⟨m, hm, hIdx, hX, hY⟩ := hSpec t ht
    obtain ⟨hsec, hyck⟩ := region_2
    rw [region_0] at h0 hyck
    rw [hIdx] at h0
    rw [hX] at h1
    rw [hY] at h2y
    refine ⟨m, hm, ?_⟩
    exact sound_step G (by linear_combination h0) (by linear_combination h1)
      (by linear_combination h2y) (by linear_combination hsec) (by linear_combination hyck)

  completeness := by
    circuit_proof_start2 [generatorLookup, sinsemillaGate, yPExpr, yAExpr, xRExpr, qS3Expr,
      reads, readState]
    obtain ⟨A, B, hAon, hH, hchain⟩ := prover_assumptions
    obtain ⟨hUsable, -, hBlock⟩ := env_assumptions
    -- land the honest witness values in the goal (the fixed selector, the outgoing
    -- row's assigns, and the running-sum cell), then the gates are the honest lemma
    rw [region_0, ← output_eq.2, region_1, region_2, region_3, region_4, region_5]
    refine ⟨?_, rfl⟩
    simp only [one_mul, true_and]
    exact complete_gates G _
      (fun t => env.fixed cfg.generatorTable.tableIdx.inner (t : ℤ))
      (fun t => env.fixed cfg.generatorTable.tableX.inner (t : ℤ))
      (fun t => env.fixed cfg.generatorTable.tableY.inner (t : ℤ))
      hH hchain hUsable hBlock

/-- The round's output variable: the next row's neighborhood (position-determined). -/
@[circuit_norm]
theorem round_output (G : Generators) (i : ℕ) (cfg : Config) (o : ℕ) (iv : AssignedCell Fp)
    (self : RegionIndex) :
    (round G i).output cfg o iv self = reads cfg (o + 1) self := rfl

end Zcash.Circuits.Sinsemilla.HashPiece
