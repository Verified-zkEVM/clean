import Clean.Halo2
import Clean.Orchard.Specs.Pallas
import Clean.Orchard.Specs.Sinsemilla
import Clean.Orchard.Ecc.DoubleAndAdd
import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Sinsemilla.Basic

/-!
Reference (ported from actual Rust, not memory):
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/sinsemilla/`
- `chip.rs` — `SinsemillaConfig` (all columns/selectors) and `configure` (ALL gates + the
  3-tuple lookup registration). Read in full via `chip.rs:37-288`, `generator_table.rs:46-82`.
- `chip/hash_to_point.rs` — the per-piece hash round layout (`hash_piece`, lines 295-493):
  every row of a piece has `q_sinsemilla1` on; `q_sinsemilla2 = 1` on rows `0 .. num_words−2`,
  and `0` (or `2` on the final piece) on the last row. Per row: assign `x_p, λ₁, λ₂` and the
  next-row `x_a`, run the generator lookup, and enable the Sinsemilla gate on adjacent pairs.

Orchard `feat/ironwood` uses **vanilla** halo2_gadgets 0.5.0 Sinsemilla unchanged, so this
ports the vanilla chip. `K = 10`.

## Slice-1 scope (this file)

The per-piece hash round loop of `hash_to_point::hash_piece`, in the established Ironwood
loop shape (`Clean/Ironwood/Ecc/MulIncomplete.lean` — the closest structural relative):

- **Config + configure**: the flattened `SinsemillaConfig`, the two gates
  (`Initial y_Q`, `Sinsemilla gate`) and the 3-tuple generator lookup, all as standalone
  `configure`-registered defs (the established gate/argument pattern).
- **The round loop**: a structurally recursive `RegionCircuit` over the word count with
  absolute-row addressing, so `(loop (k+1)).operations = (loop k).operations ++
  (round k).operations` by `rfl` — the per-round decomposition the loop inductions consume.
- **`soundness_aux`**: the pure per-row-facts → `Spec` bridge, lifted from the donor
  (framework-agnostic, over `dR : ℕ → DoubleAndAddRow Fp`, `zV : ℕ → Fp`), fully proven.
- **The `FormalRegionCircuit` contract**: statements final; the framework-half of
  soundness/completeness (reducing each round's `enableGate`/`enableLookup` constraint to
  the value-level row equations `dR`/`zV`, then routing into `soundness_aux`) is left as
  fully-stated sorries — the MulIncomplete pattern (structure-complete; threaded hypotheses
  worked out, donor lemmas identified). See the TACTIC GAP notes.

## Multi-column table resolution (recorded in `Basic.lean`)

Three `loadTable` ops (idx, x, y), each a single `TableColumn`, bundled by
`Sinsemilla.GeneratorTableLoaded`. No new multi-column op; the framework's per-column
`loadTable` already models one dense-block + default-fill column, exactly one S-table column.
-/

namespace Halo2.Ironwood.Sinsemilla.HashPiece

open Orchard (Point)
open Orchard.Ecc (DoubleAndAddRow)
open Orchard.Ecc.DoubleAndAdd (xR yA)
open Orchard.Specs.Sinsemilla (Generators step hashToPoint)
open Orchard.Specs (K)
open CompElliptic.Fields.Pasta (PALLAS_BASE_CARD)
open Halo2.Ironwood.Sinsemilla
  (GeneratorTableConfig GeneratorTableLoaded pieceWord pieceZ rowValue accAfter nextYA
   pieceWord_lt pieceZ_zero pieceZ_succ pieceZ_last chain_eq_sum piece_recombine
   chain_eq_suffix_sum step_coordinates_of_constraints step_honest accAfter_eq_chain)

/-! ## Config

Rust `SinsemillaConfig` (`chip.rs:37-72`), flattened. `q_sinsemilla1`, `q_sinsemilla4` are
`Selector`s; `q_sinsemilla2` is a `Column .fixed` (it takes values `0/1/2`, queried inside
gate polynomials and the lookup input). `fixed_y_q` loads `y_Q` for the init gate. The
`double_and_add` columns are `x_a, x_p, λ₁, λ₂`; `bits` is the running-sum `z` column. The
generator table columns are held in `generatorTable`. -/
structure Config where
  qS1 : Selector
  qS2 : Column .fixed
  qS4 : Selector
  fixedYQ : Column .fixed
  xA : Column .advice
  xP : Column .advice
  lambda1 : Column .advice
  lambda2 : Column .advice
  bits : Column .advice
  generatorTable : GeneratorTableConfig

/-! ## Gate expression builders (verbatim at the Rust rotations)

`x_r`, `Y_A` are pure functions of the double-and-add columns at a rotation
(`chip.rs:214-221`). We inline them as `Expression` builders over the config columns. -/

/-- `x_r = λ₁² − x_a − x_p` at `rot` (Rust `DoubleAndAdd::x_r`). -/
def xRExpr (cfg : Config) (rot : Rotation) : Expression Fp Query :=
  let xA : Expression Fp Query := queryAdvice cfg.xA rot
  let xP : Expression Fp Query := queryAdvice cfg.xP rot
  let l1 : Expression Fp Query := queryAdvice cfg.lambda1 rot
  l1 * l1 - xA - xP

/-- `Y_A = (λ₁ + λ₂)(x_a − x_r)` at `rot` (Rust `DoubleAndAdd::Y_A`). -/
def yAExpr (cfg : Config) (rot : Rotation) : Expression Fp Query :=
  let xA : Expression Fp Query := queryAdvice cfg.xA rot
  let l1 : Expression Fp Query := queryAdvice cfg.lambda1 rot
  let l2 : Expression Fp Query := queryAdvice cfg.lambda2 rot
  (l1 + l2) * (xA - xRExpr cfg rot)

/-- The `y_p` derivation used in the lookup input (`generator_table.rs:64-70`):
`y_p = Y_A/2 − λ₁·(x_a − x_p)`, at rotation 0. -/
def yPExpr (cfg : Config) : Expression Fp Query :=
  let xA : Expression Fp Query := queryAdvice cfg.xA 0
  let xP : Expression Fp Query := queryAdvice cfg.xP 0
  let l1 : Expression Fp Query := queryAdvice cfg.lambda1 0
  yAExpr cfg 0 * (.const ((2 : Fp)⁻¹)) - l1 * (xA - xP)

/-! ## The two gates as standalone defs

`Initial y_Q` (`chip.rs:225-240`) and the `Sinsemilla gate` (`chip.rs:243-285`). The
donor `Clean/Orchard/Sinsemilla/Chip.lean` proves these at value level; here they are the
`configure`-registered `Gate` data with polynomials verbatim at the Rust rotations. -/

/-- Rust `"Initial y_Q"` gate (`chip.rs:225-240`), gated by `q_sinsemilla4`: initializes the
accumulator `y` to `y_Q` via `2·y_Q − Y_{A,cur} = 0`. Here `y_Q` is the `fixed_y_q` column at
rotation 0 (the non-`allow_init_from_private_point` branch, which the action circuit uses). -/
def initialYQGate (cfg : Config) : Gate Fp where
  name := "Initial y_Q"
  selector := cfg.qS4
  constraints :=
    let yQ : Expression Fp Query := queryFixed cfg.fixedYQ
    Constraints.withSelector cfg.qS4
      [("init y_q", (2 : Fp) * yQ - yAExpr cfg 0)]

/-- The synthetic selector `q_s3 = q_s2·(q_s2 − 1)` (`chip.rs:49`, `98-102`): `0` when
`q_s2 ∈ {0,1}`, `2` when `q_s2 = 2` (final piece). -/
def qS3Expr (cfg : Config) : Expression Fp Query :=
  let qS2 : Expression Fp Query := queryFixed cfg.qS2
  qS2 * (qS2 - (1 : Fp))

/-- Rust `"Sinsemilla gate"` (`chip.rs:243-285`), gated by `q_sinsemilla1`. Two constraints:

- **secant line** (`chip.rs:262-263`): `λ₂² − (x_{a,next} + x_r + x_{a,cur}) = 0`.
- **y check** (`chip.rs:268-282`):
  `4·λ₂·(x_{a,cur} − x_{a,next}) − [2·Y_{A,cur} + (2 − q_s3)·Y_{A,next} + 2·q_s3·λ₁_next] = 0`.

Matches the donor `Chip.Gate` (`yLhs = 4·λ₂·(x_a − x_a')`, `yRhs = 2·Y_A(cur) + (2−q_s3)·Y_A(next)
+ q_s3·2·λ₁_next`). -/
def sinsemillaGate (cfg : Config) : Gate Fp where
  name := "Sinsemilla gate"
  selector := cfg.qS1
  constraints :=
    let l2Cur : Expression Fp Query := queryAdvice cfg.lambda2 0
    let xACur : Expression Fp Query := queryAdvice cfg.xA 0
    let xANext : Expression Fp Query := queryAdvice cfg.xA 1
    let l1Next : Expression Fp Query := queryAdvice cfg.lambda1 1
    let secant := l2Cur * l2Cur - (xANext + xRExpr cfg 0 + xACur)
    let yCheck :=
      (4 : Fp) * l2Cur * (xACur - xANext)
        - ((2 : Fp) * yAExpr cfg 0
            + ((2 : Fp) - qS3Expr cfg) * yAExpr cfg 1
            + qS3Expr cfg * (2 : Fp) * l1Next)
    Constraints.withSelector cfg.qS1
      [("secant line", secant), ("y check", yCheck)]

/-! ## The 3-tuple generator lookup

Rust `generator_table.rs:46-82`. The FIRST real 3-tuple lookup consumer in Halo2-Clean. The
input tuple (gated by `q_s1` and `q_run = q_s2 − q_s3`):

  `[ q_s1·word,                       ↦ table_idx
     q_s1·x_p + (1 − q_s1)·init_x,    ↦ table_x
     q_s1·y_p + (1 − q_s1)·init_y ]   ↦ table_y`

with `word = z_cur − q_run·z_next·2^K` (`z` = the `bits` column), `y_p = Y_A/2 − λ₁·(x_a − x_p)`
(`yPExpr`), and `(init_x, init_y) = S(0)`. On a used row `q_s1 = 1`, `q_run = 1`, so the input
is `(word, x_p, y_p)`; on an unused row it defaults to `S(0)` — exactly the disabled-row
convention. `tables` are the three table columns' rotation-0 fixed queries (via `lookup`).

The framework's `enableLookup` semantics compares the input LIST to the table LIST pointwise
(`Operations.lean:164-179`), so a 3-tuple membership reduces — via `List.map_cons`/`cons.injEq`
— to three per-column equalities at a *shared* usable table row. This is the "3-tuple
membership reduction" new shape pinned in `Clean/Halo2/Tests/`. -/
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

/-! ## Configure

Rust `SinsemillaConfig::configure` (`chip.rs`): allocate the selectors, take the handed-down
columns, register the two gates and the 3-tuple lookup. The generator-table columns are
handed down (loaded separately by `Basic.load`). -/
def configure (G : Generators) (fixedYQ : Column .fixed) (qS2 : Column .fixed)
    (xA xP lambda1 lambda2 bits : Column .advice) (genTable : GeneratorTableConfig) :
    Configure Fp Config := do
  enableEquality xA.toAny
  enableEquality lambda1.toAny
  enableEquality bits.toAny
  let qS1 ← complexSelector
  let qS4 ← selector
  let cfg : Config :=
    { qS1, qS2, qS4, fixedYQ, xA, xP, lambda1, lambda2, bits, generatorTable := genTable }
  createGate (initialYQGate cfg)
  createGate (sinsemillaGate cfg)
  -- register the 3-tuple lookup: three (input, tableColumn) pairs
  lookup [((generatorLookup G cfg).inputs[0]!, genTable.tableIdx),
          ((generatorLookup G cfg).inputs[1]!, genTable.tableX),
          ((generatorLookup G cfg).inputs[2]!, genTable.tableY)]
  return cfg

/-! ## Inputs / Output

Mirrors the donor `HashPiece.Input`/`Output`, region-level. The piece value and entering
accumulator `x_a` are already-assigned cells; the entering `y` is a prover hint (halo2's
`Y<Value>` wrapper). The output exposes the first/last rows, the exit `x_a`, and the running
sums `z_0 .. z_w`. -/

/-- Verifier-visible inputs: the piece value, the entering accumulator `x_a`, and the entering
accumulator `y`, as already-assigned cells / values. In Rust the entering `y` is threaded as
a `Y<Value>` prover hint (halo2's `Value` wrapper); slice-1 carries it as a plain `Inputs`
field (the honest witness programs read it; soundness never does), deferring the native-hint
wiring to slice 2. -/
structure Inputs (F : Type) where
  piece : F
  xA : F
  yA : F
deriving ProvableStruct

/-- Output: the first and last double-and-add rows, the exit `x_a` cell, and the piece's
`w + 1` running sums. -/
structure Output (numWords : ℕ) (F : Type) where
  first : DoubleAndAddRow F
  last : DoubleAndAddRow F
  xANext : F
  zs : Vector F numWords
deriving ProvableStruct

/-! ## Honest witness programs

The honest cell values chain through the recursive `accAfter`; they read the entering `y`
hint. Expressed via the witgen `native` escape hatch (`WitgenIROver.native`), as in
MulIncomplete's `zWit`/`l1Wit`/… . `readCell env c` reads an already-assigned input cell. -/

/-- Read an input cell's value in a placed prover environment. -/
def readCell (env : Placed ProverEnvironment Fp) (c : AssignedCell Fp) : Fp :=
  c.eval env.place env.env.toEnvironment

/-- The entering accumulator `y` value, read off the (already-assigned) input cell. -/
def yAIn (env : Placed ProverEnvironment Fp) (input : Inputs (AssignedCell Fp)) : Fp :=
  readCell env input.yA

/-- Honest running sum `z_r = ↑(piece.val ≫ (K·r))` at word `r`. Donor `pieceZ` as a witgen
program: cast to ℕ, shift right by `K·r` bits, cast back. -/
def zWit (input : Inputs (AssignedCell Fp)) (r : ℕ) : WitgenIR Fp 1 :=
  .ofFExpr (.ofNat (.div (.val (.expr input.piece)) (.const (2 ^ (K * r)))))

/-- Honest `x_p` at word `r`: the generator x-column read `S(pieceWord piece r).x`. Native
(reads the entering piece cell). -/
def xPWit (G : Generators) (input : Inputs (AssignedCell Fp)) (r : ℕ) : WitgenIR Fp 1 :=
  .native fun env => #v[(G.S (pieceWord (readCell env input.piece) r)).x]

/-- Honest `λ₁` at word `r` (`rowValue.1` of the `accAfter`-chained accumulator). Native. -/
def l1Wit (G : Generators) (input : Inputs (AssignedCell Fp)) (r : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    let p := readCell env input.piece
    let acc := accAfter G (readCell env input.xA, yAIn env input) p r
    #v[(rowValue acc ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1]

/-- Honest `λ₂` at word `r` (`rowValue.2.1`). Native. -/
def l2Wit (G : Generators) (input : Inputs (AssignedCell Fp)) (r : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    let p := readCell env input.piece
    let acc := accAfter G (readCell env input.xA, yAIn env input) p r
    #v[(rowValue acc ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.1]

/-- Honest next-row `x_a` after word `r` (`accAfter … (r+1)).1`). Native. -/
def xANextWit (G : Generators) (input : Inputs (AssignedCell Fp)) (r : ℕ) : WitgenIR Fp 1 :=
  .native fun env =>
    let p := readCell env input.piece
    #v[(accAfter G (readCell env input.xA, yAIn env input) p (r + 1)).1]

/-! ## The per-word round loop, in the MulIncomplete shape

A structurally recursive `RegionCircuit` over the word count, addressing cells by absolute
region-local rows (`offset + r`), so `(loop (k+1)).operations = (loop k).operations ++
(round k).operations` by `rfl`. Selectors: `q_s1` (in `sinsemillaGate.enable`) fires at each
row via the gate on adjacent pairs; the generator lookup fires at each word row.

Row layout (relative to `offset`, faithful to `hash_to_point.rs::hash_piece`):
- row `offset`     : `z_0` copy of the piece; loop word 0 begins here.
- word `r` at absolute row `offset + r`: assign `z_{r+1}` (at `offset + r + 1`), `x_p, λ₁, λ₂`,
  and the next-row `x_a` (at `offset + r + 1`); enable the generator lookup at `offset + r`.
- the Sinsemilla gate fires on adjacent word pairs `(r, r+1)` for `r < w`. -/

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

/-- One hash-word round at word index `r`, at absolute rows relative to `offset`. Assigns the
row cells, runs the generator lookup at row `offset + r`, and — for `r < w` — enables the
Sinsemilla gate at `offset + r` (adjacent pair `(r, r+1)`). Cells at fixed absolute rows so
round `r` is independent of the others.

`final` is Rust `hash_piece`'s `final_piece` flag: the last word row's `q_sinsemilla2` is `1`
interior, `qS2Boundary final` (`0` between pieces, `2` on the message's final piece) on the
last row. The interior running sum
`z_{r+1}` is assigned for `r < w` only — Rust assigns `z_1..z_w` and never the final `z_{w+1}`
("We do not assign the final z_n as it is constrained to be zero", `hash_to_point.rs`); row
`offset + w + 1` belongs to the next piece / the trailing dummy row, whose cells the composing
circuit owns. -/
def round (G : Generators) (cfg : Config) (input : Inputs (AssignedCell Fp))
    (final : Bool) (offset w r : ℕ) : RegionCircuit Fp Unit := do
  let row := offset + r
  if r < w then
    let _z ← assignAdvice cfg.bits (row + 1) (zWit input (r + 1))
    pure ()
  -- the `q_sinsemilla2` fixed value at this row (Rust `hash_piece`'s per-row
  -- `region.assign_fixed(q_sinsemilla2, …)`): `1` on interior word rows (the running word is
  -- `z_r − 2^K·z_{r+1}` and the gate's `q_s3 = 0`); on the last word row the word is `z_w`
  -- itself for both boundary values (`q_run = q_s2 − q_s3 = 0` at `q_s2 ∈ {0, 2}`).
  let _qs2 ← assignFixed cfg.qS2 row (if r = w then qS2Boundary final else 1)
  let _xP ← assignAdvice cfg.xP row (xPWit G input r)
  let _l1 ← assignAdvice cfg.lambda1 row (l1Wit G input r)
  let _l2 ← assignAdvice cfg.lambda2 row (l2Wit G input r)
  let _xANext ← assignAdvice cfg.xA (row + 1) (xANextWit G input r)
  -- the generator lookup at this word row (q_s1 on; the disabled-row convention handled
  -- by the input's `(1 − q_s1)·init` fallback at unused rows)
  (generatorLookup G cfg).enable [cfg.qS1] row
  -- the Sinsemilla gate on adjacent pairs (interior words only)
  if r < w then (sinsemillaGate cfg).enable row
  return ()

/-- The hash-word loop: `numWords` rounds, structurally recursive. By the append-bind of
`RegionCircuit`, `(loop … (k+1)).operations self = (loop … k).operations self ++
(round … k).operations self`. -/
def loop (G : Generators) (cfg : Config) (input : Inputs (AssignedCell Fp)) (final : Bool)
    (offset w : ℕ) : ℕ → RegionCircuit Fp Unit
  | 0 => pure ()
  | k + 1 => do
    loop G cfg input final offset w k
    round G cfg input final offset w k

/-- Per-round operations decomposition (holds by `rfl` via `operations_bind`) — the crux that
makes the loop inductable. Mirrors `MulIncomplete.loop_operations_succ`. -/
theorem loop_operations_succ (G : Generators) (cfg : Config) (input : Inputs (AssignedCell Fp))
    (final : Bool) (offset w k : ℕ) (self : RegionIndex) :
    (loop G cfg input final offset w (k + 1)).operations self
      = (loop G cfg input final offset w k).operations self
        ++ (round G cfg input final offset w k).operations self := rfl

/-- Read the assigned cell at a known region-local row/column (no op emitted). Lets
`synthesize` name the running-sum / accumulator cells for the `Output`. (`MulIncomplete.cellAt`.) -/
def cellAt (col : Column .advice) (row : ℕ) : RegionCircuit Fp (AssignedCell Fp) :=
  fun self => (.of self row col, [])

@[circuit_norm]
theorem operations_cellAt (col : Column .advice) (row : ℕ) (self : RegionIndex) :
    (cellAt col row).operations self = [] := rfl

@[circuit_norm]
theorem output_cellAt (col : Column .advice) (row : ℕ) (self : RegionIndex) :
    (cellAt col row).output self = .of self row col := rfl

/-! ## The pure per-row-facts → `Spec` bridge (`soundness_aux`, donor-proven, lifted)

Given the per-row lookup facts (`hL`: at each word the running word is a `< 2^K` generator
index `m` with `x_p = S(m).x` and the `y_p` derivation landing on `S(m).y`) and the per-pair
gate facts (`hG`: secant + y-check), plus the z-chain start (`hz0`) — produce the piece
`Spec`. Framework-agnostic: over `dR : ℕ → DoubleAndAddRow Fp`, `zV : ℕ → Fp`. Lifted from the
donor `HashPiece.soundness_aux`; this is the value-level heart the framework-half routes into. -/
theorem soundness_aux (G : Generators) (w : ℕ) (dR : ℕ → DoubleAndAddRow Fp) (zV : ℕ → Fp)
    (piece xA : Fp)
    (hxA0 : (dR 0).xA = xA)
    (hz0 : zV 0 = piece)
    (hL : ∀ r, r < w + 1 → ∃ m : ℕ, m < 2 ^ K ∧
      (if r = w then zV r else zV r - 2 ^ K * zV (r + 1)) = (m : Fp) ∧
      (dR r).xP = (G.S m).x ∧
      yA (dR r) * (2 : Fp)⁻¹ - (dR r).lambda1 * ((dR r).xA - (dR r).xP) = (G.S m).y)
    (hG : ∀ r, r < w →
      ((dR r).lambda2 * (dR r).lambda2
        = (dR (r + 1)).xA + ((dR r).lambda1 * (dR r).lambda1 - (dR r).xA - (dR r).xP)
          + (dR r).xA) ∧
      4 * (dR r).lambda2 * ((dR r).xA - (dR (r + 1)).xA)
        = 2 * yA (dR r) + 2 * yA (dR (r + 1))) :
    ∃ ms : ℕ → ℕ,
      (∀ r, ms r < 2 ^ K) ∧
      piece = ((∑ r ∈ Finset.range (w + 1), ms r * 2 ^ (K * r) : ℕ) : Fp) ∧
      Vector.ofFn (fun r : Fin (w + 1) => zV r.val) =
        Vector.ofFn (fun r : Fin (w + 1) =>
          ((∑ j ∈ Finset.range (w + 1 - r.val), ms (r.val + j) * 2 ^ (K * j) : ℕ) : Fp)) ∧
      (dR 0).xA = xA ∧
      (dR w).xP = (G.S (ms w)).x ∧
      yA (dR w) * (2 : Fp)⁻¹ - (dR w).lambda1 * ((dR w).xA - (dR w).xP) = (G.S (ms w)).y ∧
      ∀ A : Point Fp, A.OnCurve → A.x = xA →
        2 * A.y = yA (dR 0) →
        ∀ B, hashToPoint G.S A ((List.range w).map ms) = some B →
          (dR w).xA = B.x ∧ 2 * B.y = yA (dR w) := by
  -- choose the word values
  have hLE : ∀ r : Fin (w + 1), ∃ m : ℕ, m < 2 ^ K ∧
      (if r.val = w then zV r.val else zV r.val - 2 ^ K * zV (r.val + 1)) = (m : Fp) ∧
      (dR r.val).xP = (G.S m).x ∧
      yA (dR r.val) * (2 : Fp)⁻¹
        - (dR r.val).lambda1 * ((dR r.val).xA - (dR r.val).xP) = (G.S m).y :=
    fun r => hL r.val r.isLt
  choose mf hmf_lt hmf_word hmf_x hmf_y using hLE
  obtain ⟨ms, hms⟩ : ∃ ms : ℕ → ℕ, ms = fun r =>
      if h : r < w + 1 then mf ⟨r, h⟩ else 0 := ⟨_, rfl⟩
  have hms_lt : ∀ r, ms r < 2 ^ K := by
    intro r; simp only [hms]; split_ifs
    · exact hmf_lt _
    · norm_num [K]
  have hms_at : ∀ r (hr : r < w + 1), ms r = mf ⟨r, hr⟩ := by
    intro r hr; simp only [hms]; rw [dif_pos hr]
  -- recombination of the piece from its words
  have hpiece : piece = ((∑ r ∈ Finset.range (w + 1), ms r * 2 ^ (K * r) : ℕ) : Fp) := by
    rw [← hz0]
    have key : ∀ r, r ≤ w →
        zV 0 = ((∑ j ∈ Finset.range r, ms j * 2 ^ (K * j) : ℕ) : Fp)
          + zV r * ((2 ^ (K * r) : ℕ) : Fp) := by
      intro r hr
      induction r with
      | zero => simp
      | succ v ih =>
        have h := hmf_word ⟨v, by omega⟩
        rw [if_neg (show ¬ (⟨v, by omega⟩ : Fin (w + 1)).val = w by simp; omega)] at h
        rw [ih (by omega), Finset.sum_range_succ]
        rw [← hms_at v (by omega)] at h
        push_cast
        rw [show K * (v + 1) = K * v + K by ring]
        push_cast [pow_add]
        linear_combination ((2 : Fp) ^ (K * v)) * h
    have hlast : zV w = ((ms w : ℕ) : Fp) := by
      have h := hmf_word ⟨w, by omega⟩
      rw [if_pos rfl] at h
      rw [hms_at w (by omega)]; exact h
    rw [key w (by omega), hlast, Finset.sum_range_succ]
    push_cast; ring
  refine ⟨ms, hms_lt, hpiece, ?_, hxA0, ?_, ?_, ?_⟩
  · -- the running sums equal the suffix recombinations
    have hword : ∀ s, s < w → zV s = (ms s : Fp) + 2 ^ K * zV (s + 1) := by
      intro s hs
      have h := hmf_word ⟨s, by omega⟩
      rw [if_neg (show ¬ (⟨s, by omega⟩ : Fin (w + 1)).val = w by simp; omega)] at h
      rw [← hms_at s (by omega)] at h
      linear_combination h
    have hlast : zV w = (ms w : Fp) := by
      have h := hmf_word ⟨w, by omega⟩
      rw [if_pos rfl] at h
      rw [hms_at w (by omega)]; exact h
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    have h := chain_eq_suffix_sum zV ms hword hlast (w - i) i (by omega)
    rw [show w - i + 1 = w + 1 - i from by omega] at h
    exact h
  · rw [hms_at w (by omega)]; exact hmf_x ⟨w, by omega⟩
  · rw [hms_at w (by omega)]; exact hmf_y ⟨w, by omega⟩
  -- the chain invariant over message prefixes
  intro A hAon hAx hAyA B hchain
  have hinv : ∀ r, r ≤ w → ∀ Ar : Point Fp,
      hashToPoint G.S A ((List.range r).map ms) = some Ar →
      (dR r).xA = Ar.x ∧ 2 * Ar.y = yA (dR r) := by
    intro r
    induction r with
    | zero =>
      intro _ Ar hAr
      rw [show ((List.range 0).map ms) = ([] : List ℕ) from rfl,
        Orchard.Specs.Sinsemilla.hashToPoint_nil] at hAr
      obtain rfl : A = Ar := Option.some.inj hAr
      exact ⟨hxA0.trans hAx.symm, hAyA⟩
    | succ r ih =>
      intro hr Ar hAr
      rw [List.range_succ] at hAr
      simp only [List.map_append, List.map_cons, List.map_nil] at hAr
      rw [Orchard.Specs.Sinsemilla.hashToPoint_concat] at hAr
      cases hpre : hashToPoint G.S A ((List.range r).map ms) with
      | none => rw [hpre] at hAr; simp at hAr
      | some Ap =>
        rw [hpre] at hAr
        replace hAr : step G.S (ms r) Ap = some Ar := hAr
        obtain ⟨hxAr, hyAr⟩ := ih (by omega) Ap hpre
        have hxw := hmf_x ⟨r, by omega⟩
        have hyw := hmf_y ⟨r, by omega⟩
        rw [← hms_at r (by omega)] at hxw hyw
        obtain ⟨hsec, hyck⟩ := hG r (by omega)
        have hyAr' := hyAr
        simp only [yA, xR] at hyAr'
        -- `hyw : yA (dR r)/2 − λ₁·(x_a − x_p) = S(m).y`; clear the halving
        have hyw2 : yA (dR r) - 2 * ((dR r).lambda1 * ((dR r).xA - (dR r).xP))
            = 2 * (G.S (ms r)).y := by
          have h2 := congrArg (fun t => 2 * t) hyw
          simp only [mul_sub] at h2
          rw [show (2 : Fp) * (yA (dR r) * (2 : Fp)⁻¹) = yA (dR r) from by
            rw [mul_comm (yA (dR r)), ← mul_assoc,
              mul_inv_cancel₀ (by decide : (2 : Fp) ≠ 0), one_mul]] at h2
          linear_combination h2
        have hpin := step_coordinates_of_constraints G.S hAr
          (xp := (dR r).xP) (lambda1 := (dR r).lambda1) (lambda2 := (dR r).lambda2)
          (xa' := (dR (r + 1)).xA) (YA' := yA (dR (r + 1)))
          (by linear_combination hyw2 + hyAr + 2 * (dR r).lambda1 * hxAr)
          hxw
          (by linear_combination hyAr' + 2 * ((dR r).lambda1 + (dR r).lambda2) * hxAr)
          (by linear_combination hsec)
          (by linear_combination hyck - 4 * (dR r).lambda2 * hxAr - 2 * hyAr)
        exact ⟨hpin.1, hpin.2.symm⟩
  exact hinv w (by omega) B hchain

/-- A defined chain restricts to every prefix. Donor `HashPiece.range_prefix_some`. -/
theorem range_prefix_some (S : ℕ → Point Fp) (Q : Point Fp) (f : ℕ → ℕ) {n : ℕ} {B : Point Fp}
    (hn : hashToPoint S Q ((List.range n).map f) = some B)
    {r : ℕ} (hr : r ≤ n) :
    ∃ C, hashToPoint S Q ((List.range r).map f) = some C := by
  obtain ⟨k, rfl⟩ : ∃ k, n = r + k := ⟨n - r, by omega⟩
  rw [List.range_add, List.map_append, Orchard.Specs.Sinsemilla.hashToPoint_append] at hn
  cases hc : hashToPoint S Q ((List.range r).map f) with
  | none => rw [hc] at hn; simp at hn
  | some C => exact ⟨C, rfl⟩

/-- **The chain facts of one honest piece (completeness).** At every word `r ≤ w` the honest
row values satisfy the `Y_A` invariant (`(λ₁+λ₂)(x − x_R) = 2·acc.y`) and the `y_p` derivation
lands on the generator (`acc.y − λ₁(x − x_p) = S(m).y`); the piece exits at the spec-level
chain point. Donor `HashPiece.completeness_aux`, lifted verbatim (pure). -/
theorem completeness_aux (G : Generators) (w : ℕ) (p xA yA : Fp)
    {A B : Point Fp} (hAx : A.x = xA) (hAy : A.y = yA)
    (hchain : hashToPoint G.S A ((List.range (w + 1)).map (pieceWord p)) = some B) :
    (∀ r, r ≤ w →
      ((rowValue (accAfter G (xA, yA) p r)
            ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1
          + (rowValue (accAfter G (xA, yA) p r)
            ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.1)
        * ((accAfter G (xA, yA) p r).1
          - ((rowValue (accAfter G (xA, yA) p r)
                ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1
              * (rowValue (accAfter G (xA, yA) p r)
                ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1
            - (accAfter G (xA, yA) p r).1 - (G.S (pieceWord p r)).x))
        = 2 * (accAfter G (xA, yA) p r).2 ∧
      (accAfter G (xA, yA) p r).2
          - (rowValue (accAfter G (xA, yA) p r)
              ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1
            * ((accAfter G (xA, yA) p r).1 - (G.S (pieceWord p r)).x)
        = (G.S (pieceWord p r)).y) ∧
    accAfter G (xA, yA) p (w + 1) = (B.x, B.y) := by
  subst hAx hAy
  refine ⟨?_, accAfter_eq_chain G p hchain⟩
  intro r hr
  obtain ⟨Ar, hAr⟩ := range_prefix_some _ _ _ hchain (show r ≤ w + 1 by omega)
  obtain ⟨Ar1, hAr1⟩ := range_prefix_some _ _ _ hchain (show r + 1 ≤ w + 1 by omega)
  have hstep : step G.S (pieceWord p r) Ar = some Ar1 := by
    rw [List.range_succ] at hAr1
    simp only [List.map_append, List.map_cons, List.map_nil] at hAr1
    rw [Orchard.Specs.Sinsemilla.hashToPoint_concat, hAr] at hAr1
    exact hAr1
  have hacc := accAfter_eq_chain G p hAr
  have hh := step_honest G.S hstep
    (l1 := (rowValue (Ar.x, Ar.y)
      ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).1)
    (l2 := (rowValue (Ar.x, Ar.y)
      ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.1)
    (xa' := (rowValue (Ar.x, Ar.y)
      ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2.1)
    (ya' := (rowValue (Ar.x, Ar.y)
      ((G.S (pieceWord p r)).x, (G.S (pieceWord p r)).y)).2.2.2)
    rfl rfl rfl rfl
  rw [hacc]
  exact ⟨hh.2.1.symm, hh.1⟩

/-! ## The per-row cell readers off the environment

The double-and-add row and the running sum read at absolute region-local rows, in the
`soundness_aux` shape. Mirrors `MulIncomplete.adv`/`XAr`/… . -/

/-- Advice value of column `col` at region-local row `row`. -/
def adv (col : Column .advice) (place : RegionIndex → ℕ) (self : RegionIndex)
    (env : Environment Fp) (row : ℕ) : Fp :=
  env.advice col ((place self + row : ℕ) : ℤ)

/-- The double-and-add row read at word `r` (absolute row `offset + r`). The `x_a` of word `r`
is the entering accumulator cell for `r = 0` and the previous round's next-`x_a` otherwise;
here both live in the `x_a` column at row `offset + r`, written by round `r−1`'s
`xANextWit` (or the copy at `offset`). -/
def dRow (cfg : Config) (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp)
    (offset r : ℕ) : DoubleAndAddRow Fp :=
  { xA := adv cfg.xA place self env (offset + r),
    xP := adv cfg.xP place self env (offset + r),
    lambda1 := adv cfg.lambda1 place self env (offset + r),
    lambda2 := adv cfg.lambda2 place self env (offset + r) }

/-- The running sum read at word `r` (absolute row `offset + r`, the `bits`/`z` column). -/
def zRow (cfg : Config) (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp)
    (offset r : ℕ) : Fp :=
  adv cfg.bits place self env (offset + r)

/-! ## Loop-fact extraction (soundness)

Each round's `enableLookup`/`enableGate` constraint, cleaned to the value-level `hL`/`hG`
row equations `soundness_aux` consumes. Proven by induction over the word count using
`loop_operations_succ` + the append splitting of `RegionOperations.Constraints` — the
`MulIncomplete.loop_gate_facts` structure. The 3-tuple membership reduction (the NEW shape,
pinned in `Clean/Halo2/Tests/TestTupleLookup.lean`): the input list `[q_s1·word, …]` and
table list `[tableIdx, tableX, tableY]` map-equality at a shared usable row `t` splits into
three per-column equalities; `GeneratorTableLoaded`'s usable-rows spec then delivers the
generator triple `(m, S(m).x, S(m).y)` at `t`. -/

/-- **Per-word lookup facts (soundness).** From the loop's `Constraints` and the loaded
generator table, each word `r` yields a generator index `m < 2^K` with `x_p = S(m).x` and the
`y_p` derivation landing on `S(m).y`; the running word is `z_r − 2^K·z_{r+1}` on interior rows
and `z_r` on the last (the `q_s2` fixed-value case split). This is the `soundness_aux.hL`
shape. -/
theorem loop_lookup_facts (G : Generators) (cfg : Config) (input : Inputs (AssignedCell Fp))
    (final : Bool)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset w : ℕ)
    (hTable : GeneratorTableLoaded G cfg.generatorTable env)
    (hLoop : RegionOperations.Constraints place self env
      ((loop G cfg input final offset w (w + 1)).operations self)) :
    ∀ r, r < w + 1 → ∃ m : ℕ, m < 2 ^ K ∧
      (if r = w then zRow cfg place self env offset r
        else zRow cfg place self env offset r - 2 ^ K * zRow cfg place self env offset (r + 1))
        = (m : Fp) ∧
      (dRow cfg place self env offset r).xP = (G.S m).x ∧
      yA (dRow cfg place self env offset r) * (2 : Fp)⁻¹
        - (dRow cfg place self env offset r).lambda1
          * ((dRow cfg place self env offset r).xA - (dRow cfg place self env offset r).xP)
        = (G.S m).y := by
  obtain ⟨-, hSpec, -⟩ := hTable
  suffices h : ∀ numRounds : ℕ, numRounds ≤ w + 1 →
      RegionOperations.Constraints place self env
        ((loop G cfg input final offset w numRounds).operations self) →
      ∀ r, r < numRounds → ∃ m : ℕ, m < 2 ^ K ∧
        (if r = w then zRow cfg place self env offset r
          else zRow cfg place self env offset r
            - 2 ^ K * zRow cfg place self env offset (r + 1)) = (m : Fp) ∧
        (dRow cfg place self env offset r).xP = (G.S m).x ∧
        yA (dRow cfg place self env offset r) * (2 : Fp)⁻¹
          - (dRow cfg place self env offset r).lambda1
            * ((dRow cfg place self env offset r).xA - (dRow cfg place self env offset r).xP)
          = (G.S m).y from h (w + 1) le_rfl hLoop
  intro numRounds
  induction numRounds with
  | zero => intro _ _ r hr; omega
  | succ k ih =>
    intro hkb
    rw [loop_operations_succ, RegionOperations.constraints_append]
    rintro ⟨hLoopC, hRound⟩ r hr
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr' | rfl
    · exact ih (by omega) hLoopC r hr'
    · -- the fresh round `r`. Normalize the rotation-(+1) row spelling to `offset + (r + 1)`.
      have hz1 : ((place self + (offset + r) : ℕ) : ℤ) + 1
          = ((place self + (offset + (r + 1)) : ℕ) : ℤ) := by push_cast; ring
      by_cases hrw : r = w
      · -- last word row: `q_s2 = qS2Boundary final`, no gate, no z-assign; the word is `z_r`
        -- itself for both boundary values (`qS2Boundary_run`)
        subst hrw
        simp only [round, circuit_norm, generatorLookup, yPExpr, yAExpr, xRExpr, qS3Expr,
          List.mem_singleton, lt_irrefl, if_true, if_false, List.map_cons,
          List.map_nil, List.cons.injEq, and_true, one_mul, zero_mul, sub_self,
          add_zero, hz1] at hRound
        obtain ⟨hQ, t, ht, h0, h1, h2⟩ := hRound
        obtain ⟨m, hm, hIdx, hX, hY⟩ := hSpec t ht
        rw [hQ] at h0
        rw [hIdx] at h0
        rw [hX] at h1
        rw [hY] at h2
        refine ⟨m, hm, ?_, ?_, ?_⟩
        · rw [if_pos rfl]
          simp only [zRow, adv]
          linear_combination h0
            + env.advice cfg.bits ((place self + (offset + (r + 1)) : ℕ) : ℤ)
              * (2 : Fp) ^ K * qS2Boundary_run final
        · simp only [dRow, adv]
          linear_combination h1
        · simp only [dRow, adv, yA, xR]
          linear_combination h2
      · -- interior word row: `q_s2 = 1`, gate present (discarded); the word is the running one
        have hltw : r < w := by omega
        simp only [round, circuit_norm, generatorLookup, yPExpr, yAExpr, xRExpr, qS3Expr,
          List.mem_singleton, if_pos hltw, if_neg hrw, reduceIte, List.map_cons,
          List.map_nil, List.cons.injEq, and_true, one_mul, zero_mul, sub_self,
          add_zero, hz1] at hRound
        obtain ⟨hQ, ⟨t, ht, h0, h1, h2⟩, -⟩ := hRound
        obtain ⟨m, hm, hIdx, hX, hY⟩ := hSpec t ht
        rw [hQ] at h0
        rw [hIdx] at h0
        rw [hX] at h1
        rw [hY] at h2
        refine ⟨m, hm, ?_, ?_, ?_⟩
        · rw [if_neg hrw]
          simp only [zRow, adv]
          linear_combination h0
        · simp only [dRow, adv]
          linear_combination h1
        · simp only [dRow, adv, yA, xR]
          linear_combination h2

/-- **Per-pair gate facts (soundness).** From the loop's `Constraints`, each interior word
pair `(r, r+1)` (`r < w`) yields the Sinsemilla gate's secant + y-check equations — the
`soundness_aux.hG` shape. The `q_s3` term vanishes on interior rows (`q_s2 = 1` there by the
round's own `assignFixed`). -/
theorem loop_gate_facts (G : Generators) (cfg : Config) (input : Inputs (AssignedCell Fp))
    (final : Bool)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (offset w : ℕ)
    (hLoop : RegionOperations.Constraints place self env
      ((loop G cfg input final offset w (w + 1)).operations self)) :
    ∀ r, r < w →
      ((dRow cfg place self env offset r).lambda2 * (dRow cfg place self env offset r).lambda2
        = (dRow cfg place self env offset (r + 1)).xA
          + ((dRow cfg place self env offset r).lambda1
              * (dRow cfg place self env offset r).lambda1
              - (dRow cfg place self env offset r).xA - (dRow cfg place self env offset r).xP)
          + (dRow cfg place self env offset r).xA) ∧
      4 * (dRow cfg place self env offset r).lambda2
          * ((dRow cfg place self env offset r).xA - (dRow cfg place self env offset (r + 1)).xA)
        = 2 * yA (dRow cfg place self env offset r)
          + 2 * yA (dRow cfg place self env offset (r + 1)) := by
  suffices h : ∀ numRounds : ℕ, numRounds ≤ w + 1 →
      RegionOperations.Constraints place self env
        ((loop G cfg input final offset w numRounds).operations self) →
      ∀ r, r < numRounds → r < w →
        ((dRow cfg place self env offset r).lambda2 * (dRow cfg place self env offset r).lambda2
          = (dRow cfg place self env offset (r + 1)).xA
            + ((dRow cfg place self env offset r).lambda1
                * (dRow cfg place self env offset r).lambda1
                - (dRow cfg place self env offset r).xA
                - (dRow cfg place self env offset r).xP)
            + (dRow cfg place self env offset r).xA) ∧
        4 * (dRow cfg place self env offset r).lambda2
            * ((dRow cfg place self env offset r).xA
              - (dRow cfg place self env offset (r + 1)).xA)
          = 2 * yA (dRow cfg place self env offset r)
            + 2 * yA (dRow cfg place self env offset (r + 1)) from
    fun r hr => h (w + 1) le_rfl hLoop r (by omega) hr
  intro numRounds
  induction numRounds with
  | zero => intro _ _ r hr _; omega
  | succ k ih =>
    intro hkb
    rw [loop_operations_succ, RegionOperations.constraints_append]
    rintro ⟨hLoopC, hRound⟩ r hr hrw
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr' | rfl
    · exact ih (by omega) hLoopC r hr' hrw
    · -- the fresh round `r` (`r < w`, so its gate is enabled and its `q_s2 = 1`)
      have hz1 : ((place self + (offset + r) : ℕ) : ℤ) + 1
          = ((place self + (offset + (r + 1)) : ℕ) : ℤ) := by push_cast; ring
      simp only [round, circuit_norm, sinsemillaGate, yAExpr, xRExpr, qS3Expr,
        Constraints.withSelector, if_pos hrw, if_neg (show ¬ r = w by omega), reduceIte,
        List.map_cons, List.map_nil, and_true, one_mul,
        add_zero, hz1] at hRound
      obtain ⟨hQ, -, hsec, hyck⟩ := hRound
      rw [hQ] at hyck
      constructor
      · simp only [dRow, adv]
        linear_combination hsec
      · simp only [dRow, adv, yA, xR]
        linear_combination hyck

/-! ## Honest row values and loop constraints (completeness) -/

/-- **Honest row values (completeness).** The honest prover's `ExtendsWitnesses` of the loop
pins every round's cells to the donor's honest values: the running sum to `pieceZ`, the
`q_s2` fixed cell to its per-row value, `x_p` to the word's generator, `λ₁`/`λ₂` to the
`rowValue` slopes, and the next-row `x_a` to the chained accumulator. Standalone (raw
`input.*.eval` spelling) because a round's constraints read cells witnessed by *other*
rounds (the `z`/`x_a` predecessors) — the `MulIncomplete.loop_row_values` pattern. -/
theorem loop_row_values (G : Generators) (cfg : Config) (input : Inputs (AssignedCell Fp))
    (final : Bool)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment Fp) (offset w : ℕ) :
    ∀ numRounds : ℕ, numRounds ≤ w + 1 →
    RegionOperations.ExtendsWitnesses place self env
      ((loop G cfg input final offset w numRounds).operations self) →
    ∀ r, r < numRounds →
      (r < w → adv cfg.bits place self env.toEnvironment (offset + (r + 1))
          = pieceZ (input.piece.eval place env.toEnvironment) (r + 1)) ∧
      env.toEnvironment.fixed cfg.qS2 ((place self + (offset + r) : ℕ) : ℤ)
          = (if r = w then qS2Boundary final else 1) ∧
      adv cfg.xP place self env.toEnvironment (offset + r)
          = (G.S (pieceWord (input.piece.eval place env.toEnvironment) r)).x ∧
      adv cfg.lambda1 place self env.toEnvironment (offset + r)
          = (rowValue (accAfter G (input.xA.eval place env.toEnvironment,
                input.yA.eval place env.toEnvironment)
                (input.piece.eval place env.toEnvironment) r)
              ((G.S (pieceWord (input.piece.eval place env.toEnvironment) r)).x,
               (G.S (pieceWord (input.piece.eval place env.toEnvironment) r)).y)).1 ∧
      adv cfg.lambda2 place self env.toEnvironment (offset + r)
          = (rowValue (accAfter G (input.xA.eval place env.toEnvironment,
                input.yA.eval place env.toEnvironment)
                (input.piece.eval place env.toEnvironment) r)
              ((G.S (pieceWord (input.piece.eval place env.toEnvironment) r)).x,
               (G.S (pieceWord (input.piece.eval place env.toEnvironment) r)).y)).2.1 ∧
      adv cfg.xA place self env.toEnvironment (offset + (r + 1))
          = (accAfter G (input.xA.eval place env.toEnvironment,
                input.yA.eval place env.toEnvironment)
              (input.piece.eval place env.toEnvironment) (r + 1)).1 := by
  intro numRounds
  induction numRounds with
  | zero => intro _ _ r hr; omega
  | succ k ih =>
    intro hkb hW r hr
    rw [loop_operations_succ, RegionOperations.extendsWitnesses_append] at hW
    obtain ⟨hWloop, hWround⟩ := hW
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr' | rfl
    · exact ih (by omega) hWloop r hr'
    · -- the fresh round `r`'s own witnesses (the z-assign exists on interior rows only)
      by_cases hrw : r < w
      · simp only [round, circuit_norm, zWit, xPWit, l1Wit, l2Wit, xANextWit, readCell, yAIn,
          AssignedCell.eval, if_pos hrw] at hWround
        obtain ⟨hWz, hWq, hWxp, hWl1, hWl2, hWxa⟩ := hWround
        simp only [adv, show offset + (r + 1) = offset + r + 1 from by omega]
        refine ⟨fun _ => ?_, hWq, hWxp, hWl1, hWl2, hWxa⟩
        -- the z-witness program evaluates to `↑(piece.val / 2^{K(r+1)})` = `pieceZ piece (r+1)`
        simp only [pieceZ]
        convert hWz using 2
      · simp only [round, circuit_norm, zWit, xPWit, l1Wit, l2Wit, xANextWit, readCell, yAIn,
          AssignedCell.eval, if_neg hrw] at hWround
        obtain ⟨hWq, hWxp, hWl1, hWl2, hWxa⟩ := hWround
        simp only [adv, show offset + (r + 1) = offset + r + 1 from by omega]
        exact ⟨fun h => absurd h hrw, hWq, hWxp, hWl1, hWl2, hWxa⟩

/-- **Completeness loop-constraints lemma.** Given the honest row values (the loop's own
witnesses), the entering copies (`hz0`: the `z_0` piece copy; `hxA0cell`: the `x_a` copy —
both emitted *outside* the loop, discharged by the bundle), the loaded generator table, and
the honest-prover chain preconditions, the loop's `Constraints` hold: each round's
`assignFixed` is its witness, each membership is witnessed at the honest word's own table row,
and each gate holds by the honest-value algebra (`completeness_aux` + `rowValue` identities). -/
theorem loop_constraints_complete (G : Generators) (cfg : Config)
    (input : Inputs (AssignedCell Fp)) (final : Bool)
    (place : RegionIndex → ℕ) (self : RegionIndex) (env : ProverEnvironment Fp) (offset w : ℕ)
    (A B : Point Fp)
    (hAx : A.x = input.xA.eval place env.toEnvironment)
    (hAy : A.y = input.yA.eval place env.toEnvironment)
    (hchain : hashToPoint G.S A
      ((List.range (w + 1)).map (pieceWord (input.piece.eval place env.toEnvironment)))
      = some B)
    (hPieceLt : (input.piece.eval place env.toEnvironment).val < 2 ^ (K * (w + 1)))
    (hTable : GeneratorTableLoaded G cfg.generatorTable env.toEnvironment)
    (hz0 : adv cfg.bits place self env.toEnvironment offset
      = input.piece.eval place env.toEnvironment)
    (hxA0cell : adv cfg.xA place self env.toEnvironment offset
      = input.xA.eval place env.toEnvironment)
    (hWit : RegionOperations.ExtendsWitnesses place self env
      ((loop G cfg input final offset w (w + 1)).operations self)) :
    RegionOperations.Constraints place self env.toEnvironment
      ((loop G cfg input final offset w (w + 1)).operations self) := by
  obtain ⟨hUsable, -, hBlock⟩ := hTable
  -- shorthands for the honest values
  set P := input.piece.eval place env.toEnvironment with hP
  set XA := input.xA.eval place env.toEnvironment with hXA
  set YA := input.yA.eval place env.toEnvironment with hYA
  -- the chain facts of the honest piece (`Y_A` invariant + `y_p` derivation per word)
  obtain ⟨hAux, -⟩ := completeness_aux G w P XA YA hAx hAy hchain
  -- global honest row values (a round's constraints read neighbor rows' witnesses)
  have hRows := loop_row_values G cfg input final place self env offset w (w + 1) le_rfl hWit
  -- current-row `x_a` (row 0: the entering copy; row `r ≥ 1`: round `r−1`'s next-`x_a`)
  have hXcur : ∀ r, r ≤ w → adv cfg.xA place self env.toEnvironment (offset + r)
      = (accAfter G (XA, YA) P r).1 := by
    intro r hrw
    rcases Nat.eq_zero_or_pos r with rfl | hrpos
    · simpa only [accAfter, Nat.add_zero] using hxA0cell
    · have h := (hRows (r - 1) (by omega)).2.2.2.2.2
      rw [show r - 1 + 1 = r from by omega] at h
      exact h
  -- current-row `z` (row 0: the piece copy; row `r ≥ 1`: round `r−1`'s z-witness)
  have hZcur : ∀ r, r ≤ w → adv cfg.bits place self env.toEnvironment (offset + r)
      = pieceZ P r := by
    intro r hrw
    rcases Nat.eq_zero_or_pos r with rfl | hrpos
    · rw [Nat.add_zero, hz0, pieceZ_zero]
    · have h := (hRows (r - 1) (by omega)).1 (by omega)
      rw [show r - 1 + 1 = r from by omega] at h
      exact h
  -- ⟨2⁻¹·2 = 1⟩, for halving the `Y_A` invariant in the `y_p` membership component
  have h2inv : (2 : Fp)⁻¹ * 2 = 1 := inv_mul_cancel₀ (by decide)
  -- the per-round induction
  suffices h : ∀ numRounds : ℕ, numRounds ≤ w + 1 →
      RegionOperations.Constraints place self env.toEnvironment
        ((loop G cfg input final offset w numRounds).operations self) from h (w + 1) le_rfl
  intro numRounds
  induction numRounds with
  | zero => intro _; exact trivial
  | succ k ih =>
    intro hkb
    rw [loop_operations_succ, RegionOperations.constraints_append]
    refine ⟨ih (by omega), ?_⟩
    have hkw : k ≤ w := by omega
    -- the fresh round `k`'s honest cells
    obtain ⟨hVz, hVq, hVxp, hVl1, hVl2, hVxa⟩ := hRows k (by omega)
    have hVxcur := hXcur k hkw
    have hVzcur := hZcur k hkw
    -- the chain facts at word `k`
    obtain ⟨hYAinv, hYPder⟩ := hAux k hkw
    -- row normalizer for rotation-(+1) reads
    have hz1 : ((place self + (offset + k) : ℕ) : ℤ) + 1
        = ((place self + (offset + (k + 1)) : ℕ) : ℤ) := by push_cast; ring
    -- expose the raw env spellings
    simp only [adv] at hVz hVxp hVl1 hVl2 hVxa hVxcur hVzcur
    by_cases hkweq : k = w
    · -- ── last word row: `q_s2 = qS2Boundary final`, word = `z_w`, no gate, no z-assign ──
      subst hkweq
      simp only [round, circuit_norm, generatorLookup, yPExpr, yAExpr, xRExpr, qS3Expr,
        List.mem_singleton, lt_irrefl, if_true, if_false, List.map_cons,
        List.map_nil, List.cons.injEq, and_true, one_mul, zero_mul, sub_self,
        add_zero, hz1]
      rw [if_pos rfl] at hVq
      refine ⟨hVq, ?_⟩
      -- membership witnessed at the honest word's own table row (`w` was substituted to `k`)
      refine ⟨pieceWord P k, lt_of_lt_of_le (pieceWord_lt P k) hUsable, ?_, ?_, ?_⟩
      · -- word component: the boundary `q_run` vanishes (`qS2Boundary_run`), word = `z_k`
        -- (pieceZ_last)
        rw [hVq, hVzcur, (hBlock _ (pieceWord_lt P k)).1]
        rw [pieceZ_last hPieceLt]
        linear_combination
          (-(env.toEnvironment.advice cfg.bits ((place self + (offset + (k + 1)) : ℕ) : ℤ))
            * (2 : Fp) ^ K) * qS2Boundary_run final
      · -- x component
        rw [hVxp, (hBlock _ (pieceWord_lt P k)).2.1]
      · -- y component: halve the `Y_A` invariant, then the `y_p` derivation
        rw [hVl1, hVl2, hVxcur, hVxp, (hBlock _ (pieceWord_lt P k)).2.2]
        linear_combination (2 : Fp)⁻¹ * hYAinv + hYPder
          + (accAfter G (XA, YA) P k).2 * h2inv
    · -- ── interior word row: `q_s2 = 1`, word = running word, gate on ──
      have hklt : k < w := by omega
      simp only [round, circuit_norm, generatorLookup, sinsemillaGate, yPExpr, yAExpr,
        xRExpr, qS3Expr, Constraints.withSelector, List.mem_singleton, if_pos hklt,
        if_neg hkweq, reduceIte, List.map_cons, List.map_nil, List.cons.injEq, and_true,
        one_mul, zero_mul, sub_self, add_zero, hz1]
      rw [if_neg hkweq] at hVq
      -- next word's honest cells and chain facts (for the gate's rotation-(+1) reads)
      obtain ⟨-, -, hVxp1, hVl1', hVl2', -⟩ := hRows (k + 1) (by omega)
      obtain ⟨hYAinv1, -⟩ := hAux (k + 1) (by omega)
      simp only [adv] at hVxp1 hVl1' hVl2'
      refine ⟨hVq, ⟨pieceWord P k, lt_of_lt_of_le (pieceWord_lt P k) hUsable, ?_, ?_, ?_⟩,
        ?_, ?_⟩
      · -- word component: `z_k − 1·z_{k+1}·2^K = ↑(pieceWord P k)` (pieceZ_succ)
        rw [hVq, hVzcur, hVz hklt, (hBlock _ (pieceWord_lt P k)).1]
        have h := pieceZ_succ P k
        linear_combination h
      · rw [hVxp, (hBlock _ (pieceWord_lt P k)).2.1]
      · rw [hVl1, hVl2, hVxcur, hVxp, (hBlock _ (pieceWord_lt P k)).2.2]
        linear_combination (2 : Fp)⁻¹ * hYAinv + hYPder
          + (accAfter G (XA, YA) P k).2 * h2inv
      · -- gate, secant line: `rowValue`'s `xANext` identity, by `ring` after unfolding
        rw [hVl1, hVl2, hVxcur, hVxp, hVxa]
        simp only [rowValue, accAfter]
        ring
      · -- gate, y check (`q_s3 = 0`): the two `Y_A` invariants + `rowValue`'s `yANext`
        rw [hVq, hVl1, hVl2, hVxcur, hVxp, hVxa, hVl1', hVl2', hVxp1]
        -- `Y_A(k) = 2·acc_k.y`, `Y_A(k+1) = 2·acc_{k+1}.y`, and
        -- `λ₂·(acc_k.x − acc_{k+1}.x) = acc_{k+1}.y + acc_k.y` (the `yANext` definition)
        have hyd : (rowValue (accAfter G (XA, YA) P k)
              ((G.S (pieceWord P k)).x, (G.S (pieceWord P k)).y)).2.1
              * ((accAfter G (XA, YA) P k).1 - (accAfter G (XA, YA) P (k + 1)).1)
            = (accAfter G (XA, YA) P (k + 1)).2 + (accAfter G (XA, YA) P k).2 := by
          conv_lhs => rw [show accAfter G (XA, YA) P (k + 1)
            = (rowValue (accAfter G (XA, YA) P k)
                ((G.S (pieceWord P k)).x, (G.S (pieceWord P k)).y)).2.2 from rfl]
          conv_rhs => rw [show accAfter G (XA, YA) P (k + 1)
            = (rowValue (accAfter G (XA, YA) P k)
                ((G.S (pieceWord P k)).x, (G.S (pieceWord P k)).y)).2.2 from rfl]
          simp only [rowValue]
          ring
        linear_combination 4 * hyd - 2 * hYAinv - 2 * hYAinv1

/-! ## Contract

The `FormalRegionCircuit` bundle for one hash piece with `w + 1` words. `EnvAssumptions` is
the loaded generator table (`GeneratorTableLoaded`; discharged by `Basic.load_generatorTableLoaded`).
`Spec` is the donor `HashPiece.Spec`: the piece is the base-`2^K` recombination of its `< 2^K`
words, the running sums are the suffix recombinations, and — for any on-curve entering
accumulator `A` matching the first row's `x_a`/`Y_A` — the exit `x_a`/`Y_A` are the spec-level
`hashToPoint` chain point over the first `w` words. -/

/-- Name a whole vector of cells at fixed region-local rows (no op emitted) — the vector-valued
`cellAt`, for `Output.zs`. (`MulIncomplete.cellVec`.) -/
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

/-- Entering `x_a` copy + running-sum `z_0` copy, then the loop, then the output cells. The
`synthesize` body. The output rows and running sums live at fixed absolute rows and are named
by `cellAt`/`cellVec` (no ops). -/
def synthesize (G : Generators) (w : ℕ) (final : Bool) (cfg : Config) (offset : ℕ)
    (input : Inputs (AssignedCell Fp)) : RegionCircuit Fp (Var (Output (w + 1)) Fp) := do
  -- z_0 = copy of the piece into the `bits`/`z` column at `offset`
  let _z0 ← copyAdvice input.piece cfg.bits offset
  -- x_a at `offset` = copy of the entering accumulator x
  let _xA0 ← copyAdvice input.xA cfg.xA offset
  -- the hash-word loop: `w + 1` rounds, gate bound `w` (in-piece gates on adjacent pairs
  -- only — the piece-linking gate at the last word row belongs to the composing circuit,
  -- the donor's boundary choice)
  loop G cfg input final offset w (w + 1)
  -- name the output cells (fixed rows)
  let first0 ← cellAt cfg.xA offset
  let firstXP ← cellAt cfg.xP offset
  let firstL1 ← cellAt cfg.lambda1 offset
  let firstL2 ← cellAt cfg.lambda2 offset
  let last0 ← cellAt cfg.xA (offset + w)
  let lastXP ← cellAt cfg.xP (offset + w)
  let lastL1 ← cellAt cfg.lambda1 (offset + w)
  let lastL2 ← cellAt cfg.lambda2 (offset + w)
  let xANext ← cellAt cfg.xA (offset + (w + 1))
  let zsCells ← cellVec cfg.bits (fun r => offset + r) (w + 1)
  return {
    first := { xA := first0, xP := firstXP, lambda1 := firstL1, lambda2 := firstL2 },
    last := { xA := last0, xP := lastXP, lambda1 := lastL1, lambda2 := lastL2 },
    xANext := xANext,
    zs := zsCells }

/-- The piece `Spec` (donor `HashPiece.Spec`), verifier view. The piece is the base-`2^K`
recombination of its `< 2^K` words, the running sums are the suffix recombinations, the first
row starts at the entering `x_a`, the last row's `x_p`/`y_p` land on `S(m_w)`, and — for any
on-curve entering accumulator `A` matching the first row's `x_a`/`Y_A` — the exit `x_a`/`Y_A`
are the spec-level `hashToPoint` chain point over the first `w` words. -/
def Spec (G : Generators) (w : ℕ) (input : Value Inputs Fp)
    (output : Value (Output (w + 1)) Fp) (_ : Unit) : Prop :=
  ∃ ms : ℕ → ℕ,
    (∀ r, ms r < 2 ^ K) ∧
    input.piece = ((∑ r ∈ Finset.range (w + 1), ms r * 2 ^ (K * r) : ℕ) : Fp) ∧
    output.zs = Vector.ofFn (fun r : Fin (w + 1) =>
      ((∑ j ∈ Finset.range (w + 1 - r.val), ms (r.val + j) * 2 ^ (K * j) : ℕ) : Fp)) ∧
    output.first.xA = input.xA ∧
    output.last.xP = (G.S (ms w)).x ∧
    yA output.last * (2 : Fp)⁻¹
      - output.last.lambda1 * (output.last.xA - output.last.xP) = (G.S (ms w)).y ∧
    ∀ A : Point Fp, A.OnCurve → A.x = input.xA →
      2 * A.y = yA output.first →
      ∀ B, hashToPoint G.S A ((List.range w).map ms) = some B →
        output.last.xA = B.x ∧ 2 * B.y = yA output.last

/-- The entering-accumulator honest precondition (donor `HashPiece.ProverAssumptions`): the
piece fits in `K·(w+1)` bits, and the spec-level chain over its chunks is defined
(non-exceptional). -/
def ProverAssumptions (G : Generators) (w : ℕ) (input : Value Inputs Fp) : Prop :=
  input.piece.val < 2 ^ (K * (w + 1)) ∧
  ∃ (A B : Point Fp), A.OnCurve ∧ A.x = input.xA ∧ A.y = input.yA ∧
    hashToPoint G.S A ((List.range (w + 1)).map (pieceWord input.piece)) = some B

/-- The honest-prover contract (donor `HashPiece.ProverSpec`), required by a COMPOSING
circuit's completeness: the verifier-side `Spec` cannot expose honest-cell facts, but the
parent must discharge the piece-linking gate on the honest values. For the honest entering
accumulator `(input.xA, input.yA)` with exit chain point `B`:

- the first row's derived `Y_A` is `2·y_enter` (the parent's own caller consumes this via
  `enterYA`);
- the exit `x_a` cell is `B.x`;
- the last row completes its step's secant against the exit `x_a` (the linking gate's
  "secant line" on honest values);
- the `nextYA` derivation `2·λ₂·(x_a − x_a_next) − Y_A` lands on `2·B.y` (the linking gate's
  "y check" on honest values, together with the *next* level's own first-row `Y_A` fact). -/
def ProverSpec (G : Generators) (w : ℕ) (input : Value Inputs Fp)
    (output : Value (Output (w + 1)) Fp) (_ : Unit) : Prop :=
  ∀ (A B : Point Fp), A.x = input.xA → A.y = input.yA →
    hashToPoint G.S A ((List.range (w + 1)).map (pieceWord input.piece)) = some B →
    yA output.first = 2 * A.y ∧
    output.xANext = B.x ∧
    output.last.lambda2 * output.last.lambda2
      = output.xANext + xR output.last + output.last.xA ∧
    2 * output.last.lambda2 * (output.last.xA - output.xANext) - yA output.last = 2 * B.y

instance elaborated (G : Generators) (w : ℕ) (final : Bool) (cfg : Config) (offset : ℕ) :
    ElaboratedRegionCircuit Fp Inputs (Output (w + 1)) (synthesize G w final cfg offset) := {}

/-- The hash-piece region circuit bundle. `EnvAssumptions` is the loaded generator table;
`Spec` is `Spec` above. `configure` is the identity on the handed-down `Config` (the columns
are allocated by the parent chip's `configure`).

Soundness peels `synthesize`'s op list into the two start-copies ++ the (folded) loop ++
output-cell reads, extracts the per-row `hL`/`hG` facts via `loop_lookup_facts`/
`loop_gate_facts`, and hands them to `soundness_aux` — the donor `HashPiece.soundness`
restated over `dRow`/`zRow`. Completeness discharges the two copies from their witnesses
and the loop via `loop_constraints_complete` on the honest-prover chain preconditions. -/
def circuit (G : Generators) (w : ℕ) (final : Bool) :
    FormalRegionCircuit Fp Config Config Inputs (Output (w + 1)) where
  name := "sinsemilla hash_piece"
  configure := fun cfg => pure cfg
  synthesize cfg offset input := synthesize G w final cfg offset input
  EnvAssumptions cfg env := GeneratorTableLoaded G cfg.generatorTable env.env
  Assumptions _ := True
  Spec := Spec G w
  ProverAssumptions input _ _ := ProverAssumptions G w input
  ProverSpec input output _ _ := ProverSpec G w input output ()
  soundness := by
    -- loop-based composite: the universal prefix (intro + `soundness_iff` + house names, the
    -- synthesize op-list peel below, and `provable_type_simp`) runs; the folded loop chunk keeps the
    -- goal composite, so the leaf-only finish is skipped and `hc`/`h_input`/`h_output` survive.
    -- peel the synthesize op list: two copies ++ loop (kept folded) ++ output reads (no ops)
    circuit_proof_start [HashPiece.synthesize]
    obtain ⟨hZ0, hXA0, hLoop⟩ := hc
    -- reconstruct the input record so the loop lemmas' `input` argument matches `hLoop`
    set inp : Inputs (AssignedCell Fp) :=
      { piece := input_var_piece, xA := input_var_xA, yA := input_var_yA } with hinp
    obtain ⟨hIpiece, hIxA, hIyA⟩ := h_input
    -- `circuit_proof_start` (via `provable_type_simp`) destructured `output` and split `h_output`
    -- into per-field atom-left cell equations. Fold to `dRow`/`zRow`, reassembling the whole-row
    -- and per-index facts the induction consumes.
    have hOfirst : (⟨output_first_xA, output_first_xP, output_first_lambda1, output_first_lambda2⟩
        : DoubleAndAddRow Fp) = dRow cfg env.place self env.env offset 0 := by
      rw [← h_output_first_xA, ← h_output_first_xP, ← h_output_first_lambda1,
        ← h_output_first_lambda2]
      rfl
    have hOlast : (⟨output_last_xA, output_last_xP, output_last_lambda1, output_last_lambda2⟩
        : DoubleAndAddRow Fp) = dRow cfg env.place self env.env offset w := by
      rw [← h_output_last_xA, ← h_output_last_xP, ← h_output_last_lambda1,
        ← h_output_last_lambda2]
      rfl
    have hOzs : ∀ (i : ℕ) (hi : i < w + 1),
        output_zs[i] = zRow cfg env.place self env.env offset i := by
      intro i hi
      simp only [zRow, adv]
      exact (h_output_zs i hi).symm
    -- start copies: `zRow 0 = input.piece`, `(dRow 0).xA = input.xA`
    have hz0 : zRow cfg env.place self env.env offset 0 = input_piece := by
      simp only [zRow, adv, Nat.add_zero]
      rw [hZ0]
      exact hIpiece
    have hxA0 : (dRow cfg env.place self env.env offset 0).xA = input_xA := by
      simp only [dRow, adv, Nat.add_zero]
      rw [hXA0]
      exact hIxA
    -- the extraction lemmas + the pure bridge
    have hL := loop_lookup_facts G cfg inp final env.place self env.env offset w _hE hLoop
    have hG := loop_gate_facts G cfg inp final env.place self env.env offset w hLoop
    obtain ⟨ms, hms_lt, hpiece, hzs, hfxA, hlxP, hlyP, hchain⟩ :=
      soundness_aux G w (dRow cfg env.place self env.env offset)
        (zRow cfg env.place self env.env offset) input_piece input_xA hxA0 hz0 hL hG
    -- pointwise running-sum values from the vector equation
    have hzs' : ∀ (i : ℕ) (hi : i < w + 1),
        zRow cfg env.place self env.env offset i
          = ((∑ j ∈ Finset.range (w + 1 - i), ms (i + j) * 2 ^ (K * j) : ℕ) : Fp) := by
      intro i hi
      have h := congrArg (fun v : Vector Fp (w + 1) => v[i]'hi) hzs
      simpa only [Vector.getElem_ofFn] using h
    refine ⟨ms, hms_lt, hpiece, ?_, ?_, ?_, ?_, ?_⟩
    · -- the running sums are the suffix recombinations
      apply Vector.ext
      intro i hi
      rw [Vector.getElem_ofFn, hOzs i hi, hzs' i hi]
    · rw [hOfirst]; exact hfxA
    · rw [hOlast]; exact hlxP
    · rw [hOlast]; exact hlyP
    · rw [hOfirst, hOlast]; exact hchain
  completeness := by
    -- loop-based composite: the universal prefix (intro + `completeness_iff` + house names, the
    -- witness/op-list peel below, and `provable_type_simp`) runs; the folded loop witness chunk keeps
    -- the goal composite, so the leaf-only finish is skipped and `hwit`/`h_input`/`hPA`/`_hE` survive.
    circuit_proof_start [HashPiece.synthesize]
    obtain ⟨hWz0, hWxA0, hWloop⟩ := hwit
    set inp : Inputs (AssignedCell Fp) :=
      { piece := input_var_piece, xA := input_var_xA, yA := input_var_yA } with hinp
    obtain ⟨hIpiece, hIxA, hIyA⟩ := h_input
    obtain ⟨hPieceLt, A, B, hAon, hAx, hAy, hchain⟩ := hPA
    -- normalize the env-assumption spelling to the prover env
    simp only [Placed.toEnvironment_env] at _hE
    -- `provable_type_simp` (in `circuit_proof_start`) destructured `output` and split `h_output`
    -- component-wise (prover view); read the struct-row/scalar/vector components off the conjunction.
    have hOfirst : (⟨output_first_xA, output_first_xP, output_first_lambda1, output_first_lambda2⟩
        : DoubleAndAddRow Fp) = dRow cfg env.place self env.env.toEnvironment offset 0 := by
      rw [← h_output_first_xA, ← h_output_first_xP, ← h_output_first_lambda1,
        ← h_output_first_lambda2]
      rfl
    have hOlast : (⟨output_last_xA, output_last_xP, output_last_lambda1, output_last_lambda2⟩
        : DoubleAndAddRow Fp) = dRow cfg env.place self env.env.toEnvironment offset w := by
      rw [← h_output_last_xA, ← h_output_last_xP, ← h_output_last_lambda1,
        ← h_output_last_lambda2]
      rfl
    have hOxANext : output_xANext
        = adv cfg.xA env.place self env.env.toEnvironment (offset + (w + 1)) :=
      h_output_xANext.symm
    have hOl_xA : adv cfg.xA env.place self env.env.toEnvironment (offset + w)
        = output_last_xA := h_output_last_xA
    have hOl_xP : adv cfg.xP env.place self env.env.toEnvironment (offset + w)
        = output_last_xP := h_output_last_xP
    have hOl_l1 : adv cfg.lambda1 env.place self env.env.toEnvironment (offset + w)
        = output_last_lambda1 := h_output_last_lambda1
    have hOl_l2 : adv cfg.lambda2 env.place self env.env.toEnvironment (offset + w)
        = output_last_lambda2 := h_output_last_lambda2
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · -- the piece copy's `constrainEqual`, from its `assignAdvice` witness
      rw [hWz0]
    · -- the `x_a` copy's `constrainEqual`
      rw [hWxA0]
    · -- the loop's constraints, from the honest witnesses + the chain preconditions
      refine loop_constraints_complete G cfg inp final env.place self env.env offset w A B
        ?_ ?_ ?_ ?_ _hE ?_ ?_ hWloop
      · rw [hAx]; exact hIxA.symm
      · rw [hAy]; exact hIyA.symm
      · rw [show inp.piece.eval env.place env.env.toEnvironment = input_piece from hIpiece]
        exact hchain
      · rw [show inp.piece.eval env.place env.env.toEnvironment = input_piece from hIpiece]
        exact hPieceLt
      · -- `z_0` copy witness pins the entering running sum
        simp only [adv]
        rw [hWz0]
        rfl
      · -- `x_a` copy witness pins the entering accumulator cell
        simp only [adv]
        rw [hWxA0]
        rfl
    · -- ── ProverSpec: the honest-cell facts a composing parent's completeness consumes ──
      simp only [HashPiece.ProverSpec]
      intro A' B' hA'x hA'y hchain'
      -- honest-value shorthands (the loop lemmas' spellings)
      have hxA0cell : adv cfg.xA env.place self env.env.toEnvironment offset
          = inp.xA.eval env.place env.env.toEnvironment := by
        simp only [adv]; rw [hWxA0]; rfl
      -- entering-point coordinates in the loop-lemma spelling
      have hA'x' : A'.x = inp.xA.eval env.place env.env.toEnvironment := by
        rw [hA'x]; exact hIxA.symm
      have hA'y' : A'.y = inp.yA.eval env.place env.env.toEnvironment := by
        rw [hA'y]; exact hIyA.symm
      have hchainP : hashToPoint G.S A' ((List.range (w + 1)).map
          (pieceWord (inp.piece.eval env.place env.env.toEnvironment))) = some B' := by
        rw [show inp.piece.eval env.place env.env.toEnvironment = input_piece from hIpiece]
        exact hchain'
      -- the honest chain facts + the exit accumulator
      obtain ⟨hAux, hAccB⟩ := completeness_aux G w
        (inp.piece.eval env.place env.env.toEnvironment)
        (inp.xA.eval env.place env.env.toEnvironment)
        (inp.yA.eval env.place env.env.toEnvironment) hA'x' hA'y' hchainP
      obtain ⟨hYAinv0, -⟩ := hAux 0 (by omega)
      obtain ⟨hYAinvw, -⟩ := hAux w le_rfl
      -- the honest row values
      have hRows := loop_row_values G cfg inp final env.place self env.env offset w (w + 1)
        le_rfl hWloop
      obtain ⟨-, -, hVxp0, hVl10, hVl20, -⟩ := hRows 0 (by omega)
      obtain ⟨-, -, hVxpw, hVl1w, hVl2w, hVxaw⟩ := hRows w (by omega)
      -- current-row `x_a` at the last row (row 0: the entering copy; else round w−1's next-x_a)
      have hXcurw : adv cfg.xA env.place self env.env.toEnvironment (offset + w)
          = (accAfter G (inp.xA.eval env.place env.env.toEnvironment,
              inp.yA.eval env.place env.env.toEnvironment)
              (inp.piece.eval env.place env.env.toEnvironment) w).1 := by
        rcases Nat.eq_zero_or_pos w with rfl | hwpos
        · simpa only [accAfter, Nat.add_zero] using hxA0cell
        · have h := (hRows (w - 1) (by omega)).2.2.2.2.2
          rw [show w - 1 + 1 = w from by omega] at h
          exact h
      -- expose raw env spellings
      simp only [adv, Nat.add_zero] at hxA0cell hXcurw hVxp0 hVl10 hVl20 hVxpw hVl1w hVl2w hVxaw
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- first-row `Y_A` = 2·y_enter (`completeness_aux` at word 0)
        rw [hOfirst]
        simp only [dRow, adv, Nat.add_zero, yA, xR]
        rw [hVl10, hVl20, hxA0cell, hVxp0]
        rw [hA'y']
        simpa only [accAfter] using hYAinv0
      · -- exit `x_a` = B.x (`accAfter_eq_chain` through `completeness_aux`)
        rw [hOxANext]
        simp only [adv]
        rw [hVxaw, hAccB]
      · -- the last step's secant against the exit `x_a` (`rowValue` algebra)
        rw [hOxANext]
        simp only [xR, ← hOl_xA, ← hOl_xP, ← hOl_l1, ← hOl_l2, adv]
        rw [hVl2w, hVl1w, hXcurw, hVxpw, hVxaw]
        simp only [rowValue, accAfter]
        ring
      · -- the `nextYA` derivation lands on `2·B.y` (the `yANext` identity + `Y_A` invariant)
        rw [hOxANext]
        simp only [yA, xR, ← hOl_xA, ← hOl_xP, ← hOl_l1, ← hOl_l2, adv]
        rw [hVl2w, hVl1w, hXcurw, hVxpw, hVxaw]
        set P := inp.piece.eval env.place env.env.toEnvironment
        set XA := inp.xA.eval env.place env.env.toEnvironment
        set YA := inp.yA.eval env.place env.env.toEnvironment
        have hyd : (rowValue (accAfter G (XA, YA) P w)
              ((G.S (pieceWord P w)).x, (G.S (pieceWord P w)).y)).2.1
              * ((accAfter G (XA, YA) P w).1 - (accAfter G (XA, YA) P (w + 1)).1)
            = (accAfter G (XA, YA) P (w + 1)).2 + (accAfter G (XA, YA) P w).2 := by
          conv_lhs => rw [show accAfter G (XA, YA) P (w + 1)
            = (rowValue (accAfter G (XA, YA) P w)
                ((G.S (pieceWord P w)).x, (G.S (pieceWord P w)).y)).2.2 from rfl]
          conv_rhs => rw [show accAfter G (XA, YA) P (w + 1)
            = (rowValue (accAfter G (XA, YA) P w)
                ((G.S (pieceWord P w)).x, (G.S (pieceWord P w)).y)).2.2 from rfl]
          simp only [rowValue]
          ring
        have hBy : (accAfter G (XA, YA) P (w + 1)).2 = B'.y := by rw [hAccB]
        linear_combination 2 * hyd - hYAinvw + 2 * hBy

end Halo2.Ironwood.Sinsemilla.HashPiece
