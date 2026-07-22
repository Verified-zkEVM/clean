import Mathlib.Algebra.Field.Basic
import Clean.Circuit.SimpGadget
import Clean.Circuit.Expression

/-!
# Halo2 variables, expressions and environments

Port of `Clean/Circuit/Expression.lean` to the halo2 layout model. Main Clean's
`Variable`/`Expression` play two roles that halo2 separates, so this file defines both
replacements:

- `Expression` — the configure-layer constraint language: gate polynomials over
  variables. It is main Clean's `Expression` with the same four nodes, generalized over
  the variable type `L`. Circuit authors write gates in `Expression F Query`, where a
  `Query` is a selector or a (column, rotation) query, mirroring halo2's
  `meta.query_advice` etc. For VK comparison, gates are later projected to bare
  query-index variables (matching ironwood's `Expr` after a semantics-preserving erasure
  of its `Negated`/`Scaled` nodes); at consolidation time, main Clean's `Expression F`
  becomes the `L := Variable F` instance.
- `Cell` / `AssignedCell` — the synthesize-layer composition currency: region-relative
  cell references, as returned by `assignAdvice` and passed between gadgets.

`Environment` generalizes main Clean's `get : ℕ → F` to cell locations: columns at
(integer) rows. `ProverHint` is shared with main Clean, not copied.

Rust references (halo2 `halo2_gadgets-0.5.0`):
- `halo2_proofs/src/plonk/circuit.rs` — `Column`, `Any`, `Selector`, `TableColumn`,
  `FixedQuery`/`AdviceQuery`/`InstanceQuery`, `Expression` and its operator impls
- `halo2_proofs/src/circuit.rs` — `RegionIndex`, `Cell`, `AssignedCell`
- `halo2_proofs/src/poly.rs` — `Rotation`
-/

namespace Halo2

variable {F : Type} {L : Type}

/-- Kind of a column. Rust: `pub enum Any { Advice, Fixed, Instance }`.

Note: the Rust `Ord` instance (Instance < Advice < Fixed) is consensus-critical for the
layouters; a matching order function comes with the floor-planner port. -/
inductive ColumnKind where
  | advice
  | fixed
  | instance
deriving DecidableEq, Repr

/-- A column with an index, of a statically known kind.
Rust: `pub struct Column<C: ColumnType> { index, column_type }`. -/
structure Column (kind : ColumnKind) where
  index : ℕ
deriving DecidableEq, Repr

/-- A column of any kind. Rust: `Column<Any>`. -/
structure AnyColumn where
  kind : ColumnKind
  index : ℕ
deriving DecidableEq, Repr

/-- Forget a column's statically known kind. Rust: `impl From<Column<Advice>> for Column<Any>` etc.

Deliberately NOT `@[circuit_norm]`: `col.toAny` stays folded in proof states (no
`{ kind := …, index := … }` record literals); reads through it normalize to the typed
`Environment` accessors (`env.advice`/`env.fixed`/`env.inst`) via the `get_advice`-family
bridge lemmas below. -/
def Column.toAny {kind : ColumnKind} (c : Column kind) : AnyColumn := ⟨kind, c.index⟩

instance {kind : ColumnKind} : CoeOut (Column kind) AnyColumn := ⟨Column.toAny⟩

/-- A selector, used to enable a custom gate on specific rows.
Rust: `pub struct Selector(pub(crate) usize, bool)`; the `Bool` is "simple". -/
structure Selector where
  index : ℕ
  simple : Bool
deriving DecidableEq, Repr

/-- A relative row offset within a gate. Rust: `pub struct Rotation(pub i32)`. -/
abbrev Rotation := ℤ

/-- A fixed column of a lookup table. Rust: `pub struct TableColumn { inner: Column<Fixed> }`. -/
structure TableColumn where
  inner : Column .fixed
deriving DecidableEq, Repr

/-- Index of a region in a layouter. Rust: `pub struct RegionIndex(usize)`. -/
abbrev RegionIndex := ℕ

/-- A gate-expression variable: a selector or a column query at a relative row offset.
These are the atoms returned by `querySelector`/`queryFixed`/`queryAdvice`/
`queryInstance` in gate definitions (the `Selector`/`Fixed`/`Advice`/`Instance` atom
cases of Rust's `Expression<F>`).

Unlike Rust's query structs, atoms carry no query index: query indices are positions in
the constraint system's per-kind query lists, assigned by a deterministic
first-encounter walk over the finished constraint system at VK-compilation time
(mirroring Rust's `query_advice_index` registration) — not during gate authoring. This
makes gate bodies pure expression construction. -/
inductive Query where
  | selector : Selector → Query
  | fixed : Column .fixed → Rotation → Query
  | advice : Column .advice → Rotation → Query
  | instance : Column .instance → Rotation → Query
deriving DecidableEq, Repr

/-- Main Clean's `Expression`, generalized over the variable type `L`.

Halo2 uses `Expression F Query` at the circuit-writing layer. Rust's
`Negated`/`Sum`/`Product`/`Scaled` nodes correspond to `mul (const (-1)) ·` / `add` /
`mul` / `mul · (const c)`; the correspondence is a semantics-preserving erasure applied
to dumped constraint systems at the VK-comparison boundary. -/
inductive Expression (F : Type) (L : Type) where
  | var : L → Expression F L
  | const : F → Expression F L
  | add : Expression F L → Expression F L → Expression F L
  | mul : Expression F L → Expression F L → Expression F L
deriving DecidableEq

export Expression (var)

/--
`Environment` represents the data that is provided at runtime to concretely specify the
witness assignment of a circuit, and any additional witness data external to the current
circuit (`data`).

This is the halo2 counterpart of main Clean's `Environment`: `get` reads a cell by
column and (absolute, integer) row instead of by tape index.

The environment contains cell values and nothing else. In particular:

- No region placement: placement is circuit data — the floor planner computes it from
  the operations. Semantics take a `place : RegionIndex → ℕ` parameter, the analogue of
  main Clean's `offset`: proofs are generic over it, and the top-level statement
  instantiates the actual placement.
- No selector values: selector activation patterns are circuit data too — enabling a
  selector is an operation whose semantics instantiates the gate's constraints at that
  row.
- No analogue of main Clean's `data`: halo2 lookup tables are fixed columns, already
  covered by `get`.

Soundness theorems have the form `∀ env : Environment F, ...`.
-/
structure Environment (F : Type) where
  /-- Assignment of all cells: column, absolute row ↦ field element. -/
  get : AnyColumn → ℤ → F
  /-- Layout data: the domain's usable-row bound (`n − (blinding_factors + 1)`, the rows
  a lookup argument ranges over — `lookup/prover.rs:573-574`). A field, not a threaded
  semantics parameter (maintainer-adjudicated: zero signature churn, `ProverEnvironment`
  inherits it). Used only by `loadTable`'s default-fill semantics and the future VK
  bridge; it never appears in region-relative gadget statements. See `lookup-design.md`
  §2.4/§D6. -/
  usableRows : ℕ

/--
`ProverEnvironment` is `Environment` plus the prover's runtime `ProverHint`.
Completeness theorems are formulated against the `ProverEnvironment`.
-/
structure ProverEnvironment (F : Type) extends Environment F where
  /-- Runtime-only hashmap of prover hints, never committed into the proof. -/
  hint : ProverHint F

instance : Coe (ProverEnvironment F) (Environment F) := ⟨ProverEnvironment.toEnvironment⟩
instance : CoeOut (ProverEnvironment F) (Environment F) := ⟨ProverEnvironment.toEnvironment⟩

instance {α} : Coe (Environment F → α) (ProverEnvironment F → α) := ⟨fun f env => f env⟩
instance {α} : CoeOut (Environment F → α) (ProverEnvironment F → α) := ⟨fun f env => f env⟩

/-! ## Typed environment reads — the terminal normal form

`Environment.get` is kind-agnostic (`AnyColumn`), so every typed read goes through the
`Column.toAny` coercion; unfolded, that used to leave `{ kind := …, index := … }` record
literals all over proof states. The named accessors below are the single terminal normal
form for typed reads: the `get_advice`-family `circuit_norm` bridges rewrite
`env.get col.toAny row` to them, so gate-query atoms (`Query.eval`), assigned-cell evals
and witness reads all meet on the same `env.advice col row` spelling. Reads of cells with
a statically *unknown* column kind (foreign cells in copy constraints) stay on `env.get`
with a projected column — also record-free. -/

/-- Read an advice cell: column + absolute integer row. -/
def Environment.advice (env : Environment F) (col : Column .advice) (row : ℤ) : F :=
  env.get col.toAny row

/-- Read a fixed cell. -/
def Environment.fixed (env : Environment F) (col : Column .fixed) (row : ℤ) : F :=
  env.get col.toAny row

/-- Read an instance cell (a public input). Named `inst` because `instance` is a
reserved word. -/
def Environment.inst (env : Environment F) (col : Column .instance) (row : ℤ) : F :=
  env.get col.toAny row

@[circuit_norm]
lemma Environment.get_advice (env : Environment F) (col : Column .advice) (row : ℤ) :
    env.get col.toAny row = env.advice col row := rfl

@[circuit_norm]
lemma Environment.get_fixed (env : Environment F) (col : Column .fixed) (row : ℤ) :
    env.get col.toAny row = env.fixed col row := rfl

@[circuit_norm]
lemma Environment.get_inst (env : Environment F) (col : Column .instance) (row : ℤ) :
    env.get col.toAny row = env.inst col row := rfl

/-- Evaluate a query in an environment, at a `row`, given a valuation of the selectors:
column queries read their column at `row + rotation` (selector queries are not rotated —
halo2's `query_selector` takes no rotation).

The selector valuation is not part of the `Environment` because activation patterns are
circuit data: at gate-call sites it is `fun _ => 1` (the gate is enabled at this row);
at the VK bridge it is the activation table computed from the layout. -/
@[circuit_norm]
def Query.eval [Field F] (env : Environment F) (selectors : ℕ → F) (row : ℤ) : Query → F
  | .selector s => selectors s.index
  | .fixed col rot => env.fixed col (row + rot)
  | .advice col rot => env.advice col (row + rot)
  | .instance col rot => env.inst col (row + rot)

namespace Expression
variable [Field F]

/--
Evaluate an expression given a valuation of its variables.

Gate expressions are evaluated as `e.eval (Query.eval env selectors row)`, for an
external `Environment` that determines the assignment of all cells; this is needed when
we want to make statements about a circuit in the adversarial situation where the prover
can assign anything to cells.
-/
@[circuit_norm]
def eval (v : L → F) : Expression F L → F
  | var q => v q
  | const c => c
  | add x y => eval v x + eval v y
  | mul x y => eval v x * eval v y

/-- Rename/project the variables of an expression. Eval-compatibility is
`eval_mapVar` below. Used to project circuit-writing gates (`L := Query`) to the
VK-comparison form over bare query indices. -/
@[circuit_norm]
def mapVar {L' : Type} (f : L → L') : Expression F L → Expression F L'
  | var q => var (f q)
  | const c => const c
  | add x y => add (mapVar f x) (mapVar f y)
  | mul x y => mul (mapVar f x) (mapVar f y)

def toString [Repr F] [Repr L] : Expression F L → String
  | var q => reprStr q
  | const c => reprStr c
  | add x y => "(" ++ toString x ++ " + " ++ toString y ++ ")"
  | mul x y => "(" ++ toString x ++ " * " ++ toString y ++ ")"

instance [Repr F] [Repr L] : Repr (Expression F L) where
  reprPrec e _ := toString e

-- combine expressions elegantly (verbatim from main Clean)
instance : Zero (Expression F L) where zero := const 0
instance : One (Expression F L) where one := const 1
instance : Add (Expression F L) where add := add
instance : Neg (Expression F L) where neg e := mul (const (-1)) e
instance : Sub (Expression F L) where sub e₁ e₂ := add e₁ (-e₂)
instance : Mul (Expression F L) where mul := mul

/-- Rust `e * Expression::Constant(c)` — a genuine right-constant `Product` node (NOT
`Scaled`, which is Rust's `e * (c : F)` and is spelled `e * (c : F)` here). The marker
shape `e * (const c * const 1)` erases to `.product e (.constant c)` in the VK-matching
projection (`Fixtures/Project.lean`); semantically it is just `e * c` (`mul_one` folds
the marker in proofs). First needed by `base_field_elem`'s `alpha_0_hi_120`. -/
def mulConstant (e : Expression F L) (c : F) : Expression F L :=
  mul e (mul (const c) (const 1))

@[circuit_norm]
theorem eval_mulConstant (v : L → F) (e : Expression F L) (c : F) :
    (e.mulConstant c).eval v = e.eval v * c := by
  simp [mulConstant, eval]

instance : Coe F (Expression F L) where coe f := const f
instance {n : ℕ} [OfNat F n] : OfNat (Expression F L) n where
  ofNat := const (OfNat.ofNat n)

instance : HMul F (Expression F L) (Expression F L) where hMul f e := mul (const f) e
instance : HMul (Expression F L) F (Expression F L) where hMul e f := mul e (const f)

instance : HDiv (Expression F L) F (Expression F L) where hDiv e f := mul (const (f⁻¹ : F)) e
instance : HDiv (Expression F L) ℕ (Expression F L) where hDiv e f := mul (const ((f : F)⁻¹)) e

end Expression

instance [Field F] : Inhabited (Expression F L) where
  default := .const 0

/--
A pointer to a cell within a circuit, relative to the start of its region.
Rust: `pub struct Cell { region_index, row_offset, column }`.
-/
structure Cell where
  /-- Identifies the region in which this cell resides. -/
  regionIndex : RegionIndex
  /-- The relative offset of this cell within its region. -/
  rowOffset : ℕ
  /-- The column of this cell. -/
  column : AnyColumn
deriving DecidableEq, Repr

/--
An assigned cell: the synthesize-layer variable, and the composition currency between
gadgets (halo2's `AssignedCell<V, F>`). This replaces main Clean's `Variable`; unlike
the Rust original it carries no value — values are determined by the `Environment`.
-/
structure AssignedCell (F : Type) where
  cell : Cell
deriving DecidableEq, Repr

/-! ### Named cell constructors

The `varFromOffset` analogue at halo2's per-cell granularity: cells the circuit itself
creates (assign/copy operations) are spelled `Cell.of self row col` instead of an
anonymous record literal, keeping the typed column folded. NOT unfolded by
`circuit_norm` — the projection lemmas below expose exactly what the semantics need, and
evals land on the typed `Environment` accessors via the `get_advice`-family bridges. -/

/-- The cell at region `self`, region-local row `row`, column `col`. -/
def Cell.of (self : RegionIndex) (row : ℕ) {kind : ColumnKind} (col : Column kind) : Cell :=
  ⟨self, row, col.toAny⟩

/-- The assigned cell at region `self`, region-local row `row`, column `col` — what the
assign/copy operations return. -/
def AssignedCell.of (self : RegionIndex) (row : ℕ) {kind : ColumnKind} (col : Column kind) :
    AssignedCell F :=
  ⟨.of self row col⟩

@[circuit_norm]
lemma Cell.of_regionIndex (self : RegionIndex) (row : ℕ) {kind : ColumnKind} (col : Column kind) :
    (Cell.of self row col).regionIndex = self := rfl

@[circuit_norm]
lemma Cell.of_rowOffset (self : RegionIndex) (row : ℕ) {kind : ColumnKind} (col : Column kind) :
    (Cell.of self row col).rowOffset = row := rfl

@[circuit_norm]
lemma Cell.of_column (self : RegionIndex) (row : ℕ) {kind : ColumnKind} (col : Column kind) :
    (Cell.of self row col).column = col.toAny := rfl

@[circuit_norm]
lemma AssignedCell.of_cell (self : RegionIndex) (row : ℕ) {kind : ColumnKind} (col : Column kind) :
    (AssignedCell.of self row col : AssignedCell F).cell = Cell.of self row col := rfl

-- TODO HALO2 this seems extremely questionable. eval-normal form of an arbitrary cell doesn't match
-- the one of a concrete cell. see Mul.lean, `incomplete_call_output` necessity
/-- Evaluate an assigned cell: read its column at the region's placement plus the
cell's offset. `place` is the region-placement parameter of the semantics (the analogue
of main Clean's `offset`) — proofs are generic over it; the top level instantiates the
floor planner's output.

NOT `@[circuit_norm]` (normal-form unification, maintainer ruling): an ABSTRACT cell's
read stays folded as the `AssignedCell.eval place env c` atom — unfolding it produced
raw `env.get c.cell.column …` spellings that competed with the typed `env.advice` form
and got pinned into signatures. Known-kind cells reduce directly to the typed accessors
via the `eval_of_*` rules below; `env.get` never appears in the user-facing normal
form. -/
def AssignedCell.eval [Field F] (place : RegionIndex → ℕ) (env : Environment F)
    (c : AssignedCell F) : F :=
  -- cast the ℕ row sum as a whole (not `↑a + ↑b`), so cell reads share the row form
  -- `↑(place self + rowOffset)` with the query/witness paths (avoids cast-shape mismatch).
  env.get c.cell.column ((place c.cell.regionIndex + c.cell.rowOffset : ℕ) : ℤ)

/-- A concrete advice cell's read is the typed advice accessor — the single
user-facing spelling for known-kind cell reads. -/
@[circuit_norm]
lemma AssignedCell.eval_of_advice [Field F] (place : RegionIndex → ℕ)
    (env : Environment F) (self : RegionIndex) (row : ℕ) (col : Column .advice) :
    AssignedCell.eval place env (.of self row col)
      = env.advice col ((place self + row : ℕ) : ℤ) := rfl

@[circuit_norm]
lemma AssignedCell.eval_of_fixed [Field F] (place : RegionIndex → ℕ)
    (env : Environment F) (self : RegionIndex) (row : ℕ) (col : Column .fixed) :
    AssignedCell.eval place env (.of self row col)
      = env.fixed col ((place self + row : ℕ) : ℤ) := rfl

@[circuit_norm]
lemma AssignedCell.eval_of_inst [Field F] (place : RegionIndex → ℕ)
    (env : Environment F) (self : RegionIndex) (row : ℕ) (col : Column .instance) :
    AssignedCell.eval place env (.of self row col)
      = env.inst col ((place self + row : ℕ) : ℤ) := rfl

/-! ## Lemmas about Expression evaluation -/

section EvalLemmas
variable [Field F] (v : L → F)

/-- Expression.eval distributes over multiplication -/
@[circuit_norm]
lemma eval_mul (a b : Expression F L) :
    Expression.eval v (Expression.mul a b) = Expression.eval v a * Expression.eval v b := by
  simp only [Expression.eval]

/-- Expression.eval distributes over addition -/
@[circuit_norm]
lemma eval_add (a b : Expression F L) :
    Expression.eval v (Expression.add a b) = Expression.eval v a + Expression.eval v b := by
  simp only [Expression.eval]

/-- Variable renaming composes with evaluation. -/
@[circuit_norm]
lemma eval_mapVar {L' : Type} (f : L → L') (v' : L' → F) (e : Expression F L) :
    Expression.eval v' (e.mapVar f) = Expression.eval (v' ∘ f) e := by
  induction e with
  | var q => rfl
  | const c => rfl
  | add x y ihx ihy => simp only [Expression.mapVar, Expression.eval, ihx, ihy]
  | mul x y ihx ihy => simp only [Expression.mapVar, Expression.eval, ihx, ihy]

end EvalLemmas

end Halo2
