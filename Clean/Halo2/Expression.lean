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
  | «instance»
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

/-- Forget a column's statically known kind. Rust: `impl From<Column<Advice>> for Column<Any>` etc. -/
@[circuit_norm]
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
  | «instance» : Column .instance → Rotation → Query
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

/-- Evaluate a query in an environment, at a `row`, given a valuation of the selectors:
column queries read their column at `row + rotation` (selector queries are not rotated —
halo2's `query_selector` takes no rotation).

The selector valuation is not part of the `Environment` because activation patterns are
circuit data: at gate-call sites it is `fun _ => 1` (the gate is enabled at this row);
at the VK bridge it is the activation table computed from the layout. -/
@[circuit_norm]
def Query.eval [Field F] (env : Environment F) (selectors : ℕ → F) (row : ℤ) : Query → F
  | .selector s => selectors s.index
  | .fixed c rot => env.get c.toAny (row + rot)
  | .advice c rot => env.get c.toAny (row + rot)
  | .«instance» c rot => env.get c.toAny (row + rot)

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

/-- Evaluate an assigned cell: read its column at the region's placement plus the
cell's offset. `place` is the region-placement parameter of the semantics (the analogue
of main Clean's `offset`) — proofs are generic over it; the top level instantiates the
floor planner's output. -/
@[circuit_norm]
def AssignedCell.eval [Field F] (place : RegionIndex → ℕ) (env : Environment F)
    (c : AssignedCell F) : F :=
  env.get c.cell.column (place c.cell.regionIndex + c.cell.rowOffset)

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
