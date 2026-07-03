import Mathlib.Algebra.Field.Basic
import Clean.Circuit.SimpGadget
import Clean.Circuit.Expression

/-!
# Halo2 variables, expressions and environments

Port of `Clean/Circuit/Expression.lean` to the halo2 layout model. Main Clean's
`Variable`/`Expression` play two roles that halo2 separates, so this file defines both
replacements:

- `Expression` — the configure-layer constraint language: gate polynomials over
  (column, rotation) queries and selectors. Matches halo2's `Expression` node set
  exactly, so that constraint systems dumped from Rust can match syntactically.
- `Cell` / `AssignedCell` — the synthesize-layer composition currency: region-relative
  cell references, as returned by `assignAdvice` and passed between gadgets.

`Environment` generalizes main Clean's `get : ℕ → F` to cell locations: columns at
(integer) rows, plus selector values and region placement. `ProverData`/`ProverHint`
are shared with main Clean, not copied.

Rust references (halo2 `halo2_gadgets-0.5.0`):
- `halo2_proofs/src/plonk/circuit.rs` — `Column`, `Any`, `Selector`, `TableColumn`,
  `FixedQuery`/`AdviceQuery`/`InstanceQuery`, `Expression` and its operator impls
- `halo2_proofs/src/circuit.rs` — `RegionIndex`, `Cell`, `AssignedCell`
- `halo2_proofs/src/poly.rs` — `Rotation`
-/

namespace Halo2

variable {F : Type}

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

/-!
Queries of columns at relative locations, as they appear inside gate expressions.
The `index` is the query's position in the constraint system's query list, assigned
during configure; it is bookkeeping needed for VK matching and ignored by `eval`.
-/

/-- Query of a fixed column at a relative location. Rust: `FixedQuery`. -/
structure FixedQuery where
  index : ℕ
  columnIndex : ℕ
  rotation : Rotation
deriving DecidableEq, Repr

/-- Query of an advice column at a relative location. Rust: `AdviceQuery`. -/
structure AdviceQuery where
  index : ℕ
  columnIndex : ℕ
  rotation : Rotation
deriving DecidableEq, Repr

/-- Query of an instance column at a relative location. Rust: `InstanceQuery`. -/
structure InstanceQuery where
  index : ℕ
  columnIndex : ℕ
  rotation : Rotation
deriving DecidableEq, Repr

/-- Low-degree expression representing an identity that must hold over the committed
columns; the constraint language of custom gates.

Constructor set matches Rust `Expression<F>` exactly (this replaces main Clean's
`var/const/add/mul` node set, so dumped gate ASTs can be compared syntactically). -/
inductive Expression (F : Type) where
  | constant : F → Expression F
  | selector : Selector → Expression F
  | fixed : FixedQuery → Expression F
  | advice : AdviceQuery → Expression F
  | «instance» : InstanceQuery → Expression F
  | negated : Expression F → Expression F
  | sum : Expression F → Expression F → Expression F
  | product : Expression F → Expression F → Expression F
  | scaled : Expression F → F → Expression F
deriving DecidableEq

/--
`Environment` represents the data that is provided at runtime to concretely specify the
witness assignment of a circuit, and any additional witness data external to the current
circuit (`data`).

This is the halo2 counterpart of main Clean's `Environment`: `get` reads a cell by
column and (absolute, integer) row instead of by tape index. Selector values and region
placement are extra assignment dimensions with no main-Clean counterpart:

- `selector` gives each selector's virtual 0/1 value per row (selector compression into
  fixed columns happens at the data level, outside of proofs).
- `regionStart` places each region at an absolute row. Proofs quantify over arbitrary
  `Environment`s, so gadget soundness/completeness never depends on actual placement.

Soundness theorems have the form `∀ env : Environment F, ...`.
-/
structure Environment (F : Type) where
  /-- Assignment of all cells: column, absolute row ↦ field element. -/
  get : AnyColumn → ℤ → F
  /-- Virtual per-row selector values. -/
  selector : ℕ → ℤ → F
  /-- Absolute start row of each region. -/
  regionStart : RegionIndex → ℤ
  /-- Additional witness data not part of the current circuit's witness, such as the
   content of lookup tables. Shared with main Clean. -/
  data : ProverData F

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

namespace Expression
variable [Field F]

/--
Evaluate a gate expression at a `row`, given an external `environment` that determines
the assignment of all cells. Queries read their column at `row + rotation`; the query
index is CS bookkeeping and does not affect evaluation.

This is needed when we want to make statements about a circuit in the adversarial
situation where the prover can assign anything to cells.
-/
@[circuit_norm]
def eval (env : Environment F) (row : ℤ) : Expression F → F
  | constant c => c
  | selector s => env.selector s.index row
  | fixed q => env.get ⟨.fixed, q.columnIndex⟩ (row + q.rotation)
  | advice q => env.get ⟨.advice, q.columnIndex⟩ (row + q.rotation)
  | «instance» q => env.get ⟨.instance, q.columnIndex⟩ (row + q.rotation)
  | negated e => -eval env row e
  | sum x y => eval env row x + eval env row y
  | product x y => eval env row x * eval env row y
  | scaled e c => eval env row e * c

def toString [Repr F] : Expression F → String
  | constant c => reprStr c
  | selector s => "sel " ++ reprStr s.index
  | fixed q => s!"fixed[{q.columnIndex}]@{q.rotation}"
  | advice q => s!"advice[{q.columnIndex}]@{q.rotation}"
  | «instance» q => s!"instance[{q.columnIndex}]@{q.rotation}"
  | negated e => "(-" ++ toString e ++ ")"
  | sum x y => "(" ++ toString x ++ " + " ++ toString y ++ ")"
  | product x y => "(" ++ toString x ++ " * " ++ toString y ++ ")"
  | scaled e c => "(" ++ toString e ++ " * " ++ reprStr c ++ ")"

instance [Repr F] : Repr (Expression F) where
  reprPrec e _ := toString e

/- Operator instances produce exactly the AST nodes of the Rust operator impls
(`Neg → Negated`, `Add → Sum`, `Sub → Sum(a, Negated b)`, `Mul → Product`,
`Mul<F> → Scaled`), so gates ported verbatim build identical trees. The Rust
runtime panics on simple-selector misuse are not operator behavior; they become a
wellformedness predicate later. -/
instance : Zero (Expression F) where zero := constant 0
instance : One (Expression F) where one := constant 1
instance : Neg (Expression F) where neg := negated
instance : Add (Expression F) where add := sum
instance : Sub (Expression F) where sub x y := sum x (negated y)
instance : Mul (Expression F) where mul := product
instance : HMul (Expression F) F (Expression F) where hMul := scaled

instance : Coe F (Expression F) where coe f := constant f
instance {n : ℕ} [OfNat F n] : OfNat (Expression F) n where
  ofNat := constant (OfNat.ofNat n)

end Expression

instance [Field F] : Inhabited (Expression F) where
  default := .constant 0

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

/-- Evaluate an assigned cell in an environment: read its column at the region's
placement plus the cell's offset. -/
@[circuit_norm]
def AssignedCell.eval [Field F] (env : Environment F) (c : AssignedCell F) : F :=
  env.get c.cell.column (env.regionStart c.cell.regionIndex + c.cell.rowOffset)

/-! ## Lemmas about Expression evaluation -/

section EvalLemmas
variable [Field F]

@[circuit_norm]
lemma eval_sum (env : Environment F) (row : ℤ) (a b : Expression F) :
    Expression.eval env row (Expression.sum a b) =
      Expression.eval env row a + Expression.eval env row b := by
  simp only [Expression.eval]

@[circuit_norm]
lemma eval_product (env : Environment F) (row : ℤ) (a b : Expression F) :
    Expression.eval env row (Expression.product a b) =
      Expression.eval env row a * Expression.eval env row b := by
  simp only [Expression.eval]

@[circuit_norm]
lemma eval_negated (env : Environment F) (row : ℤ) (a : Expression F) :
    Expression.eval env row (Expression.negated a) = -Expression.eval env row a := by
  simp only [Expression.eval]

@[circuit_norm]
lemma eval_scaled (env : Environment F) (row : ℤ) (a : Expression F) (c : F) :
    Expression.eval env row (Expression.scaled a c) = Expression.eval env row a * c := by
  simp only [Expression.eval]

end EvalLemmas

end Halo2
