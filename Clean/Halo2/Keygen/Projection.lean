import Clean.Halo2.Keygen.RichExpression
import Clean.Halo2.Keygen.CompressSelectors

/-!
# The query-index walk: `ConstraintSystem` → pinned gate AST

Projects a Halo2-Clean `ConstraintSystem F` (the output of running a chip's `configure`)
into the pinned/verifier record shape, erasing `Halo2.Expression F Query` into the
query-index `RichExpression F`.

Two pieces:

* **The query-index walk** (halo2 `circuit.rs` `query_{advice,fixed,instance}_index`):
  halo2 assigns each *new* `(column, rotation)` the next query index, in the order the
  query is first *called* inside a gate/lookup closure. That order is recorded in the
  `ConstraintSystem` at configure time (`{advice,fixed,instance}Queries`, see
  `query-registration-design.md`); the walk starts from those layouts and rewrites each
  `Query` atom to its index.

* **The operator erasure** (`Clean/Halo2/Expression.lean`): Halo2-Clean's four-node
  `Expression` (`var/const/add/mul`) is lowered to the pinned `RichExpression` matching how
  Rust's `std::ops` build `Expression<F>`: `Neg`/`Sub` produce `mul (const (-1)) e ↦
  .negated e`, `add ↦ .sum`, `mul ↦ .product`, `const ↦ .constant`, and `var ↦
  .advice/.fixed/.instance/.selector`. `.scaled` — Rust `expr * field` (`impl Mul<F>`) — is
  the `mul e (const c)` case, constant on the RIGHT, spelled in ports as `e * (c : F)`.

The map-driven `projectCS` targets the deployed VK's shape (after `compress_selectors`):
selectors are substituted by their packed-fixed-column replacements *before* the walk
(`substSelectorMap`), so no selector atom survives to the erasure. A stray selector atom
erases to `.selector`; `Clean.Halo2.Keygen.Semantics` supplies the selector-freeness that
makes the case unreachable post-compression.
-/

namespace Halo2

/-! ## The projected record shapes -/

/-- One projected lookup argument: both sides are index-based `RichExpression`s (the table
side is a rotation-0 fixed query on the table column). -/
structure LookupFixture (F : Type) where
  inputs : List (RichExpression F)
  tables : List (RichExpression F)
deriving DecidableEq, Repr

/-- The constraint-system data a Halo2-Clean projection reproduces (the pinned/verifier
CS-field shape), specialised to a single circuit's dump. Query layouts are `(column,
rotation)` lists; `gates` is the flat index-based polynomial list; `lookups` is the
per-lookup input/table expression lists in registration order. -/
structure CsFixture (F : Type) where
  numAdviceColumns : ℕ
  numFixedColumns : ℕ
  numInstanceColumns : ℕ
  numSelectors : ℕ
  adviceQueryLayout : List (ℕ × ℤ)
  fixedQueryLayout : List (ℕ × ℤ)
  instanceQueryLayout : List (ℕ × ℤ)
  gates : List (RichExpression F)
  lookups : List (LookupFixture F) := []
deriving DecidableEq, Repr

variable {F : Type}

/-- The mutable state of the query walk: the three query layouts accumulated so far, in
first-encounter order. -/
structure QueryState where
  advice : Array (ℕ × ℤ) := #[]
  fixed : Array (ℕ × ℤ) := #[]
  inst : Array (ℕ × ℤ) := #[]

/-- Return the index of `(col, rot)` in `arr`, or `none`. -/
def findQuery (arr : Array (ℕ × ℤ)) (col : ℕ) (rot : ℤ) : Option ℕ :=
  (arr.findIdx? (fun p => p.1 = col ∧ p.2 = rot))

/-- Register `(col, rot)` in the advice layout, returning its index (existing or new). -/
def QueryState.advIdx (s : QueryState) (col : ℕ) (rot : ℤ) : ℕ × QueryState :=
  match findQuery s.advice col rot with
  | some i => (i, s)
  | none => (s.advice.size, { s with advice := s.advice.push (col, rot) })

def QueryState.fixIdx (s : QueryState) (col : ℕ) (rot : ℤ) : ℕ × QueryState :=
  match findQuery s.fixed col rot with
  | some i => (i, s)
  | none => (s.fixed.size, { s with fixed := s.fixed.push (col, rot) })

def QueryState.instIdx (s : QueryState) (col : ℕ) (rot : ℤ) : ℕ × QueryState :=
  match findQuery s.inst col rot with
  | some i => (i, s)
  | none => (s.inst.size, { s with inst := s.inst.push (col, rot) })

section Erase
variable [Field F] [DecidableEq F]

/-- Erase one `Expression F Query` into a `RichExpression F`, threading the query-walk
state. Traversal order (left operand before right, atom on encounter) is what determines the
query indices, so it must match the order the Rust gate closure *builds* its expression.
The Rust `std::ops` build left-to-right (`a - b` builds `a`, then `b`, then combines), so a
plain left-to-right structural traversal reproduces it.

A `Query.selector` atom erases to `.selector`; post-compression it is substituted away
before the walk (`substSelectorMap`), so it survives only in the pre-compression view. -/
def eraseExpr : Expression F Query → QueryState → RichExpression F × QueryState
  | .const c, s => (.constant c, s)
  | .var (.selector sel), s => (.selector sel.index, s)
  | .var (.advice col rot), s =>
      let (i, s) := s.advIdx col.index rot
      (.advice i, s)
  | .var (.fixed col rot), s =>
      let (i, s) := s.fixIdx col.index rot
      (.fixed i, s)
  | .var (.instance col rot), s =>
      let (i, s) := s.instIdx col.index rot
      (.instance i, s)
  -- Neg/Sub lower to `mul (const (-1)) e`; recognise it as `.negated`. A left constant
  -- otherwise is a genuine `Expression::Constant * e` product (const-on-left is how the
  -- ports spell Rust `Constant(c) * e`).
  | .mul (.const c) e, s =>
      if c = (-1 : F) then
        let (e', s) := eraseExpr e s
        (.negated e', s)
      else
        let (e', s) := eraseExpr e s
        (.product (.constant c) e', s)
  -- A RIGHT constant is Rust's `Expression * F` (`impl Mul<F>`), which builds
  -- `Expression::Scaled(e, c)`. The `mulConstant` marker (`Expression.lean`): Rust's
  -- right-constant `Product` (`e * Expression::Constant(c)`), spelled `e * (const c * const 1)`.
  | .mul e (.mul (.const c) (.const one)), s =>
      if one = (1 : F) then
        let (e', s) := eraseExpr e s
        (.product e' (.constant c), s)
      else
        let (e', s) := eraseExpr e s
        let (i', s) := eraseExpr (.mul (.const c) (.const one)) s
        (.product e' i', s)
  | .mul e (.const c), s =>
      let (e', s) := eraseExpr e s
      (.scaled e' c, s)
  | .add a b, s =>
      let (a', s) := eraseExpr a s
      let (b', s) := eraseExpr b s
      (.sum a' b', s)
  | .mul a b, s =>
      let (a', s) := eraseExpr a s
      let (b', s) := eraseExpr b s
      (.product a' b', s)

/-- Erase a list of gate polynomials in order, threading the query walk. -/
def eraseGates : List (Expression F Query) → QueryState → List (RichExpression F) × QueryState
  | [], s => ([], s)
  | p :: ps, s =>
      let (e, s) := eraseExpr p s
      let (es, s) := eraseGates ps s
      (e :: es, s)

/-- Erase a whole `LookupArgument` (its input and table expression lists), threading the
query walk. Mirrors `eraseGates` but returns a `LookupFixture`. -/
def eraseLookup (arg : LookupArgument F) (s : QueryState) :
    LookupFixture F × QueryState :=
  let (inputs, s) := eraseGates arg.inputs s
  let (tables, s) := eraseGates arg.tables s
  ({ inputs, tables }, s)

/-- Erase a list of lookups in registration order, threading the walk. -/
def eraseLookups : List (LookupArgument F) → QueryState → List (LookupFixture F) × QueryState
  | [], s => ([], s)
  | a :: as, s =>
      let (l, s) := eraseLookup a s
      let (ls, s) := eraseLookups as s
      (l :: ls, s)

end Erase

/-! ### The configure-recorded query layouts (halo2 `queried_cells`)

halo2 assigns query indices in the order `query_advice`/`query_fixed`/`query_instance` are
*called* inside each gate/lookup closure — i.e. the order the queries are *declared*, not the
order they appear in the finished polynomial AST. Clean's configure-time query registration
records that order in `cs.{advice,fixed,instance}Queries`; the walk starts from those recorded
layouts, so the erasure DFS finds every query already registered and reuses its index. -/

/-- The query-walk state pre-loaded with the CS's configure-recorded query layouts. -/
def recordedQueries (cs : ConstraintSystem F) : QueryState where
  advice := (cs.adviceQueries.map fun (c, r) => (c.index, r)).toArray
  fixed := (cs.fixedQueries.map fun (c, r) => (c.index, r)).toArray
  inst := (cs.instanceQueries.map fun (c, r) => (c.index, r)).toArray

/-- The post-compression walk start: the configure-recorded layouts plus the packed
selector columns' rot-0 fixed queries, appended in packing order — halo2 registers them
at column-allocation time inside `compress_selectors` (`circuit.rs:1267-1274`, via
`query_fixed_index` in the allocate closure), BEFORE the substituted gates are walked. -/
def queryWalkInit (map : SelCompressMap) (cs : ConstraintSystem F) : QueryState :=
  (List.range map.newFixedCols).foldl
    (fun s i => (s.fixIdx (cs.numFixedColumns + i) 0).2) (recordedQueries cs)

/-- Project the CS with a selector-compression map: substitute every selector (in gates and
lookups) by its root-finding replacement, grow `numFixedColumns` by the new packed columns,
and run the seeded query walk.

Halo2's query order after compression: `queryWalkInit` — the configure-recorded layouts
plus the packed columns' fixed queries in packing order. `numSelectors` is NOT reset by
compression (halo2 keeps the count; the pinned VK doesn't carry it). -/
def projectCS [Field F] [DecidableEq F] (map : SelCompressMap) (cs : ConstraintSystem F) :
    CsFixture F :=
  let m : ℕ → Option SelCompress := map.lookup
  let polys := (flatGates cs).map (substSelectorMap m)
  let lookups' : List (LookupArgument F) := cs.lookups.map (fun a =>
    { inputs := a.inputs.map (substSelectorMap m)
      tables := a.tables.map (substSelectorMap m) })
  -- plain projections (not `let (a, b) := …` matches), so record-field access reduces
  -- structurally without evaluating the walk
  let gs := eraseGates polys (queryWalkInit map cs)
  let lks := eraseLookups lookups' gs.2
  { numAdviceColumns := cs.numAdviceColumns
    numFixedColumns := cs.numFixedColumns + map.newFixedCols
    numInstanceColumns := cs.numInstanceColumns
    numSelectors := cs.numSelectors
    adviceQueryLayout := lks.2.advice.toList
    fixedQueryLayout := lks.2.fixed.toList
    instanceQueryLayout := lks.2.inst.toList
    gates := gs.1
    lookups := lks.1 }

end Halo2
