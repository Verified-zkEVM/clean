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

/-- The three authoritative query layouts. Expression projection only resolves indices
against these arrays; it never repairs a missing configure-time declaration. -/
structure QueryState where
  advice : Array (ℕ × ℤ) := #[]
  fixed : Array (ℕ × ℤ) := #[]
  inst : Array (ℕ × ℤ) := #[]

@[ext] theorem QueryState.ext
    {left right : QueryState}
    (advice : left.advice = right.advice)
    (fixed : left.fixed = right.fixed)
    (inst : left.inst = right.inst) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Return the index of `(col, rot)` in `arr`, or `none`. -/
def findQuery (arr : Array (ℕ × ℤ)) (col : ℕ) (rot : ℤ) : Option ℕ :=
  (arr.findIdx? (fun p => p.1 = col ∧ p.2 = rot))

/-- Resolve an advice query against the authoritative layout. The out-of-range fallback
is unreachable for query-lawful circuits and does not mutate the layout. -/
def QueryState.advIdx (s : QueryState) (col : ℕ) (rot : ℤ) : ℕ :=
  (findQuery s.advice col rot).getD s.advice.size

def QueryState.fixIdx (s : QueryState) (col : ℕ) (rot : ℤ) : ℕ :=
  (findQuery s.fixed col rot).getD s.fixed.size

def QueryState.instIdx (s : QueryState) (col : ℕ) (rot : ℤ) : ℕ :=
  (findQuery s.inst col rot).getD s.inst.size

/-- Register the fixed query created by selector compression. This is the sole layout
extension in the projection pipeline and corresponds to Halo2 allocating each packed
selector column and immediately querying it at rotation zero. -/
def QueryState.registerFixed (s : QueryState) (col : ℕ) : QueryState :=
  match findQuery s.fixed col 0 with
  | some _ => s
  | none => { s with fixed := s.fixed.push (col, 0) }

/-- Registering a fixed column above every existing fixed query appends its
rotation-zero query. -/
theorem QueryState.registerFixed_fixed_toList
    (queries : QueryState) (column : ℕ)
    (hqueries : queries.fixed.toList.Forall fun query => query.1 < column) :
    (queries.registerFixed column).fixed.toList =
      queries.fixed.toList ++ [(column, 0)] := by
  have hmissing : findQuery queries.fixed column 0 = none := by
    rw [findQuery, Array.findIdx?_eq_none_iff]
    intro query hquery
    have hbound := List.forall_iff_forall_mem.mp hqueries query (by
      simpa using hquery)
    simp only [decide_eq_false_iff_not]
    omega
  unfold QueryState.registerFixed
  rw [hmissing]
  simp

section Erase
variable [Field F] [DecidableEq F]

/-- Erase one `Expression F Query` into a `RichExpression F`, resolving every ordinary
query against the supplied layout. Query order was already fixed by configure, rather
than reconstructed from the finished AST.

A `Query.selector` atom erases to `.selector`; post-compression it is substituted away
before the walk (`substSelectorMap`), so it survives only in the pre-compression view. -/
def eraseExpr : Expression F Query → QueryState → RichExpression F
  | .const c, _ => .constant c
  | .var (.selector sel), _ => .selector sel.index
  | .var (.advice col rot), s =>
      .advice (s.advIdx col.index rot)
  | .var (.fixed col rot), s =>
      .fixed (s.fixIdx col.index rot)
  | .var (.instance col rot), s =>
      .instance (s.instIdx col.index rot)
  -- Neg/Sub lower to `mul (const (-1)) e`; recognise it as `.negated`. A left constant
  -- otherwise is a genuine `Expression::Constant * e` product (const-on-left is how the
  -- ports spell Rust `Constant(c) * e`).
  | .mul (.const c) e, s =>
      if c = (-1 : F) then
        .negated (eraseExpr e s)
      else
        .product (.constant c) (eraseExpr e s)
  -- A RIGHT constant is Rust's `Expression * F` (`impl Mul<F>`), which builds
  -- `Expression::Scaled(e, c)`. The `mulConstant` marker (`Expression.lean`): Rust's
  -- right-constant `Product` (`e * Expression::Constant(c)`), spelled `e * (const c * const 1)`.
  | .mul e (.mul (.const c) (.const one)), s =>
      if one = (1 : F) then
        .product (eraseExpr e s) (.constant c)
      else
        .product (eraseExpr e s)
          (eraseExpr (.mul (.const c) (.const one)) s)
  | .mul e (.const c), s =>
      .scaled (eraseExpr e s) c
  | .add a b, s =>
      .sum (eraseExpr a s) (eraseExpr b s)
  | .mul a b, s =>
      .product (eraseExpr a s) (eraseExpr b s)

/-- Erase a list of gate polynomials in order, threading the query walk. -/
def eraseGates (expressions : List (Expression F Query))
    (queries : QueryState) : List (RichExpression F) :=
  expressions.map (eraseExpr · queries)

/-- Erase a whole `LookupArgument` (its input and table expression lists), threading the
query walk. Mirrors `eraseGates` but returns a `LookupFixture`. -/
def eraseLookup (arg : LookupArgument F) (queries : QueryState) :
    LookupFixture F :=
  { inputs := eraseGates arg.inputs queries
    tables := eraseGates arg.tables queries }

/-- Erase a list of lookups in registration order, threading the walk. -/
def eraseLookups (arguments : List (LookupArgument F))
    (queries : QueryState) : List (LookupFixture F) :=
  arguments.map (eraseLookup · queries)

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
    (fun s i => s.registerFixed (cs.numFixedColumns + i)) (recordedQueries cs)

/-- The fixed-query layout after selector compression is the recorded configure
layout followed by one fresh rotation-zero query for every packed selector column. -/
theorem queryWalkInit_fixed_toList
    (map : SelCompressMap) (cs : ConstraintSystem F)
    (hrecorded : cs.fixedQueries.Forall fun query =>
      query.1.index < cs.numFixedColumns) :
    (queryWalkInit map cs).fixed.toList =
      (cs.fixedQueries.map fun query => (query.1.index, query.2)) ++
        (List.range map.newFixedCols).map fun index =>
          (cs.numFixedColumns + index, 0) := by
  have hinitial : (recordedQueries cs).fixed.toList =
      cs.fixedQueries.map fun query => (query.1.index, query.2) := by
    simp [recordedQueries]
  have hinitialBound :
      (recordedQueries cs).fixed.toList.Forall fun query =>
        query.1 < cs.numFixedColumns := by
    rw [hinitial, List.forall_map_iff]
    exact hrecorded
  have aux (count : ℕ) :
      ((List.range count).foldl
        (fun state index =>
          state.registerFixed (cs.numFixedColumns + index))
        (recordedQueries cs)).fixed.toList =
          (recordedQueries cs).fixed.toList ++
            (List.range count).map fun index =>
              (cs.numFixedColumns + index, 0) := by
    induction count with
    | zero => simp
    | succ count inductionHypothesis =>
        rw [List.range_succ, List.foldl_append]
        let current := (List.range count).foldl
          (fun state index =>
            state.registerFixed (cs.numFixedColumns + index))
          (recordedQueries cs)
        change (current.registerFixed
            (cs.numFixedColumns + count)).fixed.toList = _
        rw [QueryState.registerFixed_fixed_toList]
        · rw [inductionHypothesis]
          simp only [List.map_append, List.map_cons, List.map_nil,
            List.append_assoc]
        · rw [inductionHypothesis]
          apply List.forall_append.mpr
          constructor
          · exact hinitialBound.imp fun query hquery =>
              hquery.trans_le (Nat.le_add_right _ _)
          · rw [List.forall_map_iff, List.forall_iff_forall_mem]
            intro index hindex
            exact Nat.add_lt_add_left (List.mem_range.mp hindex) _
  unfold queryWalkInit
  rw [aux, hinitial]

/-- Selector compression adds exactly one fixed-query slot per packed selector
column. -/
theorem queryWalkInit_fixed_length
    (map : SelCompressMap) (cs : ConstraintSystem F)
    (hrecorded : cs.fixedQueries.Forall fun query =>
      query.1.index < cs.numFixedColumns) :
    (queryWalkInit map cs).fixed.toList.length =
      cs.fixedQueries.length + map.newFixedCols := by
  rw [queryWalkInit_fixed_toList map cs hrecorded, List.length_append,
    List.length_map, List.length_map, List.length_range]

/-- Selector substitution is inert on selector-free expressions. -/
theorem substSelectorMap_eq_of_selectorFree
    [Field F]
    (map : ℕ → Option SelCompress) (expression : Expression F Query)
    (hfree : expression.SelectorFree) :
    substSelectorMap map expression = expression := by
  induction expression with
  | var query =>
      cases query with
      | selector selector =>
          simp [Expression.SelectorFree] at hfree
      | fixed | advice | «instance» =>
          rfl
  | const =>
      rfl
  | add left right ihLeft ihRight =>
      simp only [Expression.SelectorFree] at hfree
      simp only [substSelectorMap]
      rw [ihLeft hfree.1, ihRight hfree.2]
  | mul left right ihLeft ihRight =>
      simp only [Expression.SelectorFree] at hfree
      simp only [substSelectorMap]
      rw [ihLeft hfree.1, ihRight hfree.2]

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
    { masterSelector := a.masterSelector
      inputs := a.inputs.map (substSelectorMap m)
      tables := a.tables.map (substSelectorMap m)
      inputsNoSimpleSelectors := by
        rw [List.forall_iff_forall_mem]
        intro expression hexpression
        obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hexpression
        exact substSelectorMap_noSimpleSelectors m source
          (List.forall_iff_forall_mem.mp a.inputsNoSimpleSelectors
            source hsource)
      tablesFree := by
        intro table htable
        obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp htable
        rw [substSelectorMap_eq_of_selectorFree m source
          (a.tablesFree source hsource)]
        exact a.tablesFree source hsource
      arity := by simp [a.arity] })
  -- plain projections (not `let (a, b) := …` matches), so record-field access reduces
  -- structurally without evaluating the walk
  let queries := queryWalkInit map cs
  { numAdviceColumns := cs.numAdviceColumns
    numFixedColumns := cs.numFixedColumns + map.newFixedCols
    numInstanceColumns := cs.numInstanceColumns
    numSelectors := cs.numSelectors
    adviceQueryLayout := queries.advice.toList
    fixedQueryLayout := queries.fixed.toList
    instanceQueryLayout := queries.inst.toList
    gates := eraseGates polys queries
    lookups := eraseLookups lookups' queries }

end Halo2
