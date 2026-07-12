import Clean.Halo2.Fixtures.FixtureTypes
import Clean.Halo2.Configure

/-!
# `projectCS` — Halo2-Clean `ConstraintSystem` → ironwood `CsFixture`

Projects a Halo2-Clean `ConstraintSystem Fp` (the output of running a chip's `configure`)
into the ironwood-shaped `CsFixture`, so it can be compared for **equality** against a
fixture dumped from the actual Rust circuit (`AddPre.lean` / `AddPost.lean`).

Two pieces (design doc `vk-matching-design.md` §3):

* **The first-encounter query-index walk** (halo2 `circuit.rs` `query_{advice,fixed,
  instance}_index`): halo2 assigns each *new* `(column, rotation)` the next query index, in
  the order the query is first *built* inside a gate closure. We reproduce that order by a
  left-to-right traversal of each gate polynomial (matching the order the Rust closure
  constructs its sub-expressions), gate by gate. The walk simultaneously (a) accumulates
  the `{advice,fixed,instance}QueryLayout` lists and (b) rewrites each `Query` atom to its
  index, erasing `_root_.Halo2.Expression Fp Query` into the index-based `Expr Fp`.

* **The operator erasure** (`Clean/Halo2/Expression.lean:104-109`): Halo2-Clean's four-node
  `Expression` (`var/const/add/mul`) is lowered to ironwood's `Expr` matching how Rust's
  `std::ops` build `Expression<F>`: `Neg`/`Sub` produce `mul (const (-1)) e ↦ .negated e`,
  `add ↦ .sum`, `mul ↦ .product`, `const ↦ .constant`, and `var ↦ .advice/.fixed/.instance/
  .selector`. (`.scaled` — Rust `expr * field` — is not produced by the ported gates, which
  only use `-`, `+`, `*`, so it never arises here; if a future gate uses `HMul expr F` we
  extend the `mul e (const c)` case.)

Pre-compression keeps `.selector`; post-compression is handled by `projectCSPost` which
substitutes each simple selector by its packed fixed column (for a single-selector gadget:
one new fixed column, replacement = the bare fixed query — see `compress_selectors.rs`).
-/

namespace Clean.Halo2.Fixtures

open _root_.Halo2
open _root_.Halo2.Ironwood (Fp)

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

/-- Erase one `_root_.Halo2.Expression Fp Query` into an `Expr Fp`, threading the query-walk state.
Traversal order (left operand before right, atom on encounter) is what determines the
query indices, so it must match the order the Rust gate closure *builds* its expression.
The Rust `std::ops` build left-to-right (`a - b` builds `a`, then `b`, then combines), so a
plain left-to-right structural traversal reproduces it. -/
def eraseExpr : _root_.Halo2.Expression Fp Query → QueryState → Expr Fp × QueryState
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
  -- Neg/Sub lower to `mul (const (-1)) e`; recognise it as `.negated`.
  | .mul (.const c) e, s =>
      if c = (-1 : Fp) then
        let (e', s) := eraseExpr e s
        (.negated e', s)
      else
        let (e', s) := eraseExpr e s
        (.product (.constant c) e', s)
  | .add a b, s =>
      let (a', s) := eraseExpr a s
      let (b', s) := eraseExpr b s
      (.sum a' b', s)
  | .mul a b, s =>
      let (a', s) := eraseExpr a s
      let (b', s) := eraseExpr b s
      (.product a' b', s)

/-- Erase a list of gate polynomials in order, threading the query walk. -/
def eraseGates : List (_root_.Halo2.Expression Fp Query) → QueryState → List (Expr Fp) × QueryState
  | [], s => ([], s)
  | p :: ps, s =>
      let (e, s) := eraseExpr p s
      let (es, s) := eraseGates ps s
      (e :: es, s)

/-- Flatten a `ConstraintSystem`'s gates to the ordered list of all constraint polynomials
(mirrors halo2 `PinnedGates`' `flat_map(polynomials)`). -/
def flatGates (cs : _root_.Halo2.ConstraintSystem Fp) : List (_root_.Halo2.Expression Fp Query) :=
  cs.gates.flatMap (fun g => g.constraints.map (·.poly))

/-! ### The query-registration seed (halo2 `queried_cells`)

**Load-bearing subtlety** (design doc D6): halo2 assigns query indices in the order
`query_advice`/`query_fixed`/`query_instance` are *called* inside each gate/lookup closure —
i.e. the order the queries are *declared*, not the order they appear in the finished
polynomial AST. A gate authored as "declare all queries via `let`, then build polys" (the
standard idiom, and how the ports read) registers in `let` order; but the first poly's AST
may reference those queries in a different order. So a naive first-encounter walk over the
finished polynomials produces the wrong layout *and* the wrong in-gate indices.

We reproduce halo2 faithfully by pre-seeding the walk with each gate's queried cells in
declaration order (halo2's `Gate::queried_cells`, `circuit.rs`). This seed is per-gadget
data supplied by the caller (the fixture test), exactly mirroring what the Rust closure
records. Once seeded, the erasure DFS finds every query already registered and reuses its
index, matching halo2 for both the layout and the gate expressions. Queries not in the seed
(should be none for a faithful seed) are appended in first-encounter order as a fallback. -/

/-- Pre-register a declaration-order list of query atoms into the walk state. -/
def seedQueries : List Query → QueryState → QueryState
  | [], s => s
  | .selector _ :: qs, s => seedQueries qs s
  | .advice col rot :: qs, s => seedQueries qs (s.advIdx col.index rot).2
  | .fixed col rot :: qs, s => seedQueries qs (s.fixIdx col.index rot).2
  | .instance col rot :: qs, s => seedQueries qs (s.instIdx col.index rot).2

/-- Project a Halo2-Clean `ConstraintSystem` (pre-compression) into the ironwood
`CsFixture`: flatten gates, run the query walk + erasure (seeded with the gadget's
declaration-order queries), read the counts. -/
def projectCS (seed : List Query) (cs : _root_.Halo2.ConstraintSystem Fp) : CsFixture :=
  let (gates, s) := eraseGates (flatGates cs) (seedQueries seed {})
  { numAdviceColumns := cs.numAdviceColumns
    numFixedColumns := cs.numFixedColumns
    numInstanceColumns := cs.numInstanceColumns
    numSelectors := cs.numSelectors
    adviceQueryLayout := s.advice.toList
    fixedQueryLayout := s.fixed.toList
    instanceQueryLayout := s.inst.toList
    gates := gates }

/-! ## Post-compression projection (single-selector gadget)

For a gadget with `numSelectors = 1` simple selector active in its gate, `compress_selectors`
packs it into one new fixed column with `combination_len = 1`, `assigned_root = 1`, so the
replacement expression is the *bare* fixed query on the new column (no `∏(i−q)` factor). The
new fixed column index is `numFixedColumns` (appended after the existing fixed columns), and
its query is registered (via `query_fixed_index`) the *first* time a substituted selector is
encountered during the gate rewrite — i.e. at fixed-query index 0 if there were no prior
fixed queries.

This mirrors halo2's order: compression substitutes selectors first, then the query walk runs
over the substituted expressions. We model that by substituting `Query.selector` for a fixed
query on the packed column *before* the walk. -/

/-- Substitute a single simple selector by a fixed query on the packed column `packedCol`,
rotation 0 (the `combination_len = 1` replacement). Leaves everything else untouched. -/
def substSelector (packedCol : ℕ) : _root_.Halo2.Expression Fp Query → _root_.Halo2.Expression Fp Query
  | .var (.selector _) => .var (.fixed ⟨packedCol⟩ 0)
  | .var q => .var q
  | .const c => .const c
  | .add a b => .add (substSelector packedCol a) (substSelector packedCol b)
  | .mul a b => .mul (substSelector packedCol a) (substSelector packedCol b)

/-- Project the post-compression CS for a **single-selector** gadget: substitute the
selector by the packed fixed column (index = old `numFixedColumns`), grow `numFixedColumns`
by 1, drop `numSelectors` to 0 (selectors don't survive compression), then run the same walk. -/
def projectCSPost (seed : List Query) (cs : _root_.Halo2.ConstraintSystem Fp) : CsFixture :=
  let packedCol := cs.numFixedColumns
  let polys := (flatGates cs).map (substSelector packedCol)
  -- The substituted selector becomes a fixed query on the packed column; register it in
  -- the fixed layout (halo2 does this via `query_fixed_index` during substitution, before
  -- the advice/instance seed of the following gates). Prepend it to the fixed seed.
  let (gates, s) := eraseGates polys (seedQueries (Query.fixed ⟨packedCol⟩ 0 :: seed) {})
  { numAdviceColumns := cs.numAdviceColumns
    numFixedColumns := cs.numFixedColumns + 1
    numInstanceColumns := cs.numInstanceColumns
    numSelectors := cs.numSelectors
    adviceQueryLayout := s.advice.toList
    fixedQueryLayout := s.fixed.toList
    instanceQueryLayout := s.inst.toList
    gates := gates }

end Clean.Halo2.Fixtures
