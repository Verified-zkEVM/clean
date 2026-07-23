# Halo2-Clean: Configure-Time Query Registration — Design (APPROVED)

> **STATUS: approved by the maintainer (2026-07-23); correction applied — `Gate.queriedCells`
> has NO default value.** This document is a handoff: it specifies the change for an
> implementing agent. The design core (§3) and the implementation checklist (§5) are
> normative; §1–§2 are the source-grounded rationale.

Phase C of the VK-derivation program (see `vk-matching-design.md` for phases A/B history,
and ironwood's `book/src/formal-verification/action-circuit-integration.md` for the
consuming side): make the Halo2-Clean `ConstraintSystem` record its own **query layouts**
— the ordered `(column, rotation)` lists that halo2's keygen builds during `configure()` —
so that ironwood's `PartialPinnedConstraintSystem.derive` no longer needs a caller-supplied
query seed. After this change plus ironwood's floor-planner port (phase B, done: derived
region starts, activations, and the `compress_selectors` map are all circuit-side), the
whole pinned constraint system is derived from the circuit with no fixture witnesses.

The hard reference rule carries over: every halo2 claim below is read from
`/mnt/data-2tb/zks/halo2/` (tag `halo2_gadgets-0.5.0`), cited file:line.

---

## 1. What Rust does (the semantics to reproduce)

Query indices are **execution-order artifacts of `configure()`**. Three sources, all
appending first-encounter into `cs.{advice,fixed,instance}_queries`:

1. **Gate closures.** `create_gate` runs the closure with a `VirtualCells`
   (`circuit.rs:1195-1202`); `VirtualCells::query_advice/fixed/instance`
   (`circuit.rs:1495-1520`) register **at call time** via `query_*_index` — i.e. in the
   closure's `let`-order, not in any traversal order of the finished polynomial. The
   `query_*_index` functions (`circuit.rs:1081-1126`) are linear-scan first-encounter:
   return the existing index if `(column, rotation)` is already present, else append.
   `query_fixed` takes no rotation in this halo2 version — always `Rotation::cur()`
   (`circuit.rs:1495-1503`). `query_advice_index` additionally bumps the per-column
   counter `num_advice_queries[column.index]` (`circuit.rs:1107`) — the input to
   `blinding_factors`.
2. **`enable_equality`** (`circuit.rs:1046-1050`): registers a cur-rotation query on the
   column (`query_any_index(column, Rotation::cur())`, `circuit.rs:1127-1136`) and *then*
   adds it to the permutation argument. `enable_constant` (`circuit.rs:1038-1044`) pushes
   the constants column and calls `enable_equality`, so it registers a cur fixed query.
   This is where the Action circuit's entire `instanceQueryLayout = [(0, 0)]` comes from —
   the instance column is never queried by any gate. These calls interleave with gate
   creation in chip-configure order, which is why no post-hoc walk over the finished CS
   can reproduce the index order.
3. **`lookup`** (`circuit.rs:1056-1079`): the table-map closure runs first (its
   `query_*` calls register, closure execution order), then each pair's table column is
   wrapped as a cur fixed query (`cells.query_fixed(table.inner())`, `circuit.rs:1068`)
   — so table-wrap registrations come **after all of that closure's input queries**, in
   pair order.

Post-configure, `compress_selectors` registers one more cur fixed query per packed
selector column, in combination order (`circuit.rs:1268-1273`). That step is
ironwood-side (it needs the floor-planned activation table) and stays there: ironwood
appends the packed columns from its derived `SelCompressMap` to the configure-recorded
fixed queries (§6).

Rust's `Gate` itself stores the closure's query calls: `queried_selectors` /
`queried_cells` (`circuit.rs:894-901`, captured from the `VirtualCells` at
`circuit.rs:1202-1203, 1220-1221`). §3 mirrors exactly this field.

## 2. Why the two "obvious" designs fail

**Monadic gate builders** (make `queryAdvice` a `Configure` action, gate bodies do-blocks)
would be the verbatim port — but Halo2-Clean's pure gate builders are shared with the
synthesize layer: e.g. `Clean/Ironwood/Ecc/AddIncomplete.lean` calls
`(gate config.qAddIncomplete …).enable offset` inside `synthesize`, and proofs reduce
these pure applications. Monadizing the builders either breaks synthesize or forces
`Gate` values into `Config` records, making gate constraints opaque to proofs. Rejected
for proof-ergonomic cost, not principle.

**Traversal-order registration** (walk the gate's polynomials at `createGate` time,
first-encounter) is *provably wrong*: AddIncomplete's closure queries
`x_p, y_p, x_q, y_q, x_r, y_r` in that order (Rust registers that order,
`ecc/chip/add_incomplete.rs`), but `poly1 = (x_r + x_q + x_p) * …` *uses* `x_r` first —
an AST walk would register `(xQR, +1)` before `(xP, 0)`. Let-order ≠ use-order, on the
first chip one looks at. A traversal also misses queries whose atoms end up unused in the
final polynomials (Rust registers at call time regardless).

## 3. The design

Everything stays pure; the registration *data* moves into `Gate`, and the registration
*effect* happens in the `Configure` actions that already exist.

### 3.1 `ConstraintSystem` gains the query lists

```lean
structure ConstraintSystem (F : Type) where
  …
  adviceQueries   : List (Column .advice × Rotation) := []
  fixedQueries    : List (Column .fixed × Rotation) := []   -- rotation always 0 (§1.1)
  instanceQueries : List (Column .instance × Rotation) := []
```

Builder-state defaults (`[]`) are correct here — this is the accumulator, not per-gate
data. Fixed queries keep a `Rotation` field for direct mapping onto the pinned
`fixedQueryLayout : List (ℕ × ℤ)`, with registration always inserting `0` (mirror of
`circuit.rs:1091`). `num_advice_queries`/`blinding_factors` need no extra field — count
occurrences per column in `adviceQueries`.

### 3.2 Registration primitives (mirror `query_*_index`)

`Configure` actions with exact first-encounter semantics (`circuit.rs:1081-1126`): if the
`(column, rotation)` pair is present, no-op; else append. Plus a `queryAnyIndex`
dispatcher (`circuit.rs:1127-1136`) for `enableEquality`. These are internal — gate
authors never call them.

### 3.3 `Gate.queriedCells` — mandatory, no default

```lean
structure Gate (F : Type) where
  name : String
  selector : Selector
  queriedCells : List (Expression F Query)   -- NO default value
  constraints : List (Constraint F)
```

Each gate builder lists its query atoms **in the Rust closure's `let`-order**, literally
reusing the existing lets:

```lean
def gate (…) : Gate Fp where
  …
  queriedCells := [x_p, y_p, x_q, y_q, x_r, y_r]   -- add_incomplete.rs create_gate order
  constraints := …
```

The list reads like the Rust query block and is verbatim-checkable against it; each entry
should carry (or the list a single) comment citing the Rust chip closure. Entries are the
same pure atoms the constraints use, so no duplication of column/rotation data — only of
*order*, which is exactly the information the finished AST does not contain (§2).

**Maintainer ruling: no default value.** A `:= []` default would make every unswept gate
compile and be silently wrong (its queries never registered, every downstream index
shifted). With the field mandatory, the sweep is enforced by the compiler: every gate
construction site fails to elaborate until its author states the query order.
Non-`var` entries (anything that isn't a query atom) are ill-formed; registration
filter-maps the `var` atoms and should be written so a non-atom is loud (see checklist).

`querySelector` atoms do NOT belong in `queriedCells`: selectors get no query index
(Rust tracks them in the separate `queried_selectors`, `circuit.rs:1490`, which we do not
need — nothing in the pinned CS consumes it).

### 3.4 Effects in the existing `Configure` actions

- `createGate gate` — first register `gate.queriedCells` in list order (dedup per §3.2),
  then append the gate. (Rust order: the closure's queries all execute before the gate is
  pushed, `circuit.rs:1195-1229`.)
- `enableEquality c` — register the cur query on `c` (`queryAnyIndex`), then the
  (existing, deduped) permutation-column append — this order per `circuit.rs:1046-1050`.
  Registration is NOT conditional on the column being new to the permutation: Rust
  registers unconditionally (idempotence comes from `query_*_index` dedup).
- `enableConstant col` — constants push + the `enableEquality` effect
  (`circuit.rs:1038-1044`); the current inlined permutation-add must gain the query
  registration.
- `lookup` — gains a mandatory `queriedCells : List (Expression F Query)` argument (the
  lookup closure has the same let-vs-use order problem as gates): register those first
  (closure execution, §1.3), then per pair in order register the table column's cur fixed
  query (`circuit.rs:1068`) — table wraps strictly after all closure queries.

Registration interleaving across chips = execution order of the `Configure` monad =
verbatim port order. No other part of the framework changes: `Expression`, `Query`, the
pure `queryAdvice/queryFixed/queryInstance/querySelector` helpers, synthesize, and all
proofs are untouched.

## 4. Trust story

The hand-listed `queriedCells` order is a per-gate witness, exactly like the caller-
supplied seed it replaces — but it now sits adjacent to the Rust closure it mirrors
(reviewable line-by-line), and it is *certified*: ironwood's `native_decide` equality
against the captured verifying key (`capturedPinnedCs_eq_derived`) compares the derived
`{advice,fixed,instance}QueryLayout` fields, so any wrong order fails the theorem. Clean's
own per-chip VK fixtures give earlier, localized checks (§5.7). A wrong list cannot be
silently absorbed — it shifts every later index in the layout.

## 5. Implementation checklist (for the implementing agent)

Work in this repo (`Verified-zkEVM/clean`, branch `halo2-clean-2`). Read
`Clean/Halo2/Configure.lean`, `Clean/Halo2/Expression.lean`, and one gadget
(`Clean/Ironwood/Ecc/AddIncomplete.lean`) before starting. Hard reference rule: take
every order from the actual Rust chip source (orchard / halo2_gadgets sibling checkouts),
cite file:line next to each `queriedCells` list.

1. `Configure.lean`: extend `ConstraintSystem` (§3.1); add the registration primitives
   (§3.2). Registration of a `queriedCells` entry: match on the atom — `var (.advice c r)`
   / `var (.fixed c r)` / `var (.instance c r)` register; `var (.selector _)` and any
   non-`var` expression should `panic!`-equivalent loudly (e.g. register into a poisoned
   marker or use a dedicated total function returning a `Bool` validity the tests
   `#guard`) — do NOT silently skip. Pick the loud mechanism that fits; document it.
2. `Configure.lean`: `Gate` gains mandatory `queriedCells` (§3.3); `createGate`,
   `enableEquality`, `enableConstant`, `lookup` gain the effects (§3.4), `lookup` the
   mandatory argument.
3. Sweep every gate builder and `lookup` call site (`grep -rln "Gate Fp where\|lookup "
   Clean/Ironwood Clean/Halo2` and the Tests/Examples trees). For each, open the
   corresponding Rust chip `create_gate`/`lookup` closure and transcribe the `query_*`
   call order. The compiler enforces completeness (no default). ~30 gates plus a handful
   of lookups expected.
4. Do not change `Expression`/`Query`/synthesize/proof files. If a proof or test
   constructs a `Gate` literal, it must state `queriedCells` too (usually `[]` is *wrong*
   — transcribe the real order; a test-only synthetic gate may genuinely query nothing).
5. Keep `Configure.lean`'s module docs honest: the "gate bodies are pure / indices
   assigned by a first-encounter walk at VK-compilation time" rationale
   (`Configure.lean:16-19`) is superseded by this design — rewrite it to describe
   configure-time registration and WHY (let-order, §2).
6. Validation, in order: (a) everything builds; (b) Clean's existing VK-match fixture
   tests stay green (they pin gates/lookups, not the new lists); (c) NEW checks — for
   each per-chip fixture that dumps query layouts, `#guard` the CS-recorded
   `{advice,fixed,instance}Queries` (mapped to `(colIndex, rotation)` pairs) against
   them; where a fixture lacks layouts, at minimum `#eval`-print the recorded lists for
   the mul/action harnesses and eyeball against the Rust dump in the ironwood repo
   (`Zcash/Snark/Fixtures/SingleAction/VkCsData.lean`:
   `vkAdviceQueryLayout`/`vkFixedQueryLayout`/`vkInstanceQueryLayout` — note those are
   POST-compression, so the fixed list has 15 extra packed-column entries at the END;
   advice and instance lists must match exactly).
7. Report: files touched, any gate whose Rust query order was ambiguous or surprising
   (e.g. queries in helper functions called by the closure — transcribe in execution
   order), and the validation results.

## 6. Ironwood follow-up (out of scope here, for context)

After this lands and ironwood bumps its Clean pin: `csSeed` is rebuilt from
`cs.{instance,advice,fixed}Queries`; the fixed seed is extended with the packed selector
columns from the derived `SelCompressMap` in combination order (mirroring
`circuit.rs:1268-1273`); `PartialPinnedConstraintSystem.derive` drops its seed parameter,
completing `FormalCircuit.deriveVkCs` with no witness inputs; the capture-equality
theorems re-certify end-to-end.
