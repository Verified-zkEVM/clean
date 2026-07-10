# Halo2-Clean: The Lookup-Argument Axis — Design

Design document for adding lookup arguments to Halo2-Clean. The framework currently
models custom gates, copy constraints, and the permutation argument; lookups exist only
as stubs (`LookupArgument`, `lookupTableColumn`, `lookup`, `ConstraintSystem.lookups` in
`Configure.lean`). This document proposes the semantics and the proof-facing model, and
enumerates the contested decisions for the maintainer before code is written.

The hard reference rule carries over: every claim about halo2 below is read from the
actual source at `/mnt/data-2tb/zks/halo2/` (tag `halo2_gadgets-0.5.0`), cited with
file:line, never from memory.

The first consumer is `halo2_gadgets::utilities::lookup_range_check` — the K-bit
range-check table with running-sum decomposition — so its requirements drive the design.

---

## 1. Rust semantics summary

### 1.1 What a lookup argument is in the constraint system

A lookup argument is registered via `ConstraintSystem::lookup`
(`halo2_proofs/src/plonk/circuit.rs:1056-1079`):

```rust
pub fn lookup(
    &mut self,
    table_map: impl FnOnce(&mut VirtualCells<'_, F>) -> Vec<(Expression<F>, TableColumn)>,
) -> usize {
    let mut cells = VirtualCells::new(self);
    let table_map = table_map(&mut cells)
        .into_iter()
        .map(|(input, table)| {
            if input.contains_simple_selector() {
                panic!("expression containing simple selector supplied to lookup argument");
            }
            let table = cells.query_fixed(table.inner());
            (input, table)
        })
        .collect();
    let index = self.lookups.len();
    self.lookups.push(lookup::Argument::new(table_map));
    index
}
```

Three facts, each load-bearing:

1. **The input side is an arbitrary `Expression<F>`**, the table side is a `TableColumn`
   — but the table column is *immediately* converted to a fixed-column query at
   rotation 0 (`cells.query_fixed(table.inner())`). So both sides end up as
   `Expression<F>`. The stored argument is
   (`halo2_proofs/src/plonk/lookup.rs:7-11`):

   ```rust
   pub(crate) struct Argument<F: Field> {
       pub input_expressions: Vec<Expression<F>>,
       pub table_expressions: Vec<Expression<F>>,
   }
   ```

   A single `meta.lookup` may carry *several* `(input, table)` pairs — a tuple lookup.
   The range-check gadget uses a single pair; the tagged 4/5-bit variant uses two.

2. **Simple selectors are banned in input expressions** (circuit.rs:1064-1066, `panic!`).
   This is why gadgets gate lookup inputs on *complex* selectors (`complex_selector()`),
   not the simple selectors used for gates. The framework's `Selector` already carries
   `simple : Bool`; the ban is a well-formedness condition on the registered argument,
   not a semantic one.

3. **Registration order matters for the VK**: `self.lookups.push(...)` appends in
   `configure`-call order (`ConstraintSystem.lookups: Vec<lookup::Argument<F>>`,
   circuit.rs:954). The pinned CS (`PinnedConstraintSystem`, circuit.rs:976) exposes
   `lookups` by reference — it is part of the VK fingerprint.

`TableColumn` wraps a fixed column, with a security note (circuit.rs:314-324): its inner
column MUST NOT be exposed as a general fixed column, because tables are default-value
filled and mixing the two breaks that convention.

### 1.2 The enforced relation (membership, not permutation)

The proof-system machinery is a compressed grand-product / permuted-pair argument
(verifier polynomials at `halo2_proofs/src/plonk/lookup/verifier.rs:92-167`; prover at
`lookup/prover.rs`). Underneath the commitments, the relation it enforces is
**multiset membership of compressed rows**, made explicit by the prover's
`permute_expression_pair` (`lookup/prover.rs:565-628`):

- Each side is compressed across the tuple with a challenge θ
  (`lookup/prover.rs:65-73`):
  `A_compressed = θ^{m-1} A_0 + … + A_{m-1}`, and likewise `S_compressed`.
- For every usable row, the compressed input value must occur in the multiset of
  compressed table values. The prover builds a `leftover_table_map` (a count of each
  table value) and, for the first occurrence of each input value, decrements that count;
  if the value is absent it returns `Error::ConstraintSystemFailure`
  (`lookup/prover.rs:596-606`). So:

  > **For every usable row `r`, the tuple
  > `(input_0(r), …, input_{m-1}(r))` equals some row of the table
  > `(S_0, …, S_{m-1})`.**

  This is a *subset* relation (input rows ⊆ table rows as multisets over the θ-compressed
  values, and — since θ is a random challenge — over the raw tuples with overwhelming
  probability). It is NOT a permutation: the table may contain values no input row uses.

"Usable rows" excludes the blinding rows at the bottom of the domain
(`prover.rs:573-574`, `usable_rows = n - (blinding_factors + 1)`). Framework-level
soundness is stated over usable rows; the bridge to the polynomial argument (joint work
with ironwood) discharges the blinding-row accounting.

### 1.3 Table columns: whole-column, default-filled

Table columns are filled globally via `Layouter::assign_table`, addressing **absolute**
rows (not region-relative). The range-check table load
(`halo2_gadgets/src/utilities/lookup_range_check.rs:434-450`):

```rust
layouter.assign_table(|| "table_idx", |mut table| {
    for index in 0..(1 << K) {
        table.assign_cell(|| "table_idx", self.table_idx, index,
            || Value::known(F::from(index as u64)))?;
    }
    Ok(())
})
```

Two behaviors that the disabled-row convention depends on:

1. **Default-fill.** After the explicit assignment, the layouter fills every remaining
   usable row of the table column with the value from **row 0**
   (`floor_planner/single_pass.rs:176-182` calling
   `fill_from_row(col.inner(), first_unused, default_val.unwrap())`; the row-0 capture is
   `table_layouter.rs:95-97`, `(true, 0) => entry.0 = Some(value)`; the fill loop is
   `keygen.rs:152-170`, `for row in usable_rows.skip(from_row) { col[row] = filler }`).
   For the range-check table, row 0 holds `0`, so **every unused table row is `0`**.

2. **No gaps, equal lengths.** `assign_table` errors unless every row from 0 to the last
   assigned row is filled (`table_layouter.rs:127-131`, `ColumnNotAssigned`) and all
   columns of a multi-column table have equal length
   (`table_layouter.rs:138-146`, `UnevenColumnLengths`). So a table is a dense block of
   rows `[0, len)` in its fixed column, then the row-0 value to the end of the domain.

### 1.4 The disabled-row / default convention

A lookup argument holds at *every* row of the domain, including rows a gadget does not
"use". Gadgets therefore arrange for unused rows to look up a value that is guaranteed to
be in the table — the default value at table row 0. They do this by multiplying the
input expression by a complex selector, `q_lookup`, so that when the row is not
participating (`q_lookup = 0`) the input evaluates to `0`, and `0` is table row 0.

`lookup_range_check::configure` (`lookup_range_check.rs:334-366`) is the canonical
pattern:

```rust
meta.lookup(|meta| {
    let q_lookup  = meta.query_selector(config.q_lookup);   // complex selector
    let q_running = meta.query_selector(config.q_running);  // complex selector
    let z_cur     = meta.query_advice(config.running_sum, Rotation::cur());
    let one = Expression::Constant(F::ONE);

    // running-sum row: a_i = z_i - 2^K z_{i+1}
    let running_sum_lookup = {
        let z_next = meta.query_advice(config.running_sum, Rotation::next());
        let running_sum_word = z_cur.clone() - z_next * F::from(1 << K);
        q_running.clone() * running_sum_word
    };
    // short row: the word is witnessed directly
    let short_lookup = {
        let q_short = one - q_running;
        q_short * z_cur
    };

    vec![( q_lookup * (running_sum_lookup + short_lookup), config.table_idx )]
})
```

So the single lookup input is
`q_lookup · (q_running · (z_cur − 2^K·z_next) + (1 − q_running) · z_cur)`.

- `q_lookup = 0` ⇒ input `= 0` ∈ table (default row). Disabled rows are free.
- `q_lookup = 1, q_running = 1` ⇒ input `= z_cur − 2^K·z_next = a_i`, the i-th K-bit word.
- `q_lookup = 1, q_running = 0` ⇒ input `= z_cur`, a directly-witnessed short word.

Membership then forces `a_i ∈ [0, 2^K)` — the range check. The gadget's soundness needs
the table to be *exactly* `[0, 2^K)`; membership alone in an arbitrary table proves
nothing. The gadget itself does not constrain the table contents — correctness of the
table is a load-side obligation (see §2.4).

Note the selector kinds: `q_lookup`, `q_running` are `complex_selector()`
(`lookup_range_check.rs:320-321`) precisely because they appear inside a lookup input;
`q_bitshift` is a simple `selector()` (line 322) because it only guards an ordinary gate.
This matches the selector survey (`halo2-selector-survey.md:46-65`): all non-trivial
selector arithmetic lives in lookup inputs over complex selectors.

---

## 2. Proposed Lean model

The guiding tension, already flagged in `halo2-selector-survey.md:61-65` and
`Operations.lean:57`: **gate constraints are region-local and enter `Constraints` from
the ops list, but a lookup argument is CS-global and holds at every absolute row.** The
proposal reconciles these by keeping the *argument* global (registered in `configure`,
matching the stub) while letting *enabling* it be an ordinary region operation whose
semantics is local — exactly the design already used for `enableGate`.

### 2.1 Where lookup arguments live: `configure`, as data

Keep the stub's placement: `configure` registers `LookupArgument`s into
`ConstraintSystem.lookups` in call order. Fix the stub's *contents* to mirror Rust — the
current `tableMap : List (Expression F Query × TableColumn)` is wrong on two counts
(the table side is a fixed *query*, not a `TableColumn`; and it drops the input/table
split Rust stores). Proposed (this is the uncontested data fix, see §6):

```lean
/-- A lookup argument. Rust `lookup::Argument<F>`: a tuple of (input, table) expression
pairs; the relation enforced is per-row membership of the input tuple in the table.
Both sides are `Expression F Query`; the table side is always a rotation-0 fixed query
(Rust wraps the `TableColumn`'s inner fixed column with `query_fixed`). -/
structure LookupArgument (F : Type) where
  inputs : List (Expression F Query)
  tables : List (Expression F Query)
```

`lookup` (the `Configure` action) takes the raw `(input, TableColumn)` pairs like Rust,
performs the `query_fixed` wrap and the unzip, and appends the argument. The simple-selector
ban (§1.1.2) is a well-formedness predicate `LookupArgument.wellFormed` checked at the VK
boundary, not enforced by the constructor (proofs never depend on it).

### 2.2 How the semantics enter — the central decision

**Proposal: lookup enabling is a region operation (`enableLookup`), dual to `enableGate`;
its per-op semantics is a local membership fact; the global "holds at every row" view is
the VK-boundary bridge, exactly as for gates.**

Rationale. The framework already faced this exact shape for custom gates. A gate is
globally "`∀ row, guard(row)·poly(row) = 0`", but the ops list only records
`enableGate gate row`, and `RegionOperation.Constraints` gives it the *local* meaning
"the compiled polys vanish at this row under `own selector ↦ 1`"
(`Operations.lean:138-144`). The bridge to the global 0/1-activation-table view is
declared a once-per-circuit VK-boundary lemma (`Configure.lean:59-63`,
`Operations.lean:50-52`). Lookups get the identical treatment:

Add a region operation
```lean
| enableLookup : LookupArgument F → ℕ → RegionOperation F
```
emitted by an `enableLookup` DSL atom (the analogue of `Gate.enable`; there is no single
Rust method — a gadget "enables a lookup at a row" by enabling the complex selector(s)
its input expression is gated on, so in the port `enableLookup arg row` is sugar the
gadget's `synthesize` emits alongside the `enable` of `q_lookup`). Its local semantics:

```lean
| .enableLookup arg row =>
    ∃ tableRow : ℤ,
      arg.inputs.map (·.eval (Query.eval env sel (place self + row))) =
      arg.tables.map (·.eval (Query.eval env sel tableRow))
```

read: "the input tuple at this row equals the table tuple at *some* table row". Here
`sel` is the local activation valuation `fun i => if i ∈ enabledSelectorsHere then 1 else
0` — the same device `enableGate` uses (`Operations.lean:143`, `own selector ↦ 1`), so
that `q_lookup = 1` at the enabled row and the input reduces to the participating word.

Why this shape, versus the alternatives (§6 weighs them):

- **Soundness gets a clean, local hypothesis.** A range-check gadget's soundness assumes
  `∃ tableRow, word = env.fixed table_idx tableRow` at each enabled row. Combined with the
  *table-contents fact* (§2.4) that `env.fixed table_idx r ∈ [0,2^K)` for the rows the
  table occupies, it concludes `word ∈ [0, 2^K)`. No global quantifier leaks into the
  gadget proof; it stays region-relative (requirements doc: "Proofs are region-relative").
- It composes through subcircuits with zero new machinery: `enableLookup` is just another
  `RegionOperation`, folded into the `.subcircuit` chunk like everything else.
- The disabled-row convention *never appears in gadget proofs*. Disabled rows are handled
  entirely at the VK bridge, where the global "every row is a member" statement is proven
  from (a) the enabled rows' local facts and (b) the default-fill fact that every
  non-participating row's input is `0` = table row 0. The gadget only ever asserts
  membership at rows it enabled.

The membership existential (`∃ tableRow`) is deliberately weak — it is exactly what the
proof system delivers. It is *not* "input ∈ {0,…,2^K−1}"; that stronger statement is
derived by the gadget from membership + table contents, keeping the framework agnostic to
what any particular table means.

**This membership predicate is the missing half of ironwood's lookup soundness.** Ironwood
proves only *gate* satisfaction; it evaluates the five lookup constraint polynomials
(`Verifier/Expressions.lean:90-102`, the log-derivative/permuted-pair identity from
verifier.rs:92-167) and folds them into the quotient check, but explicitly does **not**
connect `permutedInputEval`/`permutedTableEval` to the combinatorial table-membership
relation — that is deferred to their issue #14 (`Soundness/Constraints.lean:24-27`:
"does not connect the permutation and lookup terms to the circuit-level … lookup
constraints"). The framework's `enableLookup` membership fact is precisely the
circuit-level statement that joint bridge must land on: the shared lemma (requirements
doc §"Semantics: trace satisfaction") will have the form *ironwood's polynomial lookup
identity ⇒ this framework's per-row membership predicate*. Designing the membership
predicate as the raw-tuple existential (§D5) keeps it on the clean side of that bridge.

### 2.3 Table contents in the `Environment`

Table columns are fixed columns, and `Environment.get`/`Environment.fixed` already reads
fixed columns at absolute rows (`Expression.lean:175-176`). No new environment field is
needed — the requirements doc's "no analogue of `data`: halo2 lookup tables are fixed
columns, already covered by `get`" (`Expression.lean:136-137`) holds. The table's
*contents* are facts about `env.fixed table_col r` for `r` in the table's row range.

The membership existential in §2.2 quantifies `tableRow : ℤ` over the whole column. That is
faithful (any table row is a legal witness) but usually a gadget wants membership in the
*meaningful* range `[0, len)`. Two ways to get there, both fine:

- Let the table-contents fact (§2.4) characterize `env.fixed table_col r` for **all** `r`
  (participating rows = their intended value; default-filled rows = the row-0 value). Then
  `∃ tableRow, …` directly yields a value in the intended set, because every row of the
  column — filled or default — is in it (for range-check, `0` is in `[0,2^K)` too).
- Or bound `tableRow` to `[0, len)` in the enable semantics. Rejected: it hard-codes the
  table's row layout into the per-op semantics, which the floor planner owns.

### 2.4 Table loading and what completeness must supply

Table loading is a `Circuit` action, not a region operation on advice — it addresses
absolute rows in a fixed column. Two representations (decision in §6):

**Recommended: a `loadTable` layouter operation carrying the intended contents, plus a
proven-from-loading table-contents lemma.**

```lean
| loadTable : TableColumn → (values : List F) → Operation F
```

Its `Constraints` semantics pins the fixed column, mirroring `assignFixed` but over the
whole block and with the default-fill:

```lean
| .loadTable tbl values :: ops, i =>
    (∀ r, r < values.length → env.fixed tbl.inner r = values[r]!) ∧
    (∀ r, values.length ≤ r → r < domainUsableRows → env.fixed tbl.inner r = values[0]!)
    ∧ Constraints place env ops i
```

- The first conjunct is the explicit assignment (range-check: `values = [0,1,…,2^K−1]`).
- The second is the **default-fill** (§1.3.1): unused usable rows carry the row-0 value.
  For the range-check table `values[0]! = 0`, giving the "disabled rows look up 0" fact.
- `domainUsableRows` is a placement/layout parameter, threaded like `place`; it is the
  only new global the lookup axis introduces, and it appears only at the VK bridge and in
  `loadTable`, never in region-local gadget proofs.

Then a **table-contents lemma** (proven once per table type from its `loadTable` op) says
`∀ r < domainUsableRows, env.fixed table_col r ∈ IntendedSet`. `lookup_range_check`'s
soundness consumes this lemma as a hypothesis; membership + lemma ⇒ range.

- **Soundness** gets to *assume* the table-contents lemma (the table was loaded; that its
  fixed column holds the loaded values is part of `Constraints` via `loadTable`). This is
  the same status `assignFixed` already has: `Operations.lean:137`,
  `env.get col (place self + row) = v` is a *constraint*, not something soundness must
  prove — the VK/keygen guarantees fixed columns hold their assigned values.
- **Completeness** must *discharge* it: the honest prover's `ExtendsWitnesses`/loading
  produces an environment whose table column holds `[0,2^K)` then `0`-padding. Add a
  `loadTable` case to `ExtendsWitnesses` obliging the prover to fill the column so, and a
  completeness lemma that this satisfies the `loadTable` constraint. The prover's
  membership obligation at each enabled row (produce the `tableRow`) is discharged from
  the running-sum decomposition: `a_i < 2^K` ⇒ `tableRow := a_i` works.

The alternative — *axiomatize* each table's contents as a hypothesis on soundness without
a `loadTable` op — is simpler but severs the load from the VK (a table nobody loads would
still "work" in a proof). Rejected for the same reason `assignFixed` is a real op: the VK
bridge must see the load. See §6.

### 2.5 What a lookup-using contract looks like

A lookup-using `FormalRegionCircuit`/`FormalCircuit` needs no structural change — lookups
enter through the ops list like every other operation, and `Constraints` already folds
them. The only additions are conventions:

- The **table load** is typically a *separate* one-shot circuit (`load()` in Rust,
  called once per chip, `lookup_range_check.rs:397/434`), i.e. its own `FormalCircuit`
  whose `Spec` is "the table column holds `[0,2^K)`". Range-check *user* gadgets
  (`range_check`, `short_range_check`) take the loaded config and **assume** the
  table-contents lemma as an extra `Assumptions`/hypothesis — mirroring Rust, where
  `load` is the caller's responsibility and the check helper trusts it
  (`lookup_range_check.rs:81-83`, "The table can be loaded outside this helper").
- Soundness assumes: the `Constraints` chunk (which now includes `enableLookup`'s local
  membership facts) **and** the table-contents lemma (delivered by whoever loaded the
  table — either an assumption, or `Constraints` of the load subcircuit if loading is in
  scope). Concludes the `Spec` (`word ∈ [0,2^K)`).
- Completeness discharges: `ExtendsWitnesses` produces the running-sum cells; the
  membership existential at each enabled row is witnessed by the decomposed word; the
  disabled-row inputs are `0` by the gating (no obligation — those rows aren't enabled).

This keeps the two open seams honored: soundness/completeness stay region-relative
(`i₀`, `place`, `offset` generic), and the global lookup statement is confined to the VK
bridge.

---

## 3. Decision points

### D1. Global-vs-op-level semantics attachment  *(recommend: op-level, §2.2)*

- **Option A (op-level, recommended):** an `enableLookup` region op with a local
  membership semantics; global "every row" is a VK-boundary lemma.
  - *Pro:* dual to the already-shipped `enableGate` design; region-relative gadget proofs;
    subcircuit composition free; disabled-row convention stays out of gadget proofs.
  - *Con:* introduces a new op and a small non-interference obligation at the bridge
    (only the rows a gadget enabled contribute its membership facts — the survey's
    "decidable non-interference condition", `halo2-selector-survey.md:63-65`).
- **Option B (global):** `Constraints` gains a top-level conjunct quantifying over all
  rows and all registered lookups, threaded from the `ConstraintSystem`.
  - *Pro:* closest to the literal proof-system statement.
  - *Con:* forces the global `ConstraintSystem` and absolute rows into gadget soundness,
    breaking region-relativity (requirements doc explicitly forbids: "Soundness/
    completeness of a gadget never depends on where the floor planner puts its regions").
    The framework already rejected this for gates — consistency argues for rejecting it
    here.

Recommendation: **A**. It is the same trade the framework already made for gates, and the
selector survey was written in anticipation of it.

### D2. Table contents: proven from a load op vs axiomatized  *(recommend: proven, §2.4)*

- **Option A (recommended): `loadTable` op + table-contents lemma proven from it.** The
  load is a real operation; its `Constraints` pin the column (explicit block +
  default-fill); soundness assumes the pinned facts, completeness discharges them.
  - *Pro:* the load is visible to the VK bridge (fixed columns and their fill are VK data);
    parallels `assignFixed`; a table that is never loaded cannot silently satisfy proofs.
  - *Con:* need to model default-fill and the `domainUsableRows` layout parameter.
- **Option B: axiomatize contents as a soundness hypothesis, no load op.**
  - *Pro:* less machinery up front.
  - *Con:* the load disappears from the compiled artifact; VK recovery would have to
    reconstruct table fixed columns from nothing. Breaks "the compiled artifact is a
    constraint system + layout" (requirements doc).

Recommendation: **A**, for VK fidelity — the same reason constants are first-class copies
rather than `.const` (requirements doc, "Modeling them as gate-level `.const` would break
VK matching").

### D3. Disabled-row convention: where it is expressed  *(recommend: default-fill fact at the bridge, §2.2/§2.4)*

- **Option A (recommended):** express it as the default-fill conjunct of `loadTable`
  (every unused usable row = row-0 value) and discharge the "every row is a member" claim
  at the VK bridge; gadgets never mention disabled rows.
  - *Pro:* matches Rust exactly (the layouter's `fill_from_row`, not the gadget, provides
    it); keeps gadget proofs to enabled rows only.
- **Option B:** make each gadget prove membership at *all* rows in its region, including
  the `q_lookup = 0` ones, by unfolding the input-gating expression to `0`.
  - *Con:* pushes a global, layout-dependent obligation into every gadget; duplicates the
    default-fill reasoning at every call site.

Recommendation: **A**. The convention is a *table-loading* property in Rust, so it lives
with `loadTable`, not with lookup users.

### D4. Lookup soundness: extra hypothesis vs inside `Constraints`  *(recommend: inside `Constraints`, via `enableLookup`; table-contents as an extra hypothesis)*

Two sub-questions, resolved differently:

- **The membership fact** (input tuple ∈ table at enabled rows) enters **inside
  `Constraints`**, as the semantics of the `enableLookup` op. It is a *constraint the
  proof enforces*, so it belongs in the same predicate as gate and copy constraints — the
  single-ground-truth-`Constraints` design (issue #358, `Operations.lean:158-176`).
- **The table-contents fact** enters as an **extra hypothesis / assumption** for user
  gadgets that don't load the table themselves (mirroring Rust's "load is the caller's
  job"), or as the `Constraints` of the in-scope `loadTable` subcircuit when loading *is*
  in scope. Not baked into every lookup user's `Constraints`.

Recommendation as stated: membership in `Constraints`; table-contents as an assumption
(or an in-scope load's constraints). This mirrors how `assignFixed` (a constraint) and
"the VK loaded these fixed columns" (an ambient guarantee) already split.

### D5. Multi-input tuple lookups and the θ-compression  *(recommend: model the raw tuple, ignore θ)*

The proof system compresses tuples with a random challenge θ (§1.2). At the framework's
membership level this is invisible: "input tuple = some table tuple" over raw field
tuples is the statement θ-compression soundly implements (θ random ⇒ tuple equality whp).
Model `enableLookup` over the *raw tuple* (`List (Expression F Query)` on each side); the
θ soundness is part of the polynomial-argument bridge (ironwood joint work), not the
framework predicate. Range-check uses a 1-tuple; the tagged variant a 2-tuple — the list
form covers both.

### D6. `domainUsableRows` as a layout parameter  *(recommend: thread it like `place`)*

Default-fill and the "every row" bridge need the domain size / usable-row bound. It is
layout data (depends on `k`), so thread it as a semantics parameter alongside `place`
(the requirements doc's floor-planner output). It appears only in `loadTable` and the VK
bridge — never in region-relative gadget statements — so it does not compromise
region-relativity.

---

## 4. Consumer sketch: `lookup_range_check`

Illustrative, not compile-checked. Ports `lookup_range_check.rs` under the proposal.

```lean
namespace Halo2.LookupRangeCheck

/-- Rust `LookupRangeCheckConfig<F, K>` (lookup_range_check.rs:63-70). -/
structure Config (K : ℕ) where
  qLookup   : Selector          -- complex
  qRunning  : Selector          -- complex
  qBitshift : Selector          -- simple
  runningSum : Column .advice
  tableIdx  : TableColumn

/-- Rust `configure` (lines 313-387): allocate selectors, register the lookup + bitshift
gate. Verbatim-ported. `runningSum` handed down by the parent (ConfigInput). -/
def configure (K : ℕ) (runningSum : Column .advice) : Configure F (Config K) := do
  let qLookup   ← complexSelector
  let qRunning  ← complexSelector
  let qBitshift ← selector
  let tableIdx  ← lookupTableColumn
  -- the lookup input, verbatim from lines 334-366
  lookup {
    -- one (input, table) pair:
    -- q_lookup * (q_running*(z_cur - 2^K z_next) + (1 - q_running)*z_cur)  ↦  tableIdx
    ...
  }
  createGate { name := "range check bitshift", selector := qBitshift, constraints := ... }
  return { qLookup, qRunning, qBitshift, runningSum, tableIdx }

/-! ### The table loader — its own FormalCircuit -/

/-- Rust `load_range_check_table` (lines 434-450): fill tableIdx with 0..2^K. -/
def loadTable (cfg : Config K) : Circuit F Unit :=
  -- emits a single `loadTable` layouter op with values = (List.range (2^K)).map (↑·)
  loadTableOp cfg.tableIdx ((List.range (2^K)).map (fun i => (i : F)))

def tableLoader (K : ℕ) : FormalCircuit F (Config K) (Config K) unit unit where
  configure := pure                         -- table registered by the user's configure
  synthesize cfg _ := loadTable cfg
  Spec _ _ _ := True                        -- postcondition captured by the lemma below
  soundness := ...  -- trivial; the content is the lemma:
  completeness := ...

/-- Table-contents lemma (proven from `loadTable`'s Constraints): every usable row of
`tableIdx` holds a value in [0, 2^K). Consumed by `range_check` soundness. -/
theorem tableIdx_range (cfg : Config K) (place) (env)
    (h : (loadTable cfg).Constraints place env) :
    ∀ r, r < domainUsableRows → (env.fixed cfg.tableIdx.inner r).val < 2^K := ...

/-! ### The user gadget: range_check via running sum -/

/-- Rust `range_check` (lines 171-241): decompose `element` into `numWords` K-bit words,
assign the running sum, enable the lookup on each word row. Region-level. -/
def rangeCheck (cfg : Config K) (numWords : ℕ) (offset : ℕ) (element : AssignedCell F) :
    RegionCircuit F (List (AssignedCell F)) := do
  ... -- assign z_0 = element (copyAdvice), then for i in 0..numWords:
      --   assignAdvice runningSum (offset+i+1) (witgen: (z_i - a_i)/2^K)
      --   enable qLookup, qRunning at row (offset+i)   ⇒ emits enableLookup arg (offset+i)
  ...

/-- The formal package. `Assumptions` carries the table-contents lemma. -/
def formalRangeCheck (K numWords : ℕ) :
    FormalRegionCircuit F (Config K) (Config K)
      (Unconstrained field) (fun _ => List AssignedCell ...) where
  synthesize cfg offset element := rangeCheck cfg numWords offset element
  Assumptions input :=
    -- the table has been loaded: ∀ usable r, tableIdx[r] < 2^K
    TableLoaded cfg
  Spec input outputs _ :=
    -- element decomposes into numWords K-bit words: element = Σ a_i 2^{Ki}, each < 2^K
    ∃ words, element.val = ... ∧ ∀ w ∈ words, w < 2^K
  soundness := by
    -- from each enableLookup: ∃ r_i, a_i = tableIdx[r_i]; with TableLoaded ⇒ a_i < 2^K;
    -- running-sum algebra ⇒ element = Σ a_i 2^{Ki}
    ...
  completeness := by
    -- witness the running sum; membership witnessed by tableRow := a_i (a_i < 2^K)
    ...
```

Notes drawn from the Rust:

- `short_range_check` (lines 455-490) is a second `RegionCircuit` sharing the same
  `Config`; it enables `qLookup` at rows 0 and 1 and `qBitshift` at row 1. Same shape.
- The `qRunning`/`qLookup` complex-selector split is why the input expression, not a gate,
  carries them — `enableLookup` records the argument; the selectors are recorded by the
  same op's activation (the local `sel` valuation sets them to 1 at the enabled row).
- `strict` mode (lines 235-238) adds a `constrainConstant zs.last 0` — already expressible
  with the existing `constrainConstant` op.

---

## 5. VK-bridge implications

The ironwood verifier already models the lookup registration — validating the shape of
this section. Its `VerifyingKey` carries (`Zcash/Snark/Verifier/Assemble.lean:64-79`):

```lean
lookupInputExprs : Fin shape.numLookups → List (Expr F)
lookupTableExprs : Fin shape.numLookups → List (Expr F)
```

i.e. exactly the `(inputs, tables : List (Expression F Query))` split proposed in §2.1,
one per registered lookup, indexed by registration order (`shape.numLookups`). Ironwood's
`Expr` (`Verifier/Expressions.lean:29-37`) has `constant/fixed/advice/instance` atoms plus
`negated/sum/product/scaled` — the target of the framework's semantics-preserving erasure
of its 4-node `Expression` (requirements doc; `Expression.lean:229-235`). So the VK bridge
must produce, per lookup, two `List (Expr F)` that match ironwood's fixture after erasure.

What must be preserved verbatim for VK comparison:

1. **`ConstraintSystem.lookups`, in registration order.** The pinned CS exposes
   `lookups: &Vec<lookup::Argument<F>>` (circuit.rs:976). Halo2-Clean's
   `ConstraintSystem.lookups` (already present in the stub) must match element-for-element
   (⇒ ironwood's `lookupInputExprs`/`lookupTableExprs` indexed by `Fin numLookups`) after
   the same query-index erasure gates undergo. Each `LookupArgument` compares as its
   `(inputs, tables)` — both projected to bare query-index variables via the framework's
   `Expression` erasure (`Expression.lean:229-235`, `mapVar`), then compared as exact
   expression trees.

2. **The table side is a rotation-0 fixed query.** Because Rust stores the table side as
   `query_fixed(table.inner())` (circuit.rs:1068), the VK's `table_expressions` are always
   `Fixed { column, rotation: 0 }`. The Lean model storing `tables : List (Expression F
   Query)` where each is `queryFixed col` (rotation 0) reproduces this exactly. The
   `TableColumn` → fixed-column mapping (which fixed column index each table occupies) is
   VK data via `fixed_queries` and the fixed-column count, already covered.

3. **Query registration.** Lookup input/table expressions feed the same first-encounter
   `fixed_queries`/`advice_queries`/`instance_queries` walk as gates
   (circuit.rs:1081-1110). At VK-compilation time the framework's query-index assignment
   must include lookup expressions in the walk, in the right order (Rust walks them as part
   of building the argument). This is a VK-compiler obligation, not a semantics one, but it
   must be gotten right or query indices shift.

4. **`num_fixed_columns` includes table columns.** `lookupTableColumn` allocates a fixed
   column (`Configure.lean:140-141`, already correct); the count must match the fixture's
   fixed-column total.

5. **The simple-selector ban** (§1.1.2) is a VK-validity check, not a comparison field —
   but if a ported `configure` violated it, the real halo2 would `panic!` at keygen and no
   VK would exist. Encode it as a `wellFormed` side condition checked during VK
   compilation.

Not VK-relevant: the membership *semantics* (§2.2), `loadTable`'s default-fill, and
`domainUsableRows` are proof-side / layout-side; they do not appear in the pinned CS.

---

## 6. Uncontested data fix (may land as code)

Only the `LookupArgument` data definition and the `lookup`/`lookupTableColumn` plumbing
are uncontested (they mirror Rust directly and carry no semantics). Everything else in
this document is a proposal pending maintainer sign-off. If the data fix is applied:

- `LookupArgument` becomes `{ inputs, tables : List (Expression F Query) }` (§2.1),
  replacing the placeholder `tableMap`.
- `lookup` takes `List (Expression F Query × TableColumn)`, wraps each table column as a
  rotation-0 fixed query (`queryFixed`), unzips into `inputs`/`tables`, and appends.

No `enableLookup` op, no `loadTable` op, no semantics changes land until the decisions in
§3 are settled — those touch `RegionOperation`/`Operation` and `Constraints`, which is the
semantic core this document exists to get reviewed first.

---

## 7. Rust findings that surprised / constrain the design

- **The table side is not a `TableColumn` in the stored argument — it is an
  `Expression` (a rotation-0 fixed query).** The stub's `tableMap : … × TableColumn` is
  doubly wrong (drops the input/table split *and* keeps the un-queried column). Faithful
  VK matching needs the expression form.
- **Simple selectors are banned in lookup inputs (a `panic!`).** Gadgets must and do use
  complex selectors for lookup gating (`q_lookup`, `q_running`). The framework's
  `Selector.simple` bit already distinguishes them; the ban is a well-formedness check.
- **The disabled-row convention is a *table-loading* property, not a gadget property.**
  The layouter's `fill_from_row` (single_pass.rs:176) pads unused rows with the *row-0*
  value, and gadgets gate inputs to `0` so those rows hit row 0. This cleanly separates:
  gadgets prove membership only at rows they enable; "every row is a member" is discharged
  once, at the bridge, from the default-fill. This is why §2.4 makes default-fill a
  `loadTable` conjunct rather than a gadget obligation.
- **`assign_table` forbids gaps and requires equal column lengths** (table_layouter.rs
  :127, :138). Tables are dense `[0, len)` blocks — the `loadTable` `values : List F`
  representation (§2.4) captures this exactly and the length is intrinsic.
- **Membership, not permutation.** `permute_expression_pair` errors iff an input value is
  absent from the table multiset (prover.rs:596-606) — a subset relation. The `∃ tableRow`
  existential in §2.2 is precisely this, and is deliberately weaker than "input ∈ intended
  set", which the gadget derives via the table-contents lemma.
- **Ironwood's `VerifyingKey` already has the exact `(inputs, tables)` split proposed
  here** (`lookupInputExprs`/`lookupTableExprs : Fin numLookups → List (Expr F)`), so the
  data model is pre-validated — but **ironwood defers lookup soundness entirely** (issue
  #14): it checks the lookup quotient polynomial but never proves table membership. The
  framework's `enableLookup` membership predicate is the circuit-level target the joint
  soundness bridge must reach. This makes the membership-predicate choice (§D1, §D5) not
  just a framework-internal convenience but the interface contract with the ironwood
  effort — worth settling deliberately.
```
