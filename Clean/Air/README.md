# Clean.Air

> :warning: This is partially LLM-written and subject to future human polish

`Clean.Air` contains the row-oriented proof-system layer that sits on top of the core circuit DSL. It is the home for AIR-like objects: components, trace tables, channel balance, ensembles, and formal end-to-end statements.

Two AIR styles are supported, and a single ensemble may mix them.

In **flat AIR**, one circuit is checked independently on each row of a table. The circuit does not directly refer to adjacent rows; all communication between rows and between components is expressed through channel interactions. This matches the modern layout where lookups, VM state transitions, and public API links are modeled by balanced channels rather than by next-row constraints.

In **transition AIR**, one circuit is checked on each *adjacent pair* of rows, and may read cells of both. This is the classic AIR transition constraint, and is the Air-side answer to `TableOperation.everyRowExceptLast`.

Which to reach for:

- **Channels** for cross-*component* communication, and for cross-row structure that is unordered or non-local (a lookup, a VM state handoff, a public API link).
- **Transition constraints** for dense, local, same-table row-to-row structure, where routing through a channel would cost a full lookup argument for what is really just "the next row continues this one".

A component records its own row span in `windowRows` (1 for flat, 2 for transition), tied to the circuit by the law `window_size : circuit.size = windowRows * rowWidth`. The style is therefore derivable from the component rather than a separate tag, which is what makes the two styles safe to mix: the verifier commits to the component and thereby to the window.

For a transition component the next row is the circuit's **output** — `Input` is all of row `i`, and `main` witnesses row `i+1`:

```
Input  = Row (width w)      cells [0, w)   -- row i,   prover-chosen via `witnessAny`
main allocates w cells      cells [w, 2w)  -- row i+1, pinned by local-witness completeness
```

This is what makes `GeneralFormalCircuit.completeness` provable for a next-row constraint and `Component.Spec input output` the adjacent-row transition relation.

In this terminology, a `Flat.Component` is an AIR component: it packages the circuit whose constraints are applied to every row (flat) or every row pair (transition). A `Flat.Table` is the concrete trace table for a component of either span — there is one `Table` type, not one per style. A `Flat.TableContext` is a bundle of multiple concrete tables that share the same prover data object.

## Organization

`Circuit.lean` contains shared helpers for using `GeneralFormalCircuit`s as AIR components.

`Component.lean` defines what is shared by both AIR styles:

- `Flat.Component`: the static component, backed by a `GeneralFormalCircuit`, carrying its own row span in `windowRows` and `rowWidth`, tied to the circuit by `window_size`. `envWidth` is the width of one environment, and `envWidth_eq_size` is the *theorem* that it agrees with the circuit's footprint — so a table's environments cannot silently disagree with `rowWidth`.
- `input_le_rowWidth`: the circuit's input occupies the low cells of the window's *first* row. Not implied by `window_size`, and needed because the fixed-column and `ProverData` machinery is all stated about a single row's low indices.
- `input_eq_rowWidth`: for a multi-row window the input is the *entire* first row, so that every cell of row `i+1` has a single witnessing owner (window `i`) rather than also being own-row scratch of window `i+1`. Intermediate values are instead expressed as extra columns of the row type. Flat components are unaffected.

It also proves the component-level transport lemmas: instantiated component operations agree with row operations, and component soundness lifts to whole-environment soundness (`Component.weakSoundness`).

`FlatComponent.lean` defines the trace layer, for windows of any size:

- `Flat.Table`: concrete list of rows for one component. There is one `Table` type regardless of span.
- `Flat.Table.envs`: the list of environments the circuit is checked at — one per window. Every trace-level predicate (`Constraints`, `Assumptions`, `Guarantees`, `Requirements`, `Spec`, the `Channel*` family), every interaction collection, and `weakSoundness` quantify over it and never inspect an individual environment, which is why they apply to any window size.
- `windows` / `windowRow` / `windowEnv`: the window at index `i` is the concatenation of rows `i … i + windowRows - 1`, evaluated as one environment. An `n`-row table presents `n + 1 - windowRows` environments, which is the number any bound on interaction count must use — in particular the `< ringChar F` side condition of `BalancedInteractions`.
- `Flat.Table.circuitAssumptions`: supplies the fixed-row and derived-data facts at each row index.
- `valueFromOffset_windowEnv` / `valueFromOffset_windowEnv_curr`: a typed read of size `≤ rowWidth` gives the same value from row `i` alone as from the window at `i`.

For a flat table the environments are exactly the rows: `envs_eq_of_flat` and `mem_envs_of_mem_table` let callers who only build flat tables (VM ensembles) keep reasoning row-shaped.

`TransitionComponent.lean` is the two-row reading of that machinery: the **window-induction library**, which turns `Table.Spec` — the circuit's `Spec` at every window, i.e. what `TableSoundness` hands you — into an induction along the trace:

- `Table.IsTransition` (`windowRows = 2`) and `windowRow_eq_pair`: the window at `i` is `rows[i] ++ rows[i+1]`, so cell `rowWidth + j` is `next[j]` and "next row" is just an index offset — no new `Expression` node, no changes to `eval` or `circuit_norm`.
- `valueFromOffset_windowEnv_next`, `rowInput_windowEnv`, `rowOutput_windowEnv`: the typed readings of the window's two rows. `rowOutput_windowEnv` takes "the circuit's output variable is the canonical next-row layout" as a *hypothesis* rather than a `Component` field, so the library stays additive.
- `Table.transition_induction`: given `t.Spec data`, any `P` that holds at row 0 and is preserved by the circuit's `Spec` across an adjacent pair holds at every row. Callers state their invariant over indexed rows and never touch a window index.

An `n`-row transition table imposes `n - 1` constraint instances, and a table of 0 or 1 rows is entirely unconstrained. The last row is never a window's `curr`, which is safe only because the ends of the trace are pinned separately — by a boundary assertion or a channel interaction.

`TableContext.lean` connects tables to the ensemble:

- `Flat.Table.deriveProverData`: each named component is the source of its circuit-input rows. Keyed on rows rather than windows, so it does not depend on `windowRows`.
- `Flat.TableContext`: a bundle of committed tables sharing one prover data object. Every operation on it quantifies over each table's `envs`, so it applies uniformly to any window size.

`Balance.lean` contains the channel multiset theory. It defines `BalancedInteractions`, proves permutation and counting lemmas, and provides the channel-level implication principles used by higher-level soundness proofs. It also defines `RawChannel.Consistent` and `RawChannel.Normal`; typed channels are normal by construction, and normal channels are consistent, so both properties are satisfied in practice. A highlight in `Balance.lean` is the "guarantees-to-requirements-reversal" theorem which provides the basis for soundness of VM channels.

`Boundary.lean` defines **boundary assertions**, the direct route from a trace to the public input. A `Boundary.Assertion` is an assert-only constraint set — no witnesses, lookups or channel interactions — over the typed input prefix of a designated trace row (first or last, matching the two rows with native AIR selectors) and the public input, bundled with the `Spec` it is proved to imply. A `Boundary.Entry` attaches one to an ensemble table, keyed by component name (stable under `addTable`, which prepends). An entry naming a missing table, or one whose designated row does not exist, is *unsatisfiable* rather than vacuous. Together with a transition component these make shift-constraint AIR tables expressible: the transition constraint carries the induction, a first-row assertion pins the seed, a last-row assertion exports the result, and channels remain for lookups and cross-component interactions.

`FlatEnsemble.lean` defines AIR ensembles, `Flat.Ensemble` and their witnesses, `Flat.EnsembleWitness`. An ensemble has a list of components (which carry their own row spans, so flat and transition tables mix freely), channels, boundary assertions, and an append-only verifier program. Components are added with `addTable`, whatever their span, and boundary assertions with `addBoundary`. The verifier contributes public interactions directly; its operation type cannot create witnesses, constraints, lookups, or a synthetic table. Its `Statement` is the raw proof-system relation: there exists a witness whose table constraints hold, whose boundary assertions hold, and whose table and verifier interactions are balanced. The ensemble file also defines soundness and completeness and the `FormalEnsemble` structure which bundles an ensemble with its `Spec`, `Assumptions` and the soundness proof (completeness is TODO). For ensembles with boundary assertions, `SpecConsistencyWithBoundaries` is the consistency notion to prove: it receives the boundary specs alongside the table specs.

**Ensemble-level soundness** is more than a simple lifting of per-circuit soundness: it requires that channel guarantees, which were _assumed_ as part of local circuit proofs, are shown to hold unconditionally from global channel balance and constraints.

The library currently provides two distinct arguments to establish soundness, covering two prominent ways of using channels:

`OrderedChannel.lean` contains a staged channel construction for ordinary lookup-like channels. The defining property is a strict hierarchy on the list of component tables: any table that pushes to a channel must come before every table that pulls from it. From little more than this property, we prove ensemble-level soundness, as encapsulated in the `SoundEnsemble` structure. On the way, we introduce a relaxed notion of channel balance called `PartialBalancedChannels` that allows the balanced interaction list to contain additional interactions from tables added later. This makes it suitable for an inductive argument or gradual addition of tables to an existing sound ensemble.

Both channel soundness theories are stated over interaction lists, with no notion of which row produced what, so they apply to any span unchanged: ordering is about which channels a component uses, not how often it is checked.

`Vm.lean` contains a construction aimed at "VM-like" components that perform one transition per row. Since VM components both pull from and push to one distinguished state channel, they cannot follow the theory of ordered lookup-channel soundness. Instead, we prove a dedicated soundness theorem that applies to a set of VM components added to an existing hierarchical ensemble; a typical modern zkVMs layout.

`WitnessGeneration.lean` constructs ensemble witnesses from public input and a separately typed
runtime prover input. Demand-driven components allocate rows from channel messages. Preallocated
components initialize their prover-owned cells from constants or strided positions in the prover
input, while the generic builder supplies any verifier-fixed prefix. Preallocated channel handlers
identify an existing component interaction and a generated multiplicity column; messages and row
indices are derived from completed rows rather than duplicated in generation metadata.

The prover input is only an input to honest witness construction. Semantic `ProverData` is always
derived from the final committed component inputs. Export currently permits `dataGet` only from
stable cells of preallocated components and rejects reads from demand-generated or mutable cells.
This makes the initial data snapshot used by witness generation agree with the final derived data
at every readable location.

## Current limits of the transition kind

Transition components are supported by the Lean model, its soundness theory, and Lean-side witness
generation, but not yet by extraction. Whatever an executable layer cannot express it **refuses**,
which is what keeps the verified statement and the deployed artifact enforcing the same relation:

- **Witness generation** supports them through `Mode.transition`: a seed row program plus a
  committed row count. Generation is a chain — `input_eq_rowWidth` makes the current row the
  circuit's whole input and the witness block exactly the next row, so one generator run per window
  (`transitionStep`) extends the trace by one row. Padding continues the chain rather than stamping
  `Padding.input`, so padded suffixes satisfy the transition constraints by construction, and
  interactions are accounted per window. Windows wider than two rows are refused by `assembleTables`.
- **Extraction** covers same-row operations only: `Lower.lean` throws `LoweringError.multiRowWindow`
  unless `windowRows = 1`. `Air/Extraction/IR.lean`'s `ComponentProgram` needs a transition variant;
  the backend target is Plonky3's `builder.main().row_slice(1)`, which `backends/plonky3` does not
  yet use.
- **`VmTables` are flat by construction** (`tables_windowRows`). Not a new restriction: every VM
  obligation was already stated in terms of a single row.
- **Boundary assertions are Lean-only.** `Lower.lean` throws `LoweringError.boundaryAssertions` for
  any ensemble carrying one, because `backends/plonky3` does not yet emit
  `when_first_row`/`when_last_row` constraints or route public values into them.

`Clean/Examples/FibonacciTransition.lean` is the example to read for how the pieces fit. It proves
`fibonacciTransition_soundness`, the *same* public claim as `fibonacci_soundness`, from a mixed
ensemble: a transition component carries the recurrence, two boundary assertions pin the seed and
export the final state, and the byte-add lookup remains the only channel. Two points worth lifting
out of it:

- **Padding.** Backends pad to a power of two, and a last-row assertion reads the last *committed*
  row. The component therefore carries a boolean `enabled` selector: an enabled row advances the
  state, a disabled row freezes it — including the selector itself, so it can never turn back on.
- **Inline the selector's booleanity.** `GeneralFormalCircuit.requirementsChannelsLawful` sees only
  the circuit's *inline* constraints, not those of subcircuits, so a selector gating a channel
  interaction must be constrained with a bare `assertZero (enabled * (enabled - 1))` rather than
  through the `assertBool` gadget.

## Relation To Clean/Table

`Clean/Table` is the older table infrastructure. Its `InductiveTable` interface models classic AIRs where a row transition may directly relate adjacent rows, by putting the output of one VM step in the same relative position as the input of the next step.

The transition component is the `Clean.Air` answer to `TableOperation.everyRowExceptLast`: it recovers adjacent-row constraints without giving up the channel balance argument, so an ensemble can use next-row constraints where they are natural and channels everywhere else.

Not ported from `Clean/Table`:

- **General boundary row indices** (`RowIndex.fromStart k` / `fromEnd k`). `Boundary.lean` covers first and last row, the two with native selectors, but not interior rows.
- **Windows wider than two rows.** `windowRows` is an arbitrary `ℕ` and `windows` is generic in it, but nothing currently builds one, and `TransitionComponent.lean` covers only the two-row case.
- **`InductiveTable`** and its `Spec`-carrying inductive interface.

The two layers remain independent, but `Clean.Air` is intended to become the common home for AIR-style infrastructure, including future support for the older inductive table style now living under `Clean/Table`.
