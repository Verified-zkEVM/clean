# Clean.Air

> :warning: This is partially LLM-written and subject to future human polish

`Clean.Air` contains the row-oriented proof-system layer that sits on top of the core circuit DSL. It is the home for AIR-like objects: components, trace tables, channel balance, ensembles, and formal end-to-end statements.

Two AIR styles are supported, and a single ensemble may mix them.

In **flat AIR**, one circuit is checked independently on each row of a table. The circuit does not directly refer to adjacent rows; all communication between rows and between components is expressed through channel interactions. This matches the modern layout where lookups, VM state transitions, and public API links are modeled by balanced channels rather than by next-row constraints.

In **transition AIR**, one circuit is checked on each *adjacent pair* of rows, and may read cells of both. This is the classic AIR transition constraint, and is the Air-side answer to `TableOperation.everyRowExceptLast`.

Which to reach for:

- **Channels** for cross-*component* communication, and for cross-row structure that is unordered or non-local (a lookup, a VM state handoff, a public API link).
- **Transition constraints** for dense, local, same-table row-to-row structure, where routing through a channel would cost a full lookup argument for what is really just "the next row continues this one".

A **component** records its own row span, in the field `windowRows`: 1 for flat, 2 for transition, and in principle more. The style is therefore *derivable from the component*, not a separate tag — which is what makes the two styles safe to mix. The law that carries this is

```lean
window_size : circuit.size = windowRows * rowWidth
```

The circuit's whole cell footprint tiles exactly `windowRows` rows of width `rowWidth`. Since the verifier already commits to the component, it thereby commits to the window, and a prover cannot reinterpret a transition component as a flat trace — that is not merely forbidden, it is unstateable.

What makes a transition component *mean* something is where the next row lives:

```
Input  = Row (width w)      cells [0, w)   -- row i,   prover-chosen via `witnessAny`
main allocates w cells      cells [w, 2w)  -- row i+1, pinned by local-witness completeness
```

The next row is the circuit's **output**. That is what makes `GeneralFormalCircuit.completeness` provable for a next-row constraint (the cells belong to this instantiation, so `UsesLocalWitnessesCompleteness` pins them) and what makes `Component.Spec input output` the adjacent-row transition relation. A design in which the next row lay outside the circuit's footprint would be able to state neither. `Clean/Examples/FibonacciNextRow.lean` proves both facts for a concrete component.

Which environments a trace presents is captured by the `RowEnvs` class (see `Component.lean`), derived from `windowRows`. In this terminology, a `Flat.Component` is an AIR component: it packages the circuit whose constraints are applied to every row (flat) or every row pair (transition). A `Flat.Table` is the concrete trace table for a component of *either* span — there is one `Table` type, not one per style. A `Flat.TableContext` is a bundle of multiple concrete tables that share the same prover data object.

## Organization

`Circuit.lean` contains shared helpers for using `GeneralFormalCircuit`s as AIR components.

`Component.lean` defines what is shared by both AIR styles:

- `Flat.Component`: the static component, backed by a `GeneralFormalCircuit`, carrying its own row span in `windowRows` and `rowWidth`, tied to the circuit by `window_size`. `envWidth` is the width of one environment, and `envWidth_eq_size` is the *theorem* that it agrees with the circuit's footprint — so `RowEnvs` environments cannot silently disagree with `rowWidth`.
- `input_le_rowWidth`: the circuit's input occupies the low cells of the window's *first* row. This is not implied by `window_size` (a 2-row window with `size Input = 10` and `rowWidth = 5` tiles correctly yet spills its input across both rows), and it is what lets the fixed-column and `ProverData` machinery — all stated about a single row's low indices — apply unchanged.
- `Flat.RowEnvs`: the class that maps a trace to the list of environments its circuit is checked at. This is the single point at which the two styles differ.
- Every trace-level predicate (`Constraints`, `Assumptions`, `Guarantees`, `Requirements`, `Spec`, the `Channel*` family), interaction collection, and `weakSoundness`, all stated once over `RowEnvs` and therefore applying to any window size.

It also proves the component-level transport lemmas: instantiated component operations agree with row operations, and component soundness lifts to whole-trace soundness.

`FlatComponent.lean` defines the trace layer, for windows of any size:

- `Flat.Table`: concrete list of rows for one component. There is one `Table` type regardless of span.
- `windows` / `windowRow` / `windowEnv`: the window at index `i` is the concatenation of rows `i … i + windowRows - 1`, evaluated as one environment. A window exists at `i` exactly when `i + windowRows ≤ length`, so an `n`-row table presents `n + 1 - windowRows` environments — `n` when flat, `n - 1` when transition (`windows_length`, restated as `Table.envs_length` in `Entry.lean`). Any bound on interaction count derived from table heights must use that number, in particular the `< ringChar F` side condition carried by `BalancedInteractions`.
- `Flat.Table.circuitAssumptions`: supplies the fixed-row and derived-data facts at each row index.
- `valueFromOffset_windowEnv`: the current row's input cells read identically from the row alone and from the whole window.

The flat-specific predicates are additionally available in row-shaped form (`∀ row ∈ table.table`), with `envs_eq_of_flat` as the bridge to the shared `RowEnvs` results.

`TransitionComponent.lean` is the two-row *spelling* of that machinery, so transition-specific reasoning reads in terms of `curr`/`next` rather than window indices:

- `pairEnv`: a pair evaluated as the concatenated environment `curr ++ next`. Cell `i` is `curr[i]` and cell `rowWidth + i` is `next[i]`, so "next row" is just an index offset — no new `Expression` node, and no changes to `eval` or `circuit_norm`.
- `Table.IsTransition` (`windowRows = 2`), `Table.pairs`, and `envs_eq_pairs` relating them back to `windows`.
- `valueFromOffset_pairEnv`: the pair-shaped case of `valueFromOffset_windowEnv`.

An `n`-row transition table imposes `n - 1` constraint instances, and a table of 0 or 1 rows is entirely unconstrained. The last row is never a window's `curr`; it appears only as the previous window's `next`. That is safe rather than a soundness hole only because boundary conditions are pinned through channel interactions — see "Not ported from `Clean/Table`" below. Note that `fixed_rows_match` still forces `table.length = fixed.height`: a fixed column covers *every* row including the last, which is a real committed row that the previous window reads.

`Entry.lean` connects tables to the ensemble:

- `Flat.Table.deriveProverData`: each named component is the source of its circuit-input rows. Keyed on rows rather than environments — a transition table is *constrained* on windows, but its *data* is still one input row per trace row, so this does not depend on `windowRows`.
- `Flat.TableContext`: a bundle of committed tables sharing one prover data object. Every operation on it is a `RowEnvs` one, so it applies uniformly to any window size.

The file previously carried a `TableKind` tag, an `Entry` (component + kind) and an `EntryTable` sum type, because flat and transition traces were distinct types one ensemble had to hold together. `windowRows` replaced all three.

`Balance.lean` contains the channel multiset theory. It defines `BalancedInteractions`, proves permutation and counting lemmas, and provides the channel-level implication principles used by higher-level soundness proofs. It also defines `RawChannel.Consistent` and `RawChannel.Normal`; typed channels are normal by construction, and normal channels are consistent, so both properties are satisfied in practice. A highlight in `Balance.lean` is the "guarantees-to-requirements-reversal" theorem which provides the basis for soundness of VM channels.

`FlatEnsemble.lean` defines AIR ensembles, `Flat.Ensemble` and their witnesses, `Flat.EnsembleWitness`. An ensemble has a list of components (which carry their own row spans, so flat and transition tables mix freely), channels, and an append-only verifier program. Components are added with `addTable`, whatever their span. The verifier contributes public interactions directly; its operation type cannot create witnesses, constraints, lookups, or a synthetic table. Its `Statement` is the raw proof-system relation: there exists a witness whose table constraints hold and whose table and verifier interactions are balanced. The ensemble file also defines soundness and completeness and the `FormalEnsemble` structure which bundles an ensemble with its `Spec`, `Assumptions` and the soundness proof (completeness is TODO).

**Ensemble-level soundness** is more than a simple lifting of per-circuit soundness: it requires that channel guarantees, which were _assumed_ as part of local circuit proofs, are shown to hold unconditionally from global channel balance and constraints.

The library currently provides two distinct arguments to establish soundness, covering two prominent ways of using channels:

`OrderedChannel.lean` contains a staged channel construction for ordinary lookup-like channels. The defining property is a strict hierarchy on the list of component tables: any table that pushes to a channel must come before every table that pulls from it. From little more than this property, we prove ensemble-level soundness, as encapsulated in the `SoundEnsemble` structure. On the way, we introduce a relaxed notion of channel balance called `PartialBalancedChannels` that allows the balanced interaction list to contain additional interactions from tables added later. This makes it suitable for an inductive argument or gradual addition of tables to an existing sound ensemble.

Both channel soundness theories are stated over *interaction lists*, with no notion of which row produced what, so a wider window changes only how a table's interaction list is produced and not its type. Consequently they apply to any span unchanged, and there is a single `SoundEnsemble.addTable`: ordering is about which channels a component uses, not how often it is checked.

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

Transition components are supported by the Lean model and its soundness theory, but not yet by the
executable layers. Both layers **refuse** them rather than silently mis-handling them, which is
what keeps the verified statement and the deployed artifact enforcing the same relation:

- **Witness generation** refuses them. `assembleTables` throws unless `windowRows = 1`. Generation
  is row-independent, whereas a multi-row window needs row `i+1` to be produced from row `i`. The
  guard is on the component's own `windowRows`, so there is no tag a caller could set
  inconsistently with the circuit's actual footprint.

  Design for the follow-up, so it is not re-derived: model it on
  `Clean/Table/WitnessGeneration.lean`'s `generateNextRow` — fold the component's witness
  generators over a partially built `next_row`, the environment reading cells `< rowWidth` from
  `cur_row` and `≥ rowWidth` from `next_row`, so later witnesses chain on earlier ones.
  `completeRow` is currently a `map` over rows and would become a fold, since row `i+1` must be
  produced once and reused as row `i+1`'s input.
- **Extraction** covers same-row operations only. `Lower.lean` throws `LoweringError.multiRowWindow`
  unless `windowRows = 1`, and bounds variables by `Component.envWidth` (the whole window) rather
  than one row's width. `Air/Extraction/IR.lean`'s `ComponentProgram` needs a transition variant;
  the backend target is Plonky3's `builder.main().row_slice(1)`, which
  `backends/plonky3/src/generated_air.rs` does not yet use anywhere.
- **`VmTables` are flat by construction.** `tables_windowRows` requires `windowRows = 1` of every
  VM component. This is not a new restriction: every VM obligation was already stated in terms of
  a single row's `rowOperations` at `rowOffset`, so VM components were always implicitly flat.

A worked example is in `Clean/Examples/FibonacciNextRow.lean`: Fibonacci with a next-row constraint
in place of the state channel used by `Clean/Examples/FibonacciVm/Circuit.lean`. It proves the
component's `completeness`, and that its `Spec` at a pair environment is exactly the recurrence
between adjacent rows — the two things no component could do before the next-row-as-output layout.

## Relation To Clean/Table

`Clean/Table` is the older table infrastructure. Its `InductiveTable` interface models classic AIRs where a row transition may directly relate adjacent rows, by putting the output of one VM step in the same relative position as the input of the next step.

The transition component is the `Clean.Air` answer to `TableOperation.everyRowExceptLast`: it recovers adjacent-row constraints without giving up the channel balance argument, so an ensemble can use next-row constraints where they are natural and channels everywhere else.

Not ported from `Clean/Table`:

- **Boundary constraints** (`TableOperation.boundary`). Until they exist, a transition ensemble must pin its boundaries through the verifier's public channel interactions. This is workable — it is how `Vm.lean` already seeds and terminates the VM state channel — but it is a genuine difference, and it is why a 0- or 1-row transition table being unconstrained is safe rather than a soundness hole.
- **Windows wider than two rows.** `windowRows` is an arbitrary `ℕ` and `windows` is generic in it, so a 3-row window needs no new code at all — but nothing currently builds one, and `TransitionComponent.lean`'s `curr`/`next` spelling covers only the two-row case.
- **`InductiveTable`** and its `Spec`-carrying inductive interface.

The two layers remain independent, but `Clean.Air` is intended to become the common home for AIR-style infrastructure, including future support for the older inductive table style now living under `Clean/Table`.
