# Clean.Air

> :warning: This is partially LLM-written and subject to future human polish

`Clean.Air` contains the row-oriented proof-system layer that sits on top of the core circuit DSL. It is the home for AIR-like objects: components, trace tables, channel balance, ensembles, and formal end-to-end statements.

The first supported AIR style is **flat AIR**. In a flat AIR, one circuit is checked independently on each row of a table. The circuit does not directly refer to adjacent rows. All communication between rows and between components is expressed through channel interactions. This matches the modern layout where lookups, VM state transitions, and public API links are modeled by balanced channels rather than by next-row constraints.

In this terminology, a `Flat.Component` is a one-row AIR component: it packages the circuit whose constraints are applied to every row. A `Flat.Table` is the concrete trace table and prover data for such a component. A `Flat.Tables` value is a lightweight bundle of multiple concrete tables that share the same prover data object.

## Organization

`Circuit.lean` contains shared helpers for using `GeneralFormalCircuit`s as AIR components.

`FlatComponent.lean` defines the flat AIR component layer:

- `Flat.Component`: the static one-row component, backed by a `GeneralFormalCircuit`.
- `Flat.Table`: concrete array of rows for one component, together with the prover data used to evaluate constraints and channel interactions. Its fields guarantee that the rows agree with the component's fixed cells, and that the prover data contains the table's inputs under the component's name, so component soundness proofs can use both.
- `Flat.Tables`: a bundle of tables sharing one prover data object.
- `Component.FixedRowsMatch`: the rows of a preallocated component agree with its fixed cells, the verifier-known columns.

It also proves the basic row-level transport lemmas: instantiated component operations agree with row operations, component soundness lifts to table soundness, and table interactions can be collected per channel.

`Balance.lean` contains the channel multiset theory. It defines `BalancedInteractions`, proves permutation and counting lemmas, and provides the channel-level implication principles used by higher-level soundness proofs. It also defines `RawChannel.Consistent` and `RawChannel.Normal`; typed channels are normal by construction, and normal channels are consistent, so both properties are satisfied in practice. A highlight in `Balance.lean` is the "guarantees-to-requirements-reversal" theorem which provides the basis for soundness of VM channels.

`Verifier.lean` defines the verifier program language: an append-only list of public interactions, together with the verifier's spec and its soundness.

`RowProgram.lean` decides which witness IR a row program may use: the fixed cells of a preallocated component are computed from the row index alone, and its witness cells can also read the hint.

`Lookup.lean` defines a convenience wrapper for static lookups.

`FlatEnsemble.lean` defines flat AIR ensembles, `Flat.Ensemble` and their witnesses, `Flat.EnsembleWitness`. An ensemble is everything a prover and a verifier implementation need: components, channels, a verifier program, and the type of the prover's private input. The verifier only contributes public interactions directly. Its `Statement` is the raw proof-system relation: there exists a witness whose table constraints hold and whose interactions are balanced. Every table of a witness carries the prover data derived from all the witness tables. The ensemble file also defines soundness and completeness and the `FormalEnsemble` structure which bundles an ensemble with its `Spec`, `Assumptions`, the `ProverAssumptions` of witness generation, and the soundness proof (completeness is TODO), like `FormalCircuit` does for a circuit.

**Ensemble-level soundness** is more than a simple lifting of per-circuit soundness: it requires that channel guarantees, which were _assumed_ as part of local circuit proofs, are shown to hold unconditionally from global channel balance and constraints.

The library currently provides two distinct arguments to establish soundness, covering two prominent ways of using channels:

`OrderedChannel.lean` contains a staged channel construction for ordinary lookup-like channels. The defining property is a strict hierarchy on the list of component tables: any table that pushes to a channel must come before every table that pulls from it. From little more than this property, we prove ensemble-level soundness, as encapsulated in the `SoundEnsemble` structure. On the way, we introduce a relaxed notion of channel balance called `PartialBalancedChannel` that allows the balanced interaction list to contain additional interactions from tables added later. This makes it suitable for an inductive argument or gradual addition of tables to an existing sound ensemble.

`Vm.lean` contains a construction aimed at "VM-like" components that perform one transition per row. Since VM components both pull from and push to one distinguished state channel, they cannot follow the theory of ordered lookup-channel soundness. Instead, we prove a dedicated soundness theorem that applies to a set of VM components added to an existing hierarchical ensemble; a typical modern zkVMs layout.

`WitnessGeneration.lean` constructs ensemble witnesses from the public input and the prover's private input, see the next section.

## Witness generation

Witness generation is driven by channel balance. In a valid witness, every channel message is pushed as often as it is pulled. The generator keeps a tally of the messages that don't cancel yet, their *demand*, and answers it one message at a time: the component that handles the message adds or updates a row that cancels it. The new row has interactions of its own, which create new demand. So witness generation is a chain reaction, which ends when the tally is empty.

For example, the verifier of a VM pushes the initial state and pulls the final state. Nothing pulls the initial state yet, so the VM gets a row that pulls it and pushes the next state, which is again unanswered, and so on. Each VM row may also pull from other channels: an addition chip then gets a row for the addition, and a memory counts one more read of the address. The reaction stops once a row pushes the final state, which the verifier pulls.

Each component declares how it answers demand in its `generation` field, whose types are defined in `WitnessGeneration/Generation.lean`:

- **demand**: the component starts empty and gets a new row whenever a message on its channel is unanswered. The row's input is built from the message. How it answers repeated messages depends on whether its input uses a multiplicity cell: if not, each occurrence gets its own row (a VM step); if yes, they share one row whose multiplicity cell counts them (a chip). After balancing, these tables are padded to a power-of-two height. Padding rows can interact too, so the generator balances again until no table grows. A proving backend may also need a minimum trace height, which the Plonky3 backend pads to.
- **preallocated**: the component has a fixed number of rows from the start, like a memory with one row per address or a lookup table. Its input must have exactly one multiplicity cell, and demand on its channel only increments it.

Several components may answer the same channel, like the opcode tables of a VM, which share its state channel. A demand component can then restrict the messages it answers by a *guard*, a witness program over the message: an opcode table's guard reads the opcode at the state's `pc` from the program table. Each message must be accepted by exactly one component: a demand component whose guard holds, or a preallocated component with a row for it. `Clean/Examples/OpcodeVm` is a toy VM built this way.

Both modes describe the input of a row as a witness program producing the component's input type, with a *cell* for every input variable: a fixed cell, whose value the verifier knows and which only preallocated rows have; a witness cell, which the prover computes; or the multiplicity cell, the multiplicity of the component's interaction on its channel. A memory row emitting `memoryChannel.emit multiplicity { address, value }` has the input `{ address := .fixed i.toField, value := .witness ..., multiplicity := .multiplicity }`, and a chip row emitting `add8.emit m (x, y, z)` gets the input `{ x, y, z, m := .multiplicity }` from the message `(x, y, z)`. To answer a pulled message, the generator finds the row whose interaction on the channel carries that message and increments its multiplicity cell, or, in a chip, creates the row if there is none yet. The multiplicity may not influence the message it counts, so incrementing it never changes which message a row answers.

The fixed cells of a preallocated component are its fixed columns, wherever they sit in the input. Every table's rows agree with them by a field of `Flat.Table`, and the Plonky3 backend commits them as preprocessed columns.

The prover's private input is declared by the `Ensemble`: its type, and the hint tables through which witness programs read it. The `FormalEnsemble` adds the `ProverAssumptions` on public and private input that witness generation needs. The Plonky3 backend in `backends/plonky3` implements the same algorithm in Rust, and runs it on generation modes and witness programs extracted by `Clean/Backends`.

The generator currently makes assumptions that come from our examples rather than from the idea, listed in the module doc of `WitnessGeneration.lean`. None of them is fundamental.

## Relation To Clean/Table

`Clean/Table` is the older table infrastructure. Its `InductiveTable` interface models classic AIRs where a row transition may directly relate adjacent rows, by putting the output of one VM step in the same relative position as the input of the next step. `Clean.Air.Flat` instead models the modern one-row style: each component checks a single row in isolation, and all cross-row or cross-component structure is mediated by channels. The two layers are currently independent, but `Clean.Air` is intended to become the common home for AIR-style infrastructure, including future support for the older inductive table style now living under `Clean/Table`.
