# Clean.Air

> :warning: This is LLM-written and subject to future human edits

`Clean.Air` contains the row-oriented proof-system layer that sits on top of the core circuit DSL. It is the home for AIR-like objects: components, trace tables, channel balance, ensembles, and formal end-to-end statements.

The first supported AIR style is **flat AIR**. In a flat AIR, one circuit is checked independently on each row of a table. The circuit does not directly refer to adjacent rows. All communication between rows and between components is expressed through channel interactions. This matches the modern layout where lookups, VM state transitions, and public API links are modeled by balanced channels rather than by next-row constraints.

In this terminology, a `Flat.Component` is a one-row AIR component: it packages the circuit whose constraints are applied to every row. A `Flat.Table` is the concrete trace table and prover data for such a component. A `Flat.Tables` value is a lightweight bundle of multiple concrete tables that share the same prover data object.

## Files

`Circuit.lean` contains shared helpers for using `GeneralFormalCircuit`s as AIR components. It instantiates a reusable circuit into a fixed row circuit, provides empty/verifier circuits, and defines environment helpers for reading typed inputs from row data.

`FlatComponent.lean` defines the flat AIR component layer:

- `Air.Flat.Component`: the static one-row component, backed by a `GeneralFormalCircuit`.
- `Air.Flat.Table`: concrete rows for one component, together with the prover data used to evaluate constraints and channel interactions.
- `Air.Flat.Tables`: a bundle of tables sharing one prover data object.

It also proves the basic row-level transport lemmas: instantiated component operations agree with row operations, component soundness lifts to table soundness, and table interactions can be collected per channel.

`Balance.lean` contains the channel multiset theory. It defines `BalancedInteractions`, proves permutation and counting lemmas, and provides the channel-level implication principles used by higher-level soundness proofs. It also defines `RawChannel.Consistent` and `RawChannel.Normal`; typed channels are normal by construction, and normal channels are consistent under balance.

`FlatEnsemble.lean` defines flat AIR ensembles. A raw ensemble is structural: it has components, declared channels, and an optional verifier circuit. Its statement is the raw proof-system relation: there exists a witness whose table constraints hold and whose channel interactions are balanced. The ensemble file also defines `Air.Flat.EnsembleWitness`, verifier-table plumbing, and the generic `Soundness`, `SpecConsistency`, and `AssumptionsConsistency` predicates parameterized by external assumptions and specs. It also defines `FormalEnsemble`, which bundles a raw ensemble with external `Assumptions`, a `Spec`, and a proof that the raw statement implies the spec under those assumptions. Completeness belongs on `FormalEnsemble` as well; it is intentionally left as a commented-out field until the completeness theory is developed.

`FlatSoundChannels.lean` contains the staged channel-soundness construction for ordinary lookup-like channels. It defines partial balance, ordered channels, the `SoundChannels` invariant, and the induction that derives table specs and channel guarantees from constraints plus balanced interactions.

`FlatVm.lean` contains the VM-channel construction. VM components both pull from and push to one distinguished state channel, so their soundness is not the same as ordinary ordered lookup-channel soundness. This file packages VM components and the verifier, proves the special VM channel soundness theorem, and provides the constructor for adding a VM layer to an already sound flat ensemble.

## Relation To Clean/Table

`Clean/Table` is the older table infrastructure. Its `InductiveTable` interface models classic AIRs where a row transition may directly relate adjacent rows, by putting the output of one VM step in the same relative position as the input of the next step. `Clean.Air.Flat` instead models the modern one-row style: each component checks a single row in isolation, and all cross-row or cross-component structure is mediated by channels. The two layers are currently independent, but `Clean.Air` is intended to become the common home for AIR-style infrastructure, including future support for the older inductive table style now living under `Clean/Table`.
