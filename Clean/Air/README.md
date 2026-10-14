# Clean.Air

> :warning: This is partially LLM-written and subject to future human polish

`Clean.Air` contains the row-oriented proof-system layer that sits on top of the core circuit DSL. It is the home for AIR-like objects: components, trace tables, channel balance, ensembles, and formal end-to-end statements.

The first supported AIR style is **flat AIR**. In a flat AIR, one circuit is checked independently on each row of a table. The circuit does not directly refer to adjacent rows. All communication between rows and between components is expressed through channel interactions. This matches the modern layout where lookups, VM state transitions, and public API links are modeled by balanced channels rather than by next-row constraints.

In this terminology, a `Flat.Component` is a one-row AIR component: it packages the circuit whose constraints are applied to every row. A `Flat.Table` is the concrete trace table and prover data for such a component. A `Flat.Tables` value is a lightweight bundle of multiple concrete tables that share the same prover data object.

## Organization

`Circuit.lean` contains shared helpers for using `GeneralFormalCircuit`s as AIR components.

`FlatComponent.lean` defines the flat AIR component layer:

- `Flat.Component`: the static one-row component, backed by a `GeneralFormalCircuit`.
- `Flat.Table`: concrete array of rows for one component, together with the prover data used to evaluate constraints and channel interactions.
- `Flat.Tables`: a bundle of tables sharing one prover data object.

It also proves the basic row-level transport lemmas: instantiated component operations agree with row operations, component soundness lifts to table soundness, and table interactions can be collected per channel.

`Balance.lean` contains the channel multiset theory. It defines `BalancedInteractions`, proves permutation and counting lemmas, and provides the channel-level implication principles used by higher-level soundness proofs. It also defines `RawChannel.Consistent` and `RawChannel.Normal`; typed `Channel`s are normal by construction, and normal channels are consistent, so both properties are satisfied in practice. A highlight in `Balance.lean` is the "guarantees-to-requirements-reversal" theorem which provides the basis for soundness of VM channels. It is derived from a characteristic-free kernel: an `Event` is the payload, direction and activity of an interaction, `PullsSupported` and `CountBalanced` are support and count facts over natural numbers, and `guarantees_of_requirements_of_count_eq` is the reversal argument. `Interaction.legacyEvent` reads direction off the sign of the multiplicity.

`BalanceModel.lean` packages the relation a proof-system verifier establishes on one channel as a `BalanceModel`, together with a reading of interactions as events and the derivations of the kernel facts. `BalanceModel.logUp` is `BalancedInteractions` under the sign reading; `BalanceModel.multiset` is a permutation of active provided and received payloads under the directed reading `Interaction.directedEvent`, with no characteristic bound. A model only fits the channel encoding it reads: `RawChannel.ConsistentWith model` is the per-channel soundness obligation under a model, and `BalanceModel.Reads model Ch` ties each model to its typed channel constructor (`logUp` reads `Channel`, `multiset` reads `DirectedChannel`). The model-aware statements `Ensemble.StatementWith`, `SoundnessWith`, `CompletenessWith` and `FormalEnsembleWith` take the model explicitly, with no default; the legacy `Statement` is their LogUp instance by definition.

`OrderedChannelWith.lean` and `VmWith.lean` connect the models to ensemble soundness. The first restates the ordered-channel construction with the model as a parameter: `SoundEnsembleWith F model PublicIO` has builders that take typed channels through `BalanceModel.Reads` (`addChannel`, `addFinishedChannel`) or raw channels with a `RawChannel.ConsistentWith` instance (`addRawChannel`, `addFinishedRawChannel`). The second is the VM construction for a directed state channel under the multiset model: `DirectedVmTables`, `SoundVmEnsembleWith` and `SoundEnsembleWith.addVm`.

`FlatEnsemble.lean` defines flat AIR ensembles, `Flat.Ensemble` and their witnesses, `Flat.EnsembleWitness`. An ensemble has components, channels, and a verifier circuit. Its `Statement` is the raw proof-system relation: there exists a witness whose table constraints hold and whose channel interactions are balanced. The ensemble file also soundness and completeness and the `FormalEnsemble` structure which bundles an ensemble with its `Spec`, `Assumptions` and the soundness proof (completeness is TODO).

**Ensemble-level soundness** is more than a simple lifting of per-circuit soundness: it requires that channel guarantees, which were _assumed_ as part of local circuit proofs, are shown to hold unconditionally from global channel balance and constraints.

The library currently provides two distinct arguments to establish soundness, covering two prominent ways of using channels:

`OrderedChannels.lean` contains a staged channel construction for ordinary lookup-like channels. The defining property is a strict hierarchy on the list of component tables: any table that pushes to a channel must come before every table that pulls from it. From little more than this property, we prove ensemble-level soundness, as encapsulated in the `SoundEnsemble` structure. On the way, we introduce a relaxed notion of channel balance called `PartialBalancedChannels` that allows the balanced interaction list to contain additional interactions from tables added later. This makes it suitable for an inductive argument or gradual addition of tables to an existing sound ensemble.

`Vm.lean` contains a construction aimed at "VM-like" components that perform one transition per row. Since VM components both pull from and push to one distinguished state channel, they cannot follow the theory of ordered lookup-channel soundness. Instead, we prove a dedicated soundness theorem that applies to a set of VM components added to an existing hierarchical ensemble; a typical modern zkVMs layout.

## Channel contracts and the bus export protocol

Clean has two kinds of typed channel. They differ in how an interaction carries its direction,
in what a row must prove and may assume, and in the relation the verifier enforces on the bus.
Legacy channels are the default; directed channels are opt-in, for fields of characteristic two,
where `−1 = 1` (a signed multiplicity cannot tell a provide from a receive) and `1 + 1 = 0` (two
unmatched sends cancel).

### Legacy channels (`Channel`, `Clean/Circuit/Channel.lean`)

An interaction has a signed multiplicity `m` and a message. The sign is the direction: `−1` is a
receive, any other nonzero value a provide. For a channel with guarantee `G`, evaluated at a
row:

| operation | bus contribution | may assume `G msg`? | must prove locally |
| --- | --- | --- | --- |
| `push msg` | `+1` | no | `G msg` |
| `pull msg` | `−1` | yes | nothing |
| `emit m msg` | `m` | no | `G msg` if `m ∉ {0, −1}` |
| `emit 0 msg` | zero | no | nothing |

`emit (−1) msg` is a receive that assumes nothing and owes nothing; the `−1` exemption does not
extend to other negative weights. The verifier enforces the LogUp relation: for every message
the field sum of the multiplicities is `0`, and the channel's interaction list is shorter than
the characteristic (`BalancedInteractions`, `BalanceModel.logUp`). Only unit multiplicities give
a count of events.

### Directed channels (`DirectedChannel`, `Clean/Circuit/DirectedChannel.lean`)

An interaction has a direction, a gate and a message. The direction is stored as one extra raw
message element, the tag (`0` provide, `1` receive); the gate is the raw multiplicity and must
be `0` or `1`; one enabled interaction is one bus event. Permission to use the guarantee is
separate from the direction:

| operation | direction | may assume `G msg`? | must prove locally |
| --- | --- | --- | --- |
| `pushIf enabled msg` | provide | no | `enabled ∈ {0, 1}`, and `G msg` if `enabled ≠ 0` |
| `pullIf enabled msg` | receive | yes, if `enabled ≠ 0` | `enabled ∈ {0, 1}` |
| `emit .receive enabled msg` | receive | no | `enabled ∈ {0, 1}` |
| `emit .provide enabled msg` | provide | no | as `pushIf` |
| any, with `enabled = 0` | either | no | nothing beyond the gate |

`push`/`pull` are the `enabled = 1` cases. The verifier enforces the multiset relation: the
payloads of the active provides are a permutation of those of the active receives, with the tag
removed (`BalanceModel.multiset`), and there is no characteristic condition. A raw interaction
whose tag is neither value fails the channel's requirements, so no sound row produces one.

### Ensemble soundness, per kind

Lookup-style ensembles on either kind are built with `SoundEnsembleWith F model PublicIO`
(`OrderedChannelWith.lean`), which accepts only channels of the kind the model reads, and a VM
on a directed state channel with `VmWith.lean`; `SoundEnsemble` and `VmTables` remain for LogUp
ensembles. Either way, soundness assumes that every channel is balanced under the model, so it
holds of a deployed system only if the backend enforces that model's relation.

A worked directed VM is `Clean/Examples/FibonacciWithDirectedChannels.lean`: the Fibonacci VM
of `Clean/Examples/FibonacciWithChannels.lean` on a directed state channel, with an addition
lookup channel and a verifier that fixes the final index `N`. Its soundness theorem holds over
any field: the output is a Fibonacci pair `(fib k, fib (k + 1))` with `(k : F) = N`, so `N`
fixes the index only modulo the characteristic. Over `F 2` with `N = 1` the one-step and the
three-step run are both accepted, with different outputs; the output `(0, 0)` is rejected over
every field, since consecutive Fibonacci numbers are coprime; and the legacy relation admits no
witness of the ensemble, because its verifier alone puts two interactions on the state channel.

### The bus export protocol (`Clean/Air/BusProtocol.lean`)

The JSON of an interaction (`Clean/Circuit/Json.lean`) has the same shape for both kinds, with a
directed interaction's tag as the last message element, so it does not say which relation
applies. The bus export protocol, version 1, records the interpretation beside those bytes:

- a `ChannelSchema` per channel: its name, its raw arity, and its layout, `signed` (legacy: the
  message is the payload, the multiplicity a signed weight, relation `logup`) or `directed`
  (the payload followed by the tag at index `arity − 1`, a `0`/`1` gate, relation `multiset` on
  the tag-stripped payloads, a tag outside `{0, 1}` rejected);
- a `BusProtocol` per ensemble: the layout of its balance model and the channel schemas;
  `WellFormed` checks by `decide` that every channel has the layout the model reads.

Schemas come from the typed channels (`Channel.schema`, `DirectedChannel.schema`) and the
model's layout from `BalanceModel.Protocol`. Each clause of the directed layout is proved as a
fact about the encoding, so a backend implementing the schema enforces the relation the proofs
assume.

## Relation To Clean/Table

`Clean/Table` is the older table infrastructure. Its `InductiveTable` interface models classic AIRs where a row transition may directly relate adjacent rows, by putting the output of one VM step in the same relative position as the input of the next step. `Clean.Air.Flat` instead models the modern one-row style: each component checks a single row in isolation, and all cross-row or cross-component structure is mediated by channels. The two layers are currently independent, but `Clean.Air` is intended to become the common home for AIR-style infrastructure, including future support for the older inductive table style now living under `Clean/Table`.
