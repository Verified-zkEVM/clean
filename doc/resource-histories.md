# Ordered resource histories

`Clean.Air.ResourceHistory` connects a distributed AIR implementation to an independently
specified machine. Its complete semantic state can include all registers, memory, and host
state without adding those objects to the circuit's physical rows.

## Why another VM theorem?

Clean's `VmTables` propagates a property along a distinguished state channel from the initial
boundary to the final boundary. It deliberately permits additional disconnected cycles. This
is sufficient for many endpoint properties, but does not establish every row's guarantees.

A VM can represent control state with only a clock and program counter, while registers and
RAM use a separate channel. Reading RAM requires knowing what the most recent preceding
access produced, and those accesses must occur in the same execution as the control
transitions. The resource-history proof reconstructs that shared execution without changing
the physical AIR representation.

Clean already has a mutable-memory theory in `OfflineMemory`. That theory starts from an
ordered access log and zero memory. The new layer also proves where the log comes from and
supports arbitrary authenticated initial and final frontiers.

## Follow a store and a read

Suppose address A initially contains zero. The physical memory ledger contains these records:

```text
initial provider                  store                     read                final consumer
   (A, 0, 0)  ──────────────▶  (A, 5, 7)  ──────────────▶  (A, 9, 7)  ──────────────▶
```

Each arrow consumes the previous record and produces its successor. A record contains
`(key, version, value)`. The read advances the version and preserves the value. Versions track
accesses, rather than only writes.

The proof has several distinct jobs:

| Layer | Established fact | Additional obligation |
|---|---|---|
| Row constraints | Local arithmetic, encodings, and interaction shape | Incoming operands may still be ungrounded |
| Exact ledger | Produced and consumed records match with multiplicity | Matching alone does not establish order |
| Control history | Every retained event belongs to the boundary execution | Resource access order must agree with it |
| Resource replay | Each access consumes the current record | Local instruction semantics must use those operands correctly |
| Event refinement | One step of the independent machine, with its frame | Authenticate the complete final boundary |
| Realization | Raw acceptance is equivalent to an admissible semantic trace | Cryptographic proof-system extraction is separate |

Why does ordering matter? A balanced ledger can contain `initial → final` and also `u → v → u`.
An endpoint theorem can ignore that cycle, but its rows may contribute resource interactions.
`exhaustive_of_acyclic` rules out such a residue. A strictly increasing decoded clock is one
way to establish the required acyclicity. A machine's architectural state may repeat while its
version metadata advances.

For a scheduled resource history, `walk_of_ordered_balance` derives the predecessor links.
`replay_of_balance` then establishes the complete sequence of frontier updates. It does not
assume that the claimed predecessors were correct. An aliased instruction can access the same
key repeatedly; the later accesses consume the earlier accesses' successors.

`prefix_links` supports another useful proof order: establish the next event's resource
prefix before ordering all remaining rows. It requires that the prefix's successor versions
precede the remaining producers. Remaining consumers are unrestricted. Disjoint version
windows for successive events can establish this separation.

## Interfaces and proof order

The mathematical files under `Clean/Utils/ResourceHistory` import only Mathlib, except for
the explicitly named `OfflineMemory` compatibility module.

- `Walk` and `Ranked` provide trails, exhaustive ranked histories, and occurrence uniqueness.
- `Ordered` generalizes exhaustiveness to finite acyclicity and strict version orders. Its
  projection theorem removes certified identity transitions before ranking real events.
- `Replay` defines typed resource records, labeled accesses, optional frontiers, and sequential
  replay. It proves current-record matching, complete final-frontier equality, frames, and
  split/join at the same frontier.
- `Prefix` proves incremental predecessor links before the remaining events are ordered.
- `Inventory` derives per-key conservation from a complete global occurrence balance,
  explicit boundary coverage, and key-preserving local accesses.
- `Refresh` removes increasing, observation-preserving administrative accesses and retains a
  correspondence to every original non-refresh access. Include both key and value in its
  observation function; preserving a value alone would not preserve resource identity.
- `Grounding` combines one control walk and the resource replay of that **same occurrence
  list** with `EventRefinement`. The independent machine supplies its own trace constructors.

The AIR adapters preserve the actual witness:

- `LedgerView` describes all evaluated slots, including disabled ones. It supports explicit
  direction and activity, physical table/row identities, and gated lists of transitions.
- `TransitionView` and `ReceiverView` provide simpler interfaces for fixed unit interactions.
- `UnitBalance` converts signed field balance to typed occurrence permutations.
- `Authentication` and `ChannelClosure` discharge received properties from proved producers.
- `MessageFilter` selects complete message classes. Arbitrarily deleting tables does not
  preserve balance.
- `Footprint` relates literal ledger lengths to physical heights and interaction widths.

Establish encoding bounds before interpreting field comparisons as chronology. In particular,
do not use memory currentness to prove the timestamp bounds needed to establish currentness.
Structural producer facts and semantic value facts are separate proof obligations.

`ResourceReplay` works on arbitrary records and a key projection. The AIR adapter must prove
that each transition preserves its key. `ResourceReplay.keys` then transports well-formed
frontiers. `ResourceRecord` supports a key-indexed value family; no finite memory enumeration
or uniform value encoding is required by the mathematical theory.

An absent frontier entry means the key does not participate. It is different from a record
whose semantic value denotes an absent allocation. Allocation and deletion should transition
authenticated absent/present values, keeping the conservation argument intact.

Observation equality justifies a refresh's ledger rewrite. The adapter must separately certify
that the access is administrative. A same-value architectural write still carries write intent
and its permission checks; it cannot be erased merely because its value is unchanged.

`EventRefinement.localStep` is a semantic proof boundary. Given authentic control and current
resource records, it proves the machine step and representation of the resulting state. Its
specification must include the full intended effects and frames. A precompile can own many
physical rows; its adapter must establish exact ownership and the complete access footprint.

## Boundaries, completeness, and composition

`CompleteEnsemble` adds completeness without changing `FormalEnsemble`. `EnsembleCompiler`
accepts execution data, checks it, and returns an optional AIR witness. Its completeness field
proves success for every execution in an independently defined domain. Compiler success cannot
define that domain. A Lean function may be noncomputable; executable compiler instances must
be checked separately.

The semantic state and the compiler's input format are separate choices. `EnsembleCompiler`
can consume finite snapshot or trace data interpreted by a representation relation. Such an
instance must prove that its encoding covers the intended admissible executions. The explicit
`ExecutionData` bundle used by `TraceRealizes` is convenient when semantic endpoints are
available as data; it does not require the AIR to materialize those endpoints in every row.

`TraceRealizes` takes the existing semantic trace relation, boundary authentication relation, and
admissibility predicate. Its public theorem is:

```text
ensemble.Statement(public)
  ↔ ∃ initial, events, final,
      (∃ opening, Boundary(public, initial, final, opening))
      ∧ Trace(initial, events, final)
      ∧ Admissible(public, initial, events, final)
```

`snapshotBoundary` specializes this to complete endpoints decoded from public input.
Complete state includes untouched memory and the relevant host state. The statement permits
empty and non-halting shards when the supplied semantics and profile permit them.

A commitment-backed instance must prove the corresponding authentication relation. Composing
traces requires the same actual state at the cut. Equality of digests establishes that only
with the appropriate binding argument. The library does not assert cryptographic binding or
extract executions from proof bytes.

Capacity is physical: zero-multiplicity slots, duplicate messages, padding, providers, and
refreshes all count toward Clean's current characteristic bound. A semantic resource profile
must be enforced by the AIR, and its compiler must prove the complete expansion fits. A bound
on instruction count alone does not bound host memory work.

An external semantics library can supply the trace relation directly. Its execution model
does not need to depend on Clean's circuit representation.

## Extension contracts

| Extension | Adapter obligation |
|---|---|
| Memory protection | Authenticate permission resources at each access; check actual written bytes and write intent, including same-value writes |
| Dynamic permissions | Order permission changes and memory accesses in the shared event sequence |
| Precompiles | Bind invocation and result, prove the mathematical operation, and account for every resource effect across all rows |
| External calls | Thread the host state and authenticate requests, replies, resource effects, and completion status |
| Alternative layouts | Prove an exact ledger/history adapter or another proof of the same resource replay relation |

Each implementation supplies the corresponding circuit refinements, boundary authentication,
and witness constructors.

## Tests

The regression modules are included in `CleanTests`:

- `Clean.Utils.Test.ResourceHistory` exercises ordering, replay, cycle exclusion, and refreshes.
- `Clean.Utils.Test.ResourceGrounding` connects multiple accesses to an independent state machine.
- `Clean.Utils.Test.ResourceRealization` checks empty executions, compilation, and physical
  occurrence identities.

To check these modules:

```sh
lake build --wfail Clean.Utils.Test.ResourceHistory Clean.Utils.Test.ResourceGrounding Clean.Utils.Test.ResourceRealization
```

## Provenance

The walk, ranked-history, refresh, and several AIR adapter proofs were adapted from sp1-lean
commit `9e383aaa85aec0eaf8ed0856f243ed8806520aef`.
