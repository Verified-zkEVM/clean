# Ordered resource histories

`Clean/Utils/ResourceHistory` proves the history theory that connects a distributed AIR implementation to an independently specified machine. Its complete semantic state can include all registers, memory, and host state without adding those objects to the circuit's physical rows.

## Why another VM theorem?

Clean's `VmTables` propagates a property along a distinguished state channel from the initial boundary to the final boundary. It deliberately permits additional disconnected cycles. This is sufficient for many endpoint properties, but does not establish every row's guarantees.

A VM can represent control state with only a clock and program counter, while registers and RAM use a separate channel. Reading RAM requires knowing what the most recent preceding access produced, and those accesses must occur in the same execution as the control transitions. The resource-history proof reconstructs that shared execution without changing the physical AIR representation.

Clean already has a mutable-memory theory in `OfflineMemory`. That theory starts from an ordered access log and zero memory. The new layer also proves where the log comes from and supports arbitrary authenticated initial and final frontiers.

## Follow a store and a read

Suppose address A initially contains zero. The physical memory ledger contains these records:

```text
initial provider                  store                     read                final consumer
   (A, 0, 0)  ──────────────▶  (A, 5, 7)  ──────────────▶  (A, 9, 7)  ──────────────▶
```

Each arrow consumes the previous record and produces its successor. A record contains `(key, version, value)`. The read advances the version and preserves the value. Versions track accesses, rather than only writes.

The proof has several distinct jobs:

| Layer | Established fact | Additional obligation |
|---|---|---|
| Row constraints | Local arithmetic, encodings, and interaction shape | Incoming operands may still be ungrounded |
| Exact ledger | Produced and consumed records match with multiplicity | Matching alone does not establish order |
| Control history | Every retained event belongs to the boundary execution | Resource access order must agree with it |
| Resource replay | Each access consumes the current record | Local instruction semantics must use those operands correctly |
| Event refinement | One step of the independent machine, with its frame | Authenticate the complete final boundary |

Why does ordering matter? A balanced ledger can contain `initial → final` and also `u → v → u`. An endpoint theorem can ignore that cycle, but its rows may contribute resource interactions. `exhaustive_of_acyclic` rules out such a residue. A strictly increasing decoded clock is one way to establish the required acyclicity. A machine's architectural state may repeat while its version metadata advances.

For a scheduled resource history, `walk_of_ordered_balance` derives the predecessor links. `replay_of_balance` then establishes the complete sequence of frontier updates. It does not assume that the claimed predecessors were correct. An aliased instruction can access the same key repeatedly; the later accesses consume the earlier accesses' successors.

`prefix_links` supports another useful proof order: establish the next event's resource prefix before ordering all remaining rows. It requires that the prefix's successor versions precede the remaining producers. Remaining consumers are unrestricted. Disjoint version windows for successive events can establish this separation.

## Interfaces and proof order

The mathematical files under `Clean/Utils/ResourceHistory` import only Mathlib, except for the explicitly named `OfflineMemory` compatibility module.

- `Walk` and `Ranked` provide trails, exhaustive ranked histories, and occurrence uniqueness.
- `Ordered` generalizes exhaustiveness to finite acyclicity and strict version orders. Its projection theorem removes certified identity transitions before ranking real events.
- `Replay` defines typed resource records, labeled accesses, optional frontiers, and sequential replay. It proves current-record matching, complete final-frontier equality, frames, and split/join at the same frontier.
- `Prefix` proves incremental predecessor links before the remaining events are ordered.
- `Inventory` derives per-key conservation from a complete global occurrence balance, explicit boundary coverage, and key-preserving local accesses.
- `Refresh` removes increasing, observation-preserving administrative accesses and retains a correspondence to every original non-refresh access. Include both key and value in its observation function; preserving a value alone would not preserve resource identity.
- `Grounding` combines one control walk and the resource replay of that **same occurrence list** with `EventRefinement`. The independent machine supplies its own trace constructors.

Establish encoding bounds before interpreting field comparisons as chronology. In particular, do not use memory currentness to prove the timestamp bounds needed to establish currentness. Structural producer facts and semantic value facts are separate proof obligations.

`ResourceReplay` works on arbitrary records and a key projection. The AIR adapter must prove that each transition preserves its key. `ResourceReplay.keys` then transports well-formed frontiers. `ResourceRecord` supports a key-indexed value family; no finite memory enumeration or uniform value encoding is required by the mathematical theory.

An absent frontier entry means the key does not participate. It is different from a record whose semantic value denotes an absent allocation. Allocation and deletion should transition authenticated absent/present values, keeping the conservation argument intact.

Observation equality justifies a refresh's ledger rewrite. The adapter must separately certify that the access is administrative. A same-value architectural write still carries write intent and its permission checks; it cannot be erased merely because its value is unchanged.

`EventRefinement.localStep` is a semantic proof boundary. Given authentic control and current resource records, it proves the machine step and representation of the resulting state. Its specification must include the full intended effects and frames. A precompile can own many physical rows; its adapter must establish exact ownership and the complete access footprint.

## Tests

The regression modules are included in `CleanTests`:

- `Clean.Utils.Test.ResourceHistory` exercises ordering, replay, cycle exclusion, and refreshes.
- `Clean.Utils.Test.ResourceGrounding` connects multiple accesses to an independent state machine.

To check these modules:

```sh
lake build --wfail Clean.Utils.Test.ResourceHistory Clean.Utils.Test.ResourceGrounding
```

## Provenance

The walk, ranked-history and refresh proofs were adapted from sp1-lean commit `9e383aaa85aec0eaf8ed0856f243ed8806520aef`.
