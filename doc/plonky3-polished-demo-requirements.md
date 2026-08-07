# Plonky3 Backend and FemtoCairo Demo Requirements

## Status

This document records requirements and architectural decisions for the final Clean grant
milestone. It intentionally does not prescribe a detailed implementation plan. Open design
questions are collected separately so that implementation choices do not silently become
requirements.

## Objective

Deliver a polished end-to-end demonstration in which a realistically sized FemtoCairo program
defined in Clean is compiled to an efficient Rust/Plonky3 prover, proved, and verified.

The demonstration must preserve the soundness meaning of the Clean definition. Performance or
integration convenience must not be obtained by weakening the proved relation.

The work should also leave behind a reusable Plonky3 backend rather than an integration whose
architecture or data formats are specific to FemtoCairo.

## Delivery milestone 1: generic ensemble witness generation

Before changing the Plonky3 backend, Clean must gain a generic, executable way to construct an
`Air.Flat.EnsembleWitness` for an arbitrary ensemble. This facility is a Clean/AIR and witness-IR
feature, not a Plonky3 or Fibonacci feature, and must be testable with the Lean reference evaluator
in isolation.

Ensemble witness generation is driven automatically by channel imbalance. The verifier circuit's
interactions are evaluated from the public input and seed a deterministic worklist; the verifier
does not produce a component table.
Opposite interactions carrying the same channel message cancel. Any remaining interaction is
routed to the component registered to handle that channel and polarity; materializing or updating
that row may produce more interactions. Generation terminates when the worklist is balanced.

Components must explicitly declare how channel demand materializes their rows. The initial
surface has three modes:

- **push-driven**: an unmatched push creates one component row per occurrence;
- **pull-driven chip**: unmatched pulls create one row per distinct message, and repeated pulls
  increment that row's multiplicity; and
- **fixed**: rows exist up front, and matching demand updates declared multiplicity slots.

These modes may share one implementation parameterized by trigger polarity, allocation policy,
and aggregation policy. The declarations must also specify how a trigger message and multiplicity
map to component input cells. The builder must not attempt to infer allocation, deduplication,
termination, or padding policy from circuit expressions.

Each component also declares a semantic padding input and minimum height. The builder completes
that input with the component's ordinary witness program, adds enough rows to reach a power-of-two
height, and balances any interactions produced by those rows. If balancing grows another table,
padding and balancing repeat. There is no backend-only active-row selector or constraint gating:
every committed row is a valid Clean row and participates in its declared interactions.

The generic builder derives component order and widths from the `Ensemble`, runs each component's
existing row-local Witgen IR to complete rows, evaluates row and verifier interactions, and
assembles the `EnsembleWitness`. It must not know Fibonacci component names, channel names, or
schedules.

When an existing row is updated—for example, when a chip multiplicity increases—the builder must
replace that row's previous contribution to channel imbalance with its new contribution. It must
not enqueue unchanged nested interactions again.

For `FibonacciWithChannels`, the verifier's initial-state push drives `fib8` rows until a generated
final-state push cancels the verifier's final pull. The `add8` pulls produced inside those rows
drive multiplicity-coalesced `add8` rows. Their byte pulls update the fixed byte row's
multiplicities. This behavior is obtained from generic modes and component declarations, not from
a bespoke Fibonacci trace algorithm.

The generation declarations and worklist operations must be structured, exportable witness IR.
The existing `WitgenIR F m` is row-local and fixed-output-size, so the implementation may extend it
or compose it with an ensemble-level IR. In either case, the exportable representation must cover
multi-table allocation, deterministic worklist iteration, row updates, and accumulator/scan
computations without embedding native Lean closures.

The same IR must be the source for generated Rust witness code. Rust generation is
backend-independent: it produces component traces and public inputs, not Plonky3 constraints or
proofs. The generated Rust implementation must agree with the Lean reference evaluator and must
not interpret witness JSON in the proving hot path.

This milestone does not require a formal completeness proof for the ensemble witness generator.
In particular, it need not prove for all valid inputs that the generated tables satisfy every
constraint and balance every channel. Structural properties needed to construct an
`EnsembleWitness`—component identity and ordering, row widths, shared data, and public input—must
still hold by construction or be validated with explicit errors.

An incorrect generator can prevent an honest proof from being produced, but it must not weaken
the constraints or channel relation checked by the proof system. Lean tests must execute concrete
generated witnesses and check their constraints and channel balance even though the general
completeness theorem is deferred.

External `ProverData` semantics are outside this first milestone. The initial implementation may
support only generators and component witness programs that do not read external data, and must
reject unsupported data-dependent programs rather than ignore them.

### Ensemble-witness milestone acceptance criteria

1. A generic Lean API associates explicit row-generation modes with components of an arbitrary
   `Air.Flat.Ensemble`, without example-specific logic in the builder.
2. Given generator inputs, the Lean evaluator returns a structurally valid `EnsembleWitness` or an
   actionable validation error.
3. The builder automatically invokes each component's existing row-local Witgen IR; ensemble
   authors do not duplicate local witness computations.
4. The worklist eagerly cancels opposite equal messages and supports push-driven per-occurrence,
   pull-driven message-coalesced, and fixed-row multiplicity-updating generation.
5. Updating a row changes the global channel imbalance by the delta between its old and new
   interactions, so unchanged nested pulls or pushes are not counted twice.
6. Missing or ambiguous handlers, malformed row inputs, non-termination/fuel exhaustion,
   multiplicity overflow, and malformed padding declarations are reported as explicit errors.
7. The structured IR can express multiple component tables, deterministic worklist/scan state,
   verifier interactions, and semantic trace padding needed by `FibonacciWithChannels`.
8. All code reachable through the export path is structured IR; native witness closures are
   rejected with their locations.
9. Fibonacci generation declarations produce a non-trivial witness in Lean whose component
   constraints and `bytes`, `add8`, and `fibonacci` channel balances pass executable checks.
10. Backend-independent Rust code is generated from the same witness IR and differentially tested
   against Lean on the Fibonacci witness, including trace contents and public inputs.
11. The interface and trusted status are documented: the generator is not completeness-proved and
   generated witness correctness is not part of the soundness argument.

## Delivery milestone 2: Plonky3 support for `FibonacciWithChannels`

The first backend target is the `fibonacciEnsemble` defined in
`Clean/Examples/FibonacciVm/Circuit.lean`. It exercises multiple same-row AIR components, a
verifier/public-input circuit, conditional multiplicities, and the static, lookup-like, and
VM-state `bytes`, `add8`, and `fibonacci` channels.

None of these channel guarantees depends semantically on external `ProverData`. Therefore this
slice establishes the reusable backend substrate before addressing FemtoCairo's unresolved
external-data semantics.

All otherwise applicable backend requirements in this document apply. In particular, this slice
must use generated direct Rust constraints, the generated ensemble witness code from milestone 1,
generic multi-component channel support, public inputs, verifier-bound trace metadata,
documentation, and CI. It must not extend legacy `Clean/Table`, use the existing FemtoCairo
adapter, interpret constraint JSON in the proving hot path, or invoke Lean during Rust proving.

Completing this slice deliberately defers, but does not resolve or remove, the requirements for
sound external-data binding and the FemtoCairo demo. Those remain release blockers for the final
grant milestone.

### Fibonacci backend acceptance criteria

1. A documented Clean command generates a reproducible Rust artifact from `fibonacciEnsemble`.
2. The generated backend represents all ensemble components and the `bytes`, `add8`, and
   `fibonacci` channels without example-specific Rust topology.
3. Generated direct Rust code evaluates component constraints and interactions; the runtime JSON
   constraint interpreter is not used.
4. The generated ensemble witness code constructs every component trace without invoking Lean at
   proving time.
5. The prover and verifier accept the public Fibonacci input explicitly and establish the
   Clean-level statement represented by `fibonacci_soundness`.
6. Plonky3 channel arguments enforce balance across all participating rows and components,
   including conditional multiplicities and public-input verifier interactions supplied directly
   to the argument without a synthetic verifier trace.
7. A valid proof generated with a verifier-unexpected static trace height is rejected.
8. Negative tests reject altered public values, unbalanced or malformed channel traces, and
   invalid component witnesses.
9. A non-trivial parameterized Fibonacci run reports witness-generation, proving, and verification
   time together with trace dimensions and proof size.
10. The maintained generation, build, proof, and verification workflow runs in CI.

## Recorded decisions

### Soundness correspondence is a release blocker

The proof-system relation implemented by the backend must imply the relation stated and proved in
Clean. A known semantic weakening is a blocker for the polished demo, even if honest witness
generation happens to produce valid traces.

In particular, the current FemtoCairo bridge interprets a dynamic memory table as an unordered
relation of `(address, value)` tuples. Clean's `MemoryTable.Contains` instead requires the entry for
address `i` to agree with row `i` of the external memory data. Tuple membership is strictly weaker:
a permuted table can satisfy the backend lookup while violating the Clean predicate. The polished
demo must not ship with this mismatch or an equivalent weakening.

### Channels are the target abstraction

New backend and FemtoCairo integration work must use channel-based relations rather than invest
further in the legacy `Clean/Table` abstraction.

The work stream explicitly aims to retire `Clean/Table`. Existing users may need to be ported in
stages, but the final architecture must not depend on adding new backend-specific features to
`Table`, `TableOperation`, or arbitrary `Table.Contains` predicates.

### External prover data must have proof-system semantics

Channel-based FemtoCairo reasoning needs a sound way to represent external `ProverData`, including
program and memory data. It is insufficient for this data to exist only as an uncommitted host
runtime object used by honest witness generation.

The eventual design must relate the external data used in Clean propositions and channel
guarantees to data committed or otherwise bound by the proof. From the verifier's perspective,
the same data must govern:

- witness-generation reads;
- component constraints and channel messages;
- channel guarantees and requirements;
- the final Clean-level specification.

The exact representation is still an open design question.

### Verifier-known trace shape must be bound

Verifier-known static trace heights and other static shape metadata must not be accepted from the
proof without validation.

The issue identified by GitHub PR #419 is part of this work. Its regression coverage must use a
fully valid proof generated at an unexpected height. Merely mutating `degree_bits` on an existing
proof is not sufficient, because the current verifier already rejects that mutation when checking
the cryptographic opening.

### Public inputs are required

The polished demo must support public inputs end to end. Public values must be included in the
proof statement/transcript as required by Plonky3, drive the verifier-side channel interactions,
and be checked by the verifier.

The main demonstrated claim must not be expressed solely through constants hard-coded into a
generated circuit artifact.

### The full pipeline must exercise realistic scale

The polished demo must execute a realistically sized FemtoCairo program through export, Rust
witness generation, proving, and verification. Tiny traces that primarily measure Lean or process
startup time are not sufficient evidence.

The demo must report proving time. Additional measurements should include witness-generation time,
verification time, trace dimensions, proof size, and generated-code/build costs where practical.

The concrete workload and minimum scale remain to be selected.

### Documentation and CI are deliverables

The supported end-to-end workflow must be documented accurately and run in CI. Documentation and
CI commands must use the maintained public interface rather than test-only FemtoCairo adapters or
stale file/test names.

## Functional requirements

### Direct Rust constraint generation

- Clean constraints must be emitted as direct Rust `Air`/constraint-builder code.
- The prover hot path must not recursively interpret a JSON constraint AST.
- Unsupported Clean operations must be rejected during export or compilation with actionable
  diagnostics, rather than failing through a runtime panic during proving.
- Generated code must preserve boundary, row-scope, component, and channel semantics used by the
  Clean definition.

JSON may remain as an optional diagnostic or build-time manifest, but it must not be the runtime
constraint evaluator.

### Rust witness generation

- Witness-generation IR must be compiled to Rust.
- Proving the exported demo must not launch Lean to construct the execution trace.
- Rust evaluation must implement the specified field, wrapping `u64`, condition, data-read,
  hint-read, local-step, and vector/loop semantics of the exported witness IR.
- The generated witness implementation must be tested differentially against the Lean reference
  interpreter on representative circuits and the FemtoCairo workload.

### Channel and component support

- The backend must support multiple ordinary AIR components, not one distinguished main AIR plus
  FemtoCairo-specific table types.
- Clean channel identity, arity, message expressions, multiplicities, and balance must be preserved
  by the Plonky3 lookup/interaction implementation.
- The verifier must bind the set and ordering of components and channels used by the compiled
  statement.
- The backend-facing artifact and runtime API must not contain hard-coded `program` or `memory`
  names or assume exactly those two relations.

### External data support

- External prover data used by a component must have an explicit schema.
- The proof must bind the semantically relevant data or a commitment/trace representation from
  which the required Clean data can be reconstructed.
- Channel-provider constraints must establish the guarantees consumers use in their soundness
  proofs.
- Honest witness-generation access to external data must agree with the data represented in the
  proof.
- Malformed, permuted, substituted, or inconsistently interpreted data must not be accepted when
  it violates the Clean-level relation.

### Public input support

- The exported artifact must describe the public-input layout.
- Generated AIR code must read public values without FemtoCairo-specific glue.
- Proving and verification APIs must accept public values explicitly.
- Changing a claimed public value without regenerating a valid proof must cause verification to
  fail.
- The end-to-end FemtoCairo specification must relate its result to public input or output values.

### Verifier metadata

- Static trace heights must be verifier-known and checked against proof degree metadata.
- Dynamic trace heights, if supported, must have explicit verifier-enforced policies and bounds.
- Component widths, channel layout, preprocessed data, public-input layout, field/configuration, and
  other statement-defining metadata must be bound by the verifier interface.
- Shape validation must return structured errors where practical instead of panicking.

### Reusable integration

- At least one non-FemtoCairo example must exercise the same exported backend interface in CI.
- FemtoCairo-specific code may supply a program and private data, but it must not assemble the
  backend's component topology or proof protocol manually.
- Generated artifacts must have a reproducible build command suitable for local use and CI.

## Soundness and assurance requirements

- The backend's implemented algebraic constraints and channel relations must correspond to the
  operations exported by Clean.
- No operation carrying soundness meaning may be silently ignored. This includes constraints,
  interactions, public values, and relevant external-data bindings.
- The trusted boundary between Lean, generated Rust, Plonky3, and any code generator must be
  documented.
- Translation and witness-generation tests must include negative/adversarial cases, not only honest
  end-to-end proofs.
- A wrong Rust witness generator may remain a completeness failure, but it must not be able to
  compensate for missing or weakened constraints.

Whether the Lean-to-Rust translation itself must be formally verified is an open question. Until
then, the generator is part of the trusted computing base and requires small, auditable lowering
rules plus differential and negative testing.

## Performance and demonstration requirements

- The maintained demo command must run the complete generated Rust pipeline in release mode.
- Timings must distinguish at least witness generation, proof generation, and verification.
- The report must state trace height, component widths, and the number/type of components and
  channels.
- Results must not include Lean trace generation in the measured Rust proving time.
- The chosen program must exercise meaningful FemtoCairo behavior rather than repeated trivial
  immediate operations. The exact instruction mix is still open.
- Any claim that generated constraints are faster than runtime interpretation must be supported by
  a reproducible comparison on a representative workload.

## Documentation and CI requirements

- A top-level or backend README must explain prerequisites, generation, building, proving,
  verification, public inputs, and expected outputs.
- Documentation must explain the soundness statement demonstrated and the treatment of external
  prover data.
- CI must build generated Rust artifacts from the Clean source and run an end-to-end proof and
  verification.
- CI must include focused negative tests for semantic mismatches and verifier metadata.
- Maintained commands in documentation and CI must match.
- The full Rust unit/integration test suite and lint policy should be explicit.

## Retirement requirements for `Clean/Table`

- No new backend feature should depend on extending legacy `Table` semantics.
- Existing examples and gadgets that still depend on `Clean/Table` must be inventoried.
- Required users must be ported to the channel/component model before the legacy code is removed.
- The meaning of "retired"—deprecated, no longer imported by maintained examples, or physically
  removed from the repository—must be decided before declaring this work stream complete.
- Migration must preserve existing formal statements or document intentional specification
  changes.

## Acceptance criteria

The polished milestone is acceptable only when all of the following hold:

1. A documented Clean command generates the maintained Rust artifacts.
2. Rust constructs the FemtoCairo witness without invoking Lean.
3. Generated direct Rust code evaluates the Clean constraints; no runtime constraint JSON
   interpreter is used.
4. The proof binds and verifies meaningful public input/output.
5. External program/memory data used by FemtoCairo is soundly related to proof-committed data and
   channel guarantees.
6. The known unordered-tuple weakening of `MemoryTable.Contains` is absent; an adversarial test
   demonstrates that the former mismatch cannot be exploited.
7. A valid proof produced at a verifier-unexpected static height is rejected.
8. A realistically sized FemtoCairo workload proves and verifies, with reproducible proving-time
   measurements.
9. A non-FemtoCairo example uses the same backend interface.
10. The maintained workflow is documented and runs in CI.
11. The remaining trusted boundary and any explicitly unsupported features are documented.
12. No known semantic weakening relative to the claimed Clean specification remains open.

## Open design questions

- How should proof-committed data realize `ProverData` used in Clean specifications and channel
  guarantees?
- Should the new model bind an external-data object to component traces, or should components and
  channels replace semantic uses of `ProverData` entirely?
- What extensions to `Clean/Air` are required to express this relation and prove ensemble
  soundness?
- What public-input/output statement should the FemtoCairo demo prove?
- Which trace heights are static, dynamic, or public, and what bounds apply to dynamic heights?
- What is the minimum realistic FemtoCairo workload, and which instructions and memory behaviors
  must it exercise?
- Which non-FemtoCairo example best demonstrates backend generality?
- Which fields and Plonky3 configurations must the first polished version support?
- What is the generated Rust artifact layout and build integration?
- How much of the Lean-to-Rust lowering should be formally verified versus covered by an explicit
  trusted boundary and differential tests?
- What exact migration threshold permits deprecating and then removing `Clean/Table`?

## Known current-state issues to preserve as regression targets

- Dynamic FemtoCairo memory is weakened from indexed-array semantics to unordered tuple
  membership.
- A valid proof at an unexpected main trace height is accepted by the current verifier.
- Public-input support is not connected to Clean's exported expression format.
- Constraints are interpreted from JSON in the Rust AIR implementation.
- FemtoCairo witnesses and traces are generated by executing Lean during Rust tests.
- The current FemtoCairo artifact and adapter hard-code program and memory table structure.
- Current examples are too small to demonstrate realistic proving throughput.
- Backend documentation and CI cover stale or partial commands rather than one maintained full
  workflow.
