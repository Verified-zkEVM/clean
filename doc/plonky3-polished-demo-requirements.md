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

## Initial unblocked slice: `FibonacciWithChannels`

The first implementation target is the `fibonacciEnsemble` defined in
`Clean/Examples/FibonacciWithChannels.lean`. This slice establishes the reusable backend substrate
before addressing FemtoCairo's unresolved external-data semantics.

This is a meaningful backend target rather than a replacement toy example. It exercises:

- multiple same-row AIR components (`pushBytes`, `add8`, and `fib8`);
- a verifier/public-input circuit;
- static, lookup-like, and VM-state channels (`bytes`, `add8`, and `fibonacci`);
- conditional and non-constant interaction multiplicities;
- channel communication across rows and components; and
- an end-to-end formally proved Fibonacci statement.

None of these channel guarantees depends semantically on external `ProverData`. Therefore this
slice does not require a design for binding external program or memory data into the proof.

The Lean example proves ensemble soundness but does not currently define an executable
`EnsembleWitness` builder. The slice must therefore include an example-level Rust trace-input
driver. Given a requested step count, it must supply Fibonacci transition rows, corresponding
`add8` rows, balanced byte multiplicities, any valid disabled padding rows, and the claimed final
public state. Generated Witgen code then completes the local witness columns for those rows.

This trace-input driver is permitted to understand Fibonacci execution. It must use a generic
backend interface for component descriptions, row witness generation, channel topology, proving,
and verification; that topology must not be reassembled in a Fibonacci-specific backend adapter.
The chosen trace heights and padding policy are statement metadata and must be enforced by the
verifier.

All otherwise applicable backend requirements in this document apply to the initial slice. In
particular, it must use generated direct Rust constraints, generated Rust witness code, generic
multi-component channel support, public inputs, verifier-bound trace metadata, documentation, and
CI. It must not reach the goal by extending legacy `Clean/Table`, using the existing FemtoCairo
adapter, interpreting the constraint AST in the proving hot path, or invoking Lean for witness
generation at proving time.

Support for witness operations or channel semantics that read external `ProverData` may be
rejected explicitly by the initial exporter. Such operations must not be silently ignored or
given a weaker backend meaning.

Completing this slice deliberately defers, but does not resolve or remove, the requirements for
sound external-data binding and the FemtoCairo demo. Those remain release blockers for the final
grant milestone.

### Initial-slice acceptance criteria

The `FibonacciWithChannels` slice is complete when all of the following hold:

1. A documented Clean command generates a reproducible Rust artifact from `fibonacciEnsemble`.
2. The generated backend represents all ensemble components and the `bytes`, `add8`, and
   `fibonacci` channels without example-specific Rust topology.
3. Generated direct Rust code evaluates component constraints and interactions; the runtime JSON
   constraint interpreter is not used.
4. A Rust trace-input driver plus generated Rust witness code constructs every component trace
   without invoking Lean at proving time; the boundary between supplied row inputs and generated
   local witnesses is documented.
5. The prover and verifier accept the public Fibonacci input explicitly and establish the
   Clean-level statement represented by `fibonacci_soundness`.
6. Plonky3 channel arguments enforce balance across all participating rows and components,
   including conditional multiplicities and the public-input verifier interaction.
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

The polished demo must support public inputs end to end. Public values must be represented in the
generated Rust AIR, included in the proof statement/transcript as required by Plonky3, and checked
by the verifier.

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
