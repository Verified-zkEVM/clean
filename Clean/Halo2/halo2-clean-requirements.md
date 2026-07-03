# Halo2-Clean: Requirements

This document defines the requirements for the second phase of the Zcash circuit
formalization: a halo2-native circuit framework in Lean ("Halo2-Clean"), and the port of
the ironwood action circuit to it.

## Starting Point

Phase one ([orchard-clean-plan](../Orchard/orchard-clean-plan.md), PRs #402/#409) ported
the entire Orchard action circuit to Clean in an "approximate" form: source-conformant
gadget structure, semantic specs, full soundness/completeness proofs — but Clean's linear
witness tape cannot represent halo2's cell layout (columns, rows, rotations, selectors,
copy constraints), so nothing ties those circuits to the constraint system behind the
real verification key.

This phase closes that gap. We deliberately do **not** generalize Clean's core (variable
indices, operation set); instead we build a parallel, halo2-shaped framework from the
ground up. Unifying the two frameworks is deferred until after the Zcash work ships.

## Goal

1. A framework for writing halo2 circuits in Lean idiomatically — at least the
   circuit-writing convenience level of the Rust halo2 API — with formal proofs of
   soundness and completeness against trace-level semantics.
2. The ironwood action circuit (Orchard + cross-address checks) written in that
   framework, with specs and proofs ported from the phase-one Orchard work.
3. The framework is designed and looks **exactly like Clean**. It replaces only the
   parts of Clean that are incompatible with halo2 and is otherwise the same, so that it
   can be consolidated with main Clean later on.
4. The two open seams in [zcash/ironwood](https://github.com/zcash/ironwood) discharged:
   - **VK-correctness** (`Zcash/Snark/Verifier/Assemble.lean`): re-derive the
     `VerifyingKey` constraint-system data from the circuit definition in Lean and prove
     it equal to the captured fixture (`Zcash/Snark/Fingerprint/Fixture.lean`).
   - **Semantic adequacy** (`Zcash/Snark/Soundness/Main.lean`): prove that
     circuit-satisfaction implies the high-level action spec, filling the assumed
     `hencodes`/`S` hypothesis.

Timeline: ships before the Zcash network upgrade (early August 2026).

## Where Code Lives

- The framework starts as a branch of `clean` (`Clean/Halo2/`), moving to Lean/Mathlib
  4.30 immediately so ironwood can import it ASAP.
- The zcash circuit work itself (the phase-two equivalent of `Clean/Orchard/`) is
  destined for the **ironwood repo**, importing clean for the framework. Until the 4.30
  move lands, ironwood types may be temporarily vendored here.

## Reference Sources

Local clones in `/mnt/data-2tb/zks/`:

- **orchard**: branch `feat/ironwood` (`0.15.0-pre.1`; `ebfull/ironwood` is the working
  branch it derives from). The ironwood circuit = Orchard action circuit +
  `synthesize_cross_address_checks` (`src/circuit.rs`); 99% is exactly Orchard.
- **halo2**: tag `halo2_gadgets-0.5.0` (orchard's `feat/ironwood` depends on crates.io
  `halo2_gadgets 0.5` / `halo2_proofs 0.3`, same as phase one).
- **ironwood**: main. Verifier-side formalization; defines the types we must converge
  with (`VerifyingKey`, `Expr`, `circuitSatViaGates`, `DeployedAccepts`).

The hard reference rule from phase one carries over: every definition is ported from the
actual Rust source, never inferred from memory or protocol descriptions.

## Framework Requirements

Informed by a survey of the halo2 `Region` API, halo2_gadgets, and orchard's circuit
code, plus the (in-flux) ironwood Lean interfaces.

### Clean-shaped, consolidation-ready

The guiding design rule: **every deviation from main Clean must be justified by a halo2
incompatibility; everything else is copied from Clean verbatim.** Same core concepts,
names, file organization, and proof experience: a `Circuit` monad, `ProvableType`/
`ProvableStruct`, `FormalCircuit`/`FormalAssertion`/`GeneralFormalCircuit` with
`Assumptions`/`Spec`/`soundness`/`completeness`, `ElaboratedCircuit`, the subcircuit
mechanism as the proof boundary, witgen IR for witness values, `circuit_norm`/
`circuit_proof_start` as the automation entry points. The expected deviations are
confined to: variables are cells rather than tape indices (with region-relative
addressing replacing the linear offset), the operation set is halo2's (assign, copy,
selector enable, region) rather than witness/assert, and the compiled artifact is a
constraint system + layout rather than a flat operation list. This keeps a later
consolidation with main Clean tractable and is a hard requirement, not a preference.

Where code can actually be shared, it is **shared, not copied** — the witgen IR is the
expected first case; candidates include `ProvableType` machinery and generic utilities.
Reorganizing Clean core code is permitted where it facilitates sharing (e.g. splitting a
file so the reusable part has no dependency on Clean's tape-indexed layer).

### Two-layer DSL, mirroring halo2

1. **Configure layer**: define custom gates and lookups as expressions over
   (column, rotation) queries, with **first-class selectors**. Gate-authoring AST matches
   halo2's `Expression` node set (constant, selector, fixed/advice/instance query,
   negated, sum, product, scaled) so that dumped ASTs can match syntactically.
   Chip `configure` functions are ported verbatim from Rust.
2. **Synthesize layer**: monadic region DSL mirroring the halo2 `Region` API surface:
   `assignAdvice`, `assignAdviceFromConstant`, `assignAdviceFromInstance`, `assignFixed`,
   `copyAdvice`, `constrainEqual`, `constrainConstant`, selector `enable`;
   `assignRegion` as the composition unit.

### Composition currency: cell references

The Rust survey settled this: halo2's synthesize API has no expression inputs
(`Expression` exists only in configure), and every gadget-level abstraction is
cell-backed (`Var` requires `cell()`; `EccPoint`, `MessagePiece`, `RunningSum` are
structs of `AssignedCell`s). Therefore:

- Subcircuit inputs/outputs are `AssignedCell` references, grouped in typed structs
  (`ProvableStruct` analogue).
- Source sum types are ported faithfully where they appear:
  `PaddedWord = Message(cell) | Padding(constant)`, `RangeConstrained` over
  assigned-cell vs. prover-value.
- Prover-side `Value<F>` inputs (unassigned values, assigned inside the gadget) use the
  phase-one `Unconstrained`/hint pattern; witness generation reuses Clean's witgen IR
  concepts.
- **`constrainConstant` and the constants column are first-class**: constants are copies
  against fixed cells that participate in the permutation argument (this is visible in
  the pinned CS: `constants: [Column 3 Fixed]`, permutation over 15 columns). Modeling
  them as gate-level `.const` would break VK matching.

### Semantics: trace satisfaction

The proof-facing anchor is a row-wise satisfaction predicate over traces
(assignments column-index → row → F): every gate polynomial vanishes at every row
(selector-weighted), copy-constrained cells are equal, lookup rows are members of their
tables. This predicate must bridge (one shared lemma, joint work with ironwood's
permutation/lookup soundness effort) to ironwood's polynomial-level `circuitSatViaGates`.

### Proofs are region-relative

- Cells in proofs are region-relative; absolute rows exist only after placement.
  Soundness/completeness of a gadget never depends on where the floor planner puts its
  regions.

### Proof UX

Target the phase-one proof experience: analogues of `circuit_proof_start`,
`circuit_norm`, and `elaborate_circuit`; subcircuit-style proof boundaries so parent
proofs consume child specs opaquely. User-land proofs must not unfold framework
internals.

### Reuse from phase one

The Orchard-in-Clean tree is the reference implementation and proof-content donor:

- `Spec`s, `Assumptions`, and all mathematical lemmas (CompElliptic-based EC facts,
  Sinsemilla/Poseidon specs, `pallas_natCard`) carry over (modulo consolidating them with `zcash/ironwood` specs).
- Circuit bodies are rewritten in the new DSL (mechanical; they already mirror
  `assign_region` structure), and plumbing halves of proofs are redone with the new
  automation.

## Out of Scope (Deferred)

- Recomputing the VK's `fixed_commitments` / permutation commitments in Lean (Pallas
  MSMs); until then, commitment-level VK identity rests on ironwood's fixture capture.
- Generalizing mainline Clean to share code with Halo2-Clean.

## Milestones

1. **Vertical slice**: core types + one gadget chain (`witness_point` →
   `add_incomplete`) end to end — configure, synthesize, region-relative proof, CS data
   extraction matched against the corresponding fixture fragment. De-risks every layer.

(More concrete milestones will be added as we progress.)
