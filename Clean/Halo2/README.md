# Halo2-Clean

Halo2-Clean (`Clean/Halo2/`) is a halo2-native circuit framework in Lean for writing halo2 circuits idiomatically and formally proving their soundness and completeness against trace-level and compiled constraint-system semantics.

## Relation to Main Clean

Main Clean targets a linear witness tape, which cannot directly represent halo2's 2D cell layout (columns, rows, rotations, selectors, copy constraints, and lookup tables). Rather than generalizing Clean's tape-indexed core immediately, Halo2-Clean builds a parallel, halo2-shaped framework designed to mirror main Clean's structure, naming, and proof experience so that the two can be consolidated later.

Where components do not depend on Clean's tape-indexed layer, they are shared rather than copied — notably the witness-generation IR (`Clean/Circuit/WitnessIR.lean`, parameterized over variable atoms) and `ProvableType`/`ProvableStruct` machinery. Deviations from main Clean are confined to halo2-specific structure: variables are cells (`AssignedCell`) with region-relative addressing rather than linear tape indices, the operation set matches halo2's region and layouter operations, and compilation targets a halo2 constraint system and floor-planned layout rather than a flat operation list.

One simplification compared to main Clean is that `FormalCircuit`, `FormalAssertion`, and `GeneralFormalCircuit` collapse into a single hint-aware contract (`FormalCircuit` at layouter level, `FormalRegionCircuit` at region level).

## Two-Layer DSL

Mirroring the Rust `halo2_proofs` API, circuits have two layers:

1. **Configure layer** (`Configure`, `ConstraintSystem`): defines custom gates and lookup arguments as expressions over `(column, rotation)` queries with first-class simple and complex selectors. Gate polynomials reuse main Clean's `Expression`, generalized over the query type (`Expression F Query`), with rich-expression lowering for halo2's extra AST nodes (`Negated`, `Scaled`) at the keygen/VK boundary.
2. **Synthesize layer** (`Circuit`, `RegionCircuit`, `Operations`): monadic region and layouter DSL mirroring halo2's `Region` and `Layouter` APIs (`assignAdvice`, `assignAdviceFromConstant`, `assignAdviceFromInstance`, `assignFixed`, `copyAdvice`, `constrainEqual`, `constrainConstant`, selector/lookup `enable`, `loadTable`, and `assignRegion`).

Both layers are bundled into `FormalCircuit F ConfigInput Config Input Output` (layouter-level) and `FormalRegionCircuit F ConfigInput Config Input Output` (region-level, for fragments composed inside an ambient region at a row `offset`). `ConfigInput` and `Config` are explicit type parameters so parent circuits interact with them directly; soundness and completeness quantify over arbitrary `config` (and `offset` at region level). Configuration side conditions that a proof genuinely depends on (such as lookup selector-index distinctness) are carried in `EnvAssumptions config`.

## Composition Currency: Cell References

In halo2's synthesize phase, expressions exist only at configure time and every gadget-level value is backed by assigned cells:

- Subcircuit inputs and outputs are `AssignedCell` references grouped in typed structures (`ProvableType` / `ProvableStruct`, plus `deriving CircuitType` for mixed provable/hint records).
- Constants constrained via `constrainConstant` use a dedicated fixed constants column that participates in the permutation argument, preserving VK layout fidelity.
- **No prover information at synthesis time**: `synthesize` never branches on or takes prover-side witness values as parameters. Witness computation runs through the witness IR (`Clean/Halo2/WitnessIR.lean`), and external hints use `Unconstrained` / `UnconstrainedNative` mechanisms so circuit layout is strictly independent of the witness.

## Semantics, Region-Relativity, and Region-Faithfulness

The proof-facing semantics is row-wise trace satisfaction over an `Environment` (assignments `column → row → F`): every active gate polynomial vanishes, copy-constrained cells are equal, fixed writes match, and enabled lookup rows belong to their loaded tables. The `Compiler/` layer proves that compiled gate vanishing, resolved copy equality, and lookup membership imply the top-level circuit specification (`TopLevelCircuit.soundness_compiled`; see [Compiler/README.md](Compiler/README.md)).

Proofs of gadgets are **region-relative**: cells are addressed relative to their region, and absolute rows appear only after floor-planner placement, so gadget soundness and completeness never depend on where the floor planner places a region.

When porting Rust halo2 circuits whose verification keys must match, ports must be **region-faithful**: `assignRegion` boundaries and their contents must mirror the Rust source, because the verifying key's permutation commitments depend on floor-planned cell positions.

## Knowledge Soundness and Constructive Extractors

When a specification references internal witnesses that are not part of circuit I/O (such as window-decomposed scalars in fixed-base scalar multiplication), `FormalCircuit` provides a `Witness` type slot (defaulting to `unit`) and a computable **extractor** mapping the low-level placement and environment to `Witness F`. `Spec` takes the extracted witness as an argument, and parent extractors compose child extractors constructively across the subcircuit tree.

## Proof Automation and Conventions

- **Deliberate simp normal forms**: monadic binds, DSL atoms (`assignAdvice`, `copyAdvice`, …), and circuit accessors (`output`, `operations`) are normal forms and do not unfold blindly. `circuit_norm` rewrites via dedicated composition lemmas in `Lemmas.lean`, `Operations.lean`, `Loops.lean`, and `Subcircuit.lean`.
- **Subcircuit boundaries**: `Subcircuit.lean` and `Tactics/SubcircuitRw.lean` / `Tactics/CircuitProofStart2.lean` peel subcircuit calls into opaque child specs so parent proofs consume child contracts without unfolding child internals.
- **`provable_type_simp`**: normalizes `ProvableType`/`ProvableStruct` evaluations along component boundaries (`StructEvalSimprocs.lean`, `Tactics/ProvableTypeSimp.lean`) while keeping opaque evaluations folded and preserving `AssignedCell.of` / `Environment.advice` / `Environment.fixed` pretty normal forms.
- **Completeness contracts**: completeness assumes both verifier-visible `Assumptions` and optional hint-side `ProverAssumptions` (default `True`), and establishes `Spec` plus optional `ProverSpec` (default `True`). Keep `ProverAssumptions`/`ProverSpec` at `True` unless a gadget or its parent genuinely needs hint-side facts.

## Directory Layout

- `Basic.lean`, `Expression.lean`, `ConstraintSystem.lean`, `Operations.lean`, `Operations/`: core columns, queries, gates, lookups, cells, environments, and region/layouter operations.
- `Configure.lean`, `Configure/`, `ElaboratedConfigure.lean`: configure-phase monad, query/selector tracking, and elaborated configuration contracts.
- `Provable.lean`, `CircuitTypeDeriving.lean`, `StructEvalSimprocs.lean`, `WitnessIR.lean`, `UnconstrainedNative.lean`: halo2 `ProvableType` evaluation, mixed-type deriving, eval simprocs, witness IR instantiation, and external hints.
- `Formal.lean`, `Formal/`, `FormalRegion.lean`, `FormalRegion/`, `Elaborated.lean`, `Subcircuit.lean`, `Loops.lean`, `Lemmas.lean`: formal circuit/region contracts, elaboration, subcircuit composition, loop combinators, and `circuit_norm` composition lemmas.
- `TopLevel.lean`, `CircuitShape.lean`, `SynthesisSummary/`: top-level circuit assembly and synthesis summaries.
- `Keygen.lean`, `Keygen/`: floor planner, selector compression, query/gate projection, and pinned constraint-system extraction for VK matching.
- `Compiler/`: compiled constraint semantics and soundness preservation (see [Compiler/README.md](Compiler/README.md)).
- `Tactics/`: proof automation (`CircuitProofStart2`, `SubcircuitRw`, `ProvableTypeSimp`, `AbstractOutputs`, `ContractBridges`, `Keygen`, `QueryCorrect`, `SelectorFree`).
- `Tests/`: framework regression tests for simprocs, subcircuits, loops, lookups, keygen, and tactics.
