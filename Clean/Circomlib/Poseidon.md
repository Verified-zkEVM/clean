# Verified optimized Poseidon circuits

`Clean.Circomlib.Poseidon` implements the optimized circomlib Poseidon
schedule over the BN254 scalar field. The circuit is verified once for a
symbolic state width and then specialized through parameter bundles.

The implementation follows six phases:

1. initialize the state with capacity element zero and apply the initial ARK;
2. apply three dense full rounds using `M`;
3. apply the transition full round using `P`;
4. apply every optimized sparse partial round using `S`;
5. apply three more dense full rounds using `M`;
6. apply the final full S-box layer and compute output coordinate zero with
   `MixLast`.

## Generic specification

`Specs.PoseidonOptimized.Params t` contains the round count and indexed
constant tables for state width `t`:

```lean
structure Params (t : ℕ) where
  nPartial : ℕ
  C : Vector ℕ (8 * t + nPartial)
  M : Vector (Vector ℕ t) t
  P : Vector (Vector ℕ t) t
  S : Vector ℕ (nPartial * (2 * t - 1))
  two_le_width : 2 ≤ t
```

The vector lengths encode the constant-index bounds used by the proof. The
pure function

```lean
Specs.PoseidonOptimized.poseidon params : Vector F (t - 1) → F
```

is the semantic specification of the circuit. Parameter bundles exist for
every circomlib-supported state width from 2 through 17 (`params_t2` through
`params_t17`), corresponding to input arities 1 through 16.

The constant tables are deterministically generated during Lean elaboration
from the parameters used by iden3/circomlib commit
`35e54ea21da3e8762557234298dbb553c175ea8d`. The generated definitions retain
the same statically sized vector types and public names as the old literals.

## Verified circuit boundaries

The implementation is divided into reusable `FormalCircuit`s:

| Circuit | Semantic role |
| --- | --- |
| `InitialArk.circuit` | Build `[0, inputs...]` and add the initial constants |
| `Sigma.circuit` | Compute `x^5` |
| `Mix.circuit` | Apply an arbitrary dense matrix |
| `MixS.circuit` | Apply one optimized sparse matrix |
| `MixLast.circuit` | Compute coordinate zero of the final dense mix |
| `FullRound.circuit` | Full S-box, ARK, and dense mix |
| `PartialRound.circuit` | First-coordinate S-box and ARK, then sparse mix |
| `ApplyFullRounds.circuit` | Fold any number of dense rounds |
| `ApplyPartialRounds.circuit` | Fold any valid range of sparse rounds |
| `FinalRound.circuit` | Full S-box followed by `MixLast` |

Parents call these bundled circuits as subcircuits and consume their semantic
specifications. The top-level proof does not unfold child operation traces.

## Generic top-level circuit

`Clean.Circomlib.Poseidon.Generic` exposes:

```lean
Circomlib.Poseidon.circuit (params : Params t) :
  FormalCircuit F (fields (t - 1)) field
```

Its specification is:

```lean
output = Specs.PoseidonOptimized.poseidon params input
```

One soundness proof and one completeness proof cover every well-typed
parameter bundle. The generic local witness count is

```text
32 * t + params.nPartial * (t + 4) + 1
```

## `Poseidon1` compatibility wrapper

The historical scalar-input interface remains available:

```lean
Poseidon1.main : Expression F → Circuit F (Expression F)
Poseidon1.Spec (input output : F) : Prop :=
  output = Specs.PoseidonOptimized.poseidon1Opt input
Poseidon1.circuit : FormalCircuit F field field
```

It is a thin adapter around `Circomlib.Poseidon.circuit params_t2`, packaging
the scalar input as a length-one vector. `poseidon1Opt` is itself a
compatibility alias for the generic `params_t2` specification.

The wrapper has 401 local witnesses. Its output remains at local offset 400,
so consumers that elaborate its operations at offset 1 continue to use
circuit variable 401. The previous implementation used 402 witnesses because
it computed and stored both coordinates of the final dense mix; `MixLast`
deliberately omits the unused second coordinate.

## Arity-specific instances

The wider instances are direct aliases of the generic circuit because their
public inputs already use the generic vector representation. The first two
are:

```lean
Poseidon2.circuit : FormalCircuit F (fields 2) field
Poseidon3.circuit : FormalCircuit F (fields 3) field
```

The same pattern continues through:

```lean
Poseidon16.circuit : FormalCircuit F (fields 16) field
```

`PoseidonN.circuit` specializes `Circomlib.Poseidon.circuit` with
`params_t(N+1)`. No arity-specific soundness or completeness proof is needed.
For example, the generic witness-count formula gives 496 local witnesses for
`Poseidon2` and 577 for `Poseidon3`.

## Guarantees and regression coverage

Lean proves:

- soundness: every satisfying assignment produces the generic optimized
  Poseidon result;
- completeness: the honest witness generator satisfies every constraint;
- the same results for the arity-specific wrappers;
- the `Poseidon1` witness count and output position stated above.

Compile-time vectors compare the optimized specification with the independent
non-optimized Poseidon specification for widths 2, 3, and 4. For every new
input arity 4 through 16, `PoseidonReferenceVectors.lean` checks the input
`[1, 2, ..., n]` against an output generated by both the reference and
optimized implementations from iden3/circomlibjs commit
`48b3ab37013c5ed21e9ff8a80a5b010795c97094`. The WASM demo also exports the
complete `Poseidon1` circuit and R1CS using the preserved output position.

Useful verification commands:

```bash
lake build Clean.Circomlib.Poseidon
lake build Clean.Specs.PoseidonReferenceVectors
lake build Clean.Examples.WasmDemo
lake build Clean.Backends.Circom.TestWasmCompile
```

The constants are produced by `PoseidonParameterGeneration.lean` from the
Grain-LFSR, Cauchy MDS construction, constant compression, and sparse-matrix
factorization. `PoseidonParameterElaboration.lean` runs that executable Lean
generator once per width while compiling `PoseidonConstants.lean`, and emits
ordinary typed vector terms. Downstream modules therefore consume constants,
not computations that regenerate them on every use.

This arrangement replaces the former 1.69 MB literal source file. Before the
literals were removed, Lean checked all 24,060 generated C/M/P/S values for
exact equality with that table. An independent Python implementation checked
the same values against `poseidon_constants.circom` from circomlib commit
`35e54ea21da3e8762557234298dbb553c175ea8d` (source SHA-256
`94c9e4b5ea891ab4d1ba626f1d719f8c661014d9b628f6096c803f75f39e3eee`).
The resulting per-width and combined digests are retained by the independent
Python audit:

```bash
python3 scripts/reproduce_poseidon_constants.py --trials 1
```

This offline command needs only Python's standard library. It regenerates all
values, checks the pinned digests, and reports separate base generation,
optimization, and total timings. Normal Lean builds are also deterministic and
offline; neither path downloads circomlib or requires an external checkout.

For a full value-by-value audit against a local copy of the original pinned
circomlib source, run:

```bash
python3 scripts/reproduce_poseidon_constants.py \
  --source /path/to/circomlib/circuits/poseidon_constants.circom --trials 1
```

The script rejects a source file whose SHA-256 differs from the pinned source.
Reference vectors have a separate optional upstream audit:

```bash
node scripts/generate_poseidon_vectors.mjs \
  --circomlibjs /path/to/circomlibjs --check
```

The correspondence with the external circomlib source is an audited regression
check rather than a theorem about that external file. Soundness and
completeness of the circuit relative to the generated Lean specification remain
fully proved in Lean.
