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

The constant tables are generated from iden3/circomlib commit
`35e54ea21da3e8762557234298dbb553c175ea8d`. The generator validates the
upstream file's SHA-256 and every expected table length before emitting Lean.

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

All constants and reference vectors used by these builds are committed as
Lean data. Normal proof checking and circuit compilation are offline: they do
not run either generator and do not require an upstream repository checkout.
The pinned checkouts below are needed only to audit or regenerate that data.

To reproduce and check the imported data from pinned upstream checkouts:

```bash
python3 scripts/generate_poseidon_constants.py \
  --source /path/to/circomlib/circuits/poseidon_constants.circom --check
node scripts/generate_poseidon_vectors.mjs \
  --circomlibjs /path/to/circomlibjs --check
```

The translation from circomlib source is not mechanically proved in Lean, but
the generators pin source revisions and hashes, validate dimensions, and
detect any changed, reordered, or truncated value.
