# CompStark backend

Proves Clean ensembles with [CompStark](https://github.com/zksecurity/CompStark), a STARK prover and verifier in Lean that is byte-compatible with Plonky3, and connects CompStark's knowledge soundness to Clean's soundness theorems.

This is a separate Lake package, so that Clean does not depend on CompStark. It requires Clean (`../..`) and CompStark; their dependencies resolve to the same revisions.

## Translation

- `CleanCompStark.Fields`: Clean's `F p = ZMod p` and CompStark's Montgomery field `FastField p` are isomorphic (`montEquiv`, `koalaBear`, `babyBear`). The translation is generic over a ring isomorphism `e : F ≃+* K` to any CompStark base field.
- `CleanCompStark.Air`: a component becomes one AIR (`toAir`), laid out as the Plonky3 backend does. The fixed columns are the preprocessed trace; the trace commits the rest of the row's own input and the witnesses; a two-row component's next-row cells read the next row and its selector cells are Plonky3's selectors. Every constraint is split by `Backends.gateConstraint` and becomes its body times its gate's selector (`when_first_row`, `when_last_row`, `when_transition`). Every interaction becomes a global lookup on the bus named after its channel, with the negated multiplicity and weight `0`. `toRows` reads a trace back as Clean rows, `toTrace` drops the fixed and window cells of Clean rows.
- `CleanCompStark.Batch`: an ensemble becomes a batch with one instance per component (`toBatchSetup`).

## Theorems

- Lowering is correct (`eval_constraint_iff`): a constraint holds on a row read off the trace if and only if its lowered form vanishes on the trace's row. CompStark's selectors are scaled (`n` on the first row, `n ω` on the last, `ωⁱ - ω⁻¹` on transitions); they vanish exactly where Clean's 0/1 selectors do (`selectors_eq_zero_iff`).
- One component (`table_of_satisfied`): a trace satisfying the AIR of a `bridgeable` component is a table of the component, with consistent prover data, the fixed columns and the windows of its rows, whose constraints hold.
- An ensemble (`statement_of_satisfied`): traces satisfying a batch that proves an `EnsembleBridgeable` ensemble are a witness of `Ensemble.Statement`: the constraints hold and every channel balances, since its bus does (`rowBalance`; packing and bus numbering in `CleanCompStark.Buses`).
- Knowledge soundness, interactive and in the random-oracle model: `knowledgeSoundness_of_tableSound` for one component, `batchKnowledgeSoundness_of_witnessSound` and `batchKnowledgeSoundness_of_soundness` for an ensemble. Unless what the circuit proves holds of the rows read off some trace close to the committed one, the verifier accepts with probability at most CompStark's error.
- `CleanCompStark.KeccakAir.knowledgeSoundness` and `knowledgeSoundness_ro`: for any STARK proving Plonky3's Keccak-f AIR over KoalaBear, every 24-row block starting at round 0 of such rows computes Keccak-f.

The side conditions are explicit: `bridgeable` (no legacy lookups, gated constraints, cells within the row) is a decidable check; `Fits` asks for a trace domain in the two-adic subgroup, `u64` row indices and the fixed columns' height; `EnsembleBridgeable` asks for a verifier without interactions and channels told apart by their names; the number of interactions must stay below the characteristic.

## The keccak-air showcase

Plonky3's Keccak-f AIR, `p3-keccak-air` at `a4982ec` (2633 columns, 3182 constraints, 24 rows per permutation), is the two-row Clean component `KeccakAir.component`, with exactly upstream's layout and constraint order, proved sound against Clean's Keccak-f specification `Specs.Keccak256.keccakPermutation`. CompStark proves it, and the proof is Plonky3's: from the Clean AIR and Clean's fast trace, CompStark's prover produces Plonky3's proof byte for byte.

### The theorem

`CleanCompStark/KeccakShowcase.lean`, in the random-oracle model:

```lean
theorem keccak_soundness_ro (logN : ℕ) (h : Sized logN) (Q : ℕ)
    (prover : NIProver (stark logN h)) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run (stark logN h) [] prover}[
      verdict = .ok () ∧ proof.degreeBits = logN ∧
        ∀ trace ∈ closeTraces (stark logN h) extractorRadius
            (committedTrace (stark logN h) log proof),
          ¬ BlocksCorrect (toRows koalaBear (component logN) logN trace)] ≤
      (Q + (stark logN h).verifierQueries) * (2 ^ 100)⁻¹ +
        hashError KoalaBear.Fast.Field 3 (Q + (stark logN h).verifierQueries)
```

On `2 ^ logN` rows, `2 ^ 11` to `2 ^ 21` (`Sized`), a prover making at most `Q` oracle calls gets a proof accepted while the rows read off every trace within `δ' = 1/4 - 2 ^ (-11)` of the one it committed to fail to compute Keccak-f on some 24-row block starting at round 0 with probability at most `q · 2 ^ (-100) + hashError q`, `q = Q + verifierQueries`: 100 bits per oracle call. `BlocksCorrect rows` says that every 24-row block starting at round 0 has its preimage in 16-bit limbs and its last row's output is `keccakPermutation` of its first row's preimage (`KeccakAir.table_block_soundness`). The interactive version, `keccak_soundness`, bounds the acceptance probability of a prover none of whose close traces has correct blocks by `2 ^ (-84)`: without grinding to credit, the same configuration has 84 bits.

`stark logN h` is the STARK over KoalaBear's quartic extension with FRI's parameters `params`: blowup `2`, folding by arity `2` down to a constant (the arity the security calculator analyses), `204` queries with `16` bits of query grinding and `10` bits of batching grinding, and Merkle caps of height `3`. The calculator (`CompStark/SecurityCalculator.lean`) certifies every round error to be at most `2 ^ (-100)` (`secureRo`) with FRI's proximity `δ = 1/4 - 2 ^ (-10)` and the extractor's radius `δ' = 1/4 - 2 ^ (-11)`, below the unique-decoding radius of rate `1/2`, from the AIR's numbers: 3182 constraints (`numConstraints_setup`), the constraint identity's degree `3 n` (`identityDegree_setup`) and 5274 opened words (`numOpened_setup`). The largest round error is FRI's queries', about `2 ^ (-100.3)`; constraint folding, which Plonky3 does not grind, is about `2 ^ (-112.3)`. Plonky3's example's configuration (arity up to 8, 87 queries) is only conjectured to reach 100 bits.

The theorem composes CompStark's knowledge soundness in the random-oracle model, the transfer theorem `table_of_satisfied`, Clean's `KeccakAir.table_block_soundness` and the calculator. All of it uses only `propext`, `Classical.choice` and `Quot.sound` (`CleanCompStarkTests/Axioms.lean`) and is checked by the kernel in seconds: no proof evaluates the 3182 constraints.

- `bridgeable_component` (`CleanCompStark/KeccakAir/Bridgeable.lean`): the constraints are written once over any type with `+`, `-`, `*` and numerals, so their shapes (`plain`, a `selector`, `gated`) are the constraints of the cells' shapes, which `simp` reduces family by family.
- The AIR's numbers (`CleanCompStark/KeccakAir/Degree.lean`, `Lowered.lean`, `Setup.lean`): a lowered constraint's degree and degree bound are weights of the Clean constraint, and the weights are the constraints of the cells' weights, at most `max (3 a) (b + 2 a)` for cells of weight `a` and the transition selector `b`, with the parity constraints at `3 a`.

### Evidence

`lake exe keccak_showcase` (`KeccakShowcase/`) checks that the Clean AIR, trace and proofs are Plonky3's, against Plonky3 `a4982ec` in `rust/`, a reproduction of the upstream example `prove_prime_field_31 --field koala-bear --objective keccak-f-permutations --merkle-hash poseidon2 --discrete-fourier-transform radix-2-dit-parallel` from the same upstream functions (its configuration, its Poseidon2 constants `new_from_rng_128` of `SmallRng` seeded with `1`, caps of height 3, its inputs), since the example binary does not write its proof:

- fingerprint: the fingerprint report of the Clean AIR (`toAir`), the values of its 3182 constraints at pseudorandom points and their Poseidon2 digest, is that of Plonky3's `KeccakAir` from its symbolic constraints (CompStark's `tests/data/fingerprint/keccak_4.json`);
- trace: Clean's fast trace (`KeccakAir.koalaBearTrace`) is Plonky3's `generate_trace_rows` on the example's inputs, row by row, padding included;
- the example's configuration: CompStark's fast prover, from the Clean AIR and the Clean trace, produces Plonky3's proof byte for byte, and CompStark's verifier accepts Plonky3's proof;
- the proven configuration of the theorem: Plonky3's `verify` accepts CompStark's proof and rejects it with an opened value changed, CompStark's verifier accepts Plonky3's proof, and the two proofs are byte for byte the same.

Run, in this directory:

```sh
scripts/showcase.sh check 16
```

It builds `rust/` and the executable, runs `lake exe keccak_showcase kat` (CompStark's known answers from Plonky3: the fingerprint, the trace of five permutations and the example's proof on `2 ^ 6` rows, no Rust needed), then `lake exe keccak_showcase check 16 rust/target/release/keccak-showcase` on `2 ^ 16` rows, and prints one line per check.

### Benchmark

```sh
scripts/showcase.sh bench 16 3
```

times trace generation, the proof and its verification on `2 ^ 16` rows, `lake exe keccak_showcase bench CONFIG 16 3` (Lean: Clean's fast trace and CompStark's fast prover) interleaved with `rust/target/release/keccak-showcase bench CONFIG 16 3` (Plonky3), both configurations, medians of 3, two rounds each.

At CompStark `50708f5` on a Ryzen 7 3700X (8 cores, 16 threads), shared and loaded (load 9 to 13), all threads, two rounds:

| rows | configuration | Lean tracegen | Lean prove | Lean verify | Plonky3 tracegen | Plonky3 prove | Plonky3 verify |
|---|---|---|---|---|---|---|---|
| $2^{15}$ | example | 45–110 ms | 6.7–7.7 s | 326–334 ms | 26–28 ms | 850–862 ms | 11 ms |
| $2^{15}$ | proven | 36–55 ms | 7.1–7.6 s | 871–895 ms | 27–30 ms | 869–1008 ms | 18–19 ms |
| $2^{16}$ | example | 57–58 ms | 12.6–13.1 s | 281 ms | 52–57 ms | 1.84–1.92 s | 11 ms |
| $2^{16}$ | proven | 70 ms | 12.5–13.0 s | 873–917 ms | 56–60 ms | 1.91–2.04 s | 19 ms |

## Tests

`CleanCompStarkTests` proves and verifies Clean-generated traces with CompStark's specification prover over BabyBear: the two-row `SquaresTable` as a STARK (with its knowledge soundness instantiated), and a range check against a bytes lookup table as a batch. Tampered traces are rejected. `CleanCompStarkTests/Axioms.lean` checks the axioms of the headline theorems.

## Building

Run `lake build` and `lake build CleanCompStarkTests` in this directory, and `lake build keccak_showcase` for the showcase's executable. Point `.lake/packages` at existing checkouts with their builds rather than fetching and building Mathlib again.
