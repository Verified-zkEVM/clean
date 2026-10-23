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
    (prover : NIProver (stark 203 logN h)) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run (stark 203 logN h) [] prover}[
      verdict = .ok () ∧ proof.degreeBits = logN ∧
        ∀ trace ∈ closeTraces (stark 203 logN h) (radius 13)
            (committedTrace (stark 203 logN h) log proof),
          ¬ BlocksCorrect (toRows koalaBear (component logN) logN trace)] ≤
      (Q + (stark 203 logN h).verifierQueries) * (2 ^ 100)⁻¹ +
        hashError KoalaBear.Fast.Field 3 (Q + (stark 203 logN h).verifierQueries)
```

On `2 ^ logN` rows, `2 ^ 12` to `2 ^ 21` (`Sized`), a prover making at most `Q` oracle calls gets a proof accepted while the rows read off every trace within `δ' = 1/4 - 2 ^ (-13)` (`radius 13`) of the one it committed to fail to compute Keccak-f on some 24-row block starting at round 0 with probability at most `q · 2 ^ (-100) + hashError q`, `q = Q + verifierQueries`: 100 bits per oracle call. `BlocksCorrect rows` says that every 24-row block starting at round 0 has its preimage in 16-bit limbs and its last row's output is `keccakPermutation` of its first row's preimage (`KeccakAir.table_block_soundness`).

`stark numQueries logN h` is the STARK over KoalaBear's quartic extension with FRI's parameters `params numQueries`: those of Plonky3's example `prove_prime_field_31` (blowup `2`, folding by arity up to `8` down to a constant, `16` bits of query grinding and `10` bits of batching grinding, Merkle caps of height `3`) with `numQueries` queries. The example's own configuration is `params 87`. The security calculator (CompStark's `CompStark/SecurityCalculator.lean`) reads the STARK's shape (`shape_setup`: 3182 constraints, the identity degree `3 n`, 5274 opened words, no lookups) and certifies each bound in the kernel, for every trace length of `Sized`, at an analysis its search finds. Each query count is the smallest the calculator certifies on all of `2 ^ 12` to `2 ^ 21` rows:

| theorem | queries | analysis | proven bits |
| --- | --- | --- | --- |
| `keccak_soundness_ro` | `203` | `δ = 1/4 - 2 ^ (-11)`, `δ' = 1/4 - 2 ^ (-13)` | `100` per oracle call |
| `keccak_soundness` (interactive) | `247` | `δ = 1/4 - 2 ^ (-10)`, `δ' = 1/4 - 2 ^ (-12)`, loss `2 ^ (-16)` | `100` |
| `keccak_soundness_ro_example` (Plonky3's example) | `87` | `δ = 1/4 - 2 ^ (-11)`, `δ' = 1/4 - 2 ^ (-13)` | `52` per oracle call |

In the random-oracle model the largest round error is FRI's queries', `2 ^ (-100.06)` with `203` queries; constraint folding, which Plonky3 does not grind, is `2 ^ (-112.3)`, and the out-of-domain term `(3n + n) / |𝕂|` is `2 ^ (-100.95)` on `2 ^ 21` rows, which bounds the trace lengths from above. FRI's proximity `δ` stays below the unique-decoding radius `1/4` of rate `1/2`, where the proven correlated-agreement bounds hold, so each query is worth at most `log₂ (4/3) ≈ 0.415` bits: the `87` queries and `16` bits of grinding of Plonky3's example prove `52` bits per oracle call, where Plonky3 conjectures 100. Interactively, without grinding to credit, `247` queries reach 100 bits on `2 ^ 21` rows (`100.07`), limited by the sum of the out-of-domain, batching and query terms. At blowup `4` the calculator's search reaches 100 bits per oracle call with `124` queries; the showcase keeps the example's blowup.

The theorems compose CompStark's knowledge soundness in the random-oracle model, the transfer theorem `table_of_satisfied`, Clean's `KeccakAir.table_block_soundness` and the calculator. All of it uses only `propext`, `Classical.choice` and `Quot.sound` (`CleanCompStarkTests/Axioms.lean`) and is checked by the kernel in seconds: no proof evaluates the 3182 constraints.

- `bridgeable_component` (`CleanCompStark/KeccakAir/Bridgeable.lean`): the constraints are written once over any type with `+`, `-`, `*` and numerals, so their shapes (`plain`, a `selector`, `gated`) are the constraints of the cells' shapes, which `simp` reduces family by family.
- The STARK's shape (`CleanCompStark/KeccakAir/Degree.lean`, `Lowered.lean`, `Setup.lean`): a lowered constraint's degree, and the sum of its degree profile's entries, are weights of the Clean constraint, and the weights are the constraints of the cells' weights, at most `max (3 a) (b + 2 a)` for cells of weight `a` and the transition selector `b`, with the parity constraints at `3 a`. So every constraint's degree profile fits two quotient chunks (`profileFits_toAir`), which fixes the calculator's shape (`shape_setup`).

### Evidence

`lake exe keccak_showcase` (`KeccakShowcase/`) checks that the Clean AIR, trace and proofs are Plonky3's, against Plonky3 `a4982ec` in `rust/`, a reproduction of the upstream example `prove_prime_field_31 --field koala-bear --objective keccak-f-permutations --merkle-hash poseidon2 --discrete-fourier-transform radix-2-dit-parallel` from the same upstream functions (its configuration, its Poseidon2 constants `new_from_rng_128` of `SmallRng` seeded with `1`, caps of height 3, its inputs), since the example binary does not write its proof:

- fingerprint: the fingerprint report of the Clean AIR (`toAir`), the values of its 3182 constraints at pseudorandom points and their Poseidon2 digest, is that of Plonky3's `KeccakAir` from its symbolic constraints (CompStark's `tests/data/fingerprint/keccak_4.json`);
- trace: Clean's fast trace (`KeccakAir.koalaBearTrace`) is Plonky3's `generate_trace_rows` on the example's inputs, row by row, padding included;
- the example's configuration: CompStark's fast prover, from the Clean AIR and the Clean trace, produces Plonky3's proof byte for byte, and CompStark's verifier accepts Plonky3's proof;
- the proven configuration of `keccak_soundness_ro` (the example's with `203` queries): Plonky3's `verify` accepts CompStark's proof and rejects it with an opened value changed, CompStark's verifier accepts Plonky3's proof, and the two proofs are byte for byte the same.

Run, in this directory:

```sh
scripts/showcase.sh check 16
```

It builds `rust/` and the executable, runs `lake exe keccak_showcase kat` (CompStark's known answers from Plonky3: the fingerprint, the trace of five permutations and the example's proof on `2 ^ 6` rows, no Rust needed), then `lake exe keccak_showcase check 16 rust/target/release/keccak-showcase` on `2 ^ 16` rows, and prints one line per check.

### Benchmark

```sh
scripts/showcase.sh bench 16 3
```

times trace generation, the proof and its verification on `2 ^ 16` rows, `lake exe keccak_showcase bench CONFIG 16 3` (Lean: Clean's fast trace and CompStark's fast prover, with the AIR, the prover's backend and the verifying key made once, as Plonky3's side makes its configuration once) interleaved with `rust/target/release/keccak-showcase bench CONFIG 16 3` (Plonky3, built for the native CPU), both configurations, medians of 3, two rounds each. `LEAN_NUM_THREADS=1 RAYON_NUM_THREADS=1 scripts/showcase.sh bench 16 1` runs both sides on one thread.

At CompStark `45dadc6` on a Ryzen 7 3700X (8 cores, 16 threads), shared and loaded (load 6 to 22), all threads, two rounds:

| rows | configuration | Lean tracegen | Lean prove | Lean verify | Plonky3 tracegen | Plonky3 prove | Plonky3 verify |
|---|---|---|---|---|---|---|---|
| $2^{15}$ | example | 30–32 ms | 2.11–2.29 s | 167–171 ms | 28–29 ms | 0.89–0.94 s | 11 ms |
| $2^{15}$ | proven | 32–34 ms | 2.33–2.53 s | 403–415 ms | 27 ms | 0.87–0.90 s | 17 ms |
| $2^{16}$ | example | 59–62 ms | 4.65–4.88 s | 172–175 ms | 55–59 ms | 1.89–1.96 s | 11 ms |
| $2^{16}$ | proven | 60–61 ms | 3.97–4.67 s | 399–412 ms | 50–52 ms | 1.82–1.94 s | 16–17 ms |
| $2^{17}$ | example | 126–134 ms | 10.10–10.68 s | 244–251 ms | 105–117 ms | 4.75–4.80 s | 11–12 ms |
| $2^{17}$ | proven | 144 ms | 11.86–13.29 s | 467–474 ms | 121–158 ms | 4.91–5.30 s | 17–18 ms |

On one thread (load 10 to 24), medians of 1, two rounds:

| rows | configuration | Lean tracegen | Lean prove | Lean verify | Plonky3 tracegen | Plonky3 prove | Plonky3 verify |
|---|---|---|---|---|---|---|---|
| $2^{15}$ | example | 100–133 ms | 10.5–11.9 s | 198–263 ms | 190–221 ms | 4.64–4.74 s | 15 ms |
| $2^{15}$ | proven | 129–134 ms | 12.0–12.8 s | 402–488 ms | 171–180 ms | 4.39–4.66 s | 23–24 ms |
| $2^{16}$ | example | 194–271 ms | 23.3–26.8 s | 171–200 ms | 353–366 ms | 8.48–9.23 s | 11–15 ms |
| $2^{16}$ | proven | 194–206 ms | 21.9–25.3 s | 408–468 ms | 344–345 ms | 8.65–8.70 s | 17 ms |

On $2^{18}$ rows the Lean prover peaks above 12 GB of memory (7.5 GB on $2^{17}$, where Plonky3 takes 2.8 GB).

## Tests

`CleanCompStarkTests` proves and verifies Clean-generated traces with CompStark's specification prover over BabyBear: the two-row `SquaresTable` as a STARK (with its knowledge soundness instantiated), and a range check against a bytes lookup table as a batch. Tampered traces are rejected. `CleanCompStarkTests/Axioms.lean` checks the axioms of the headline theorems.

## Building

Run `lake build` and `lake build CleanCompStarkTests` in this directory, and `lake build keccak_showcase` for the showcase's executable. Point `.lake/packages` at existing checkouts with their builds rather than fetching and building Mathlib again.
