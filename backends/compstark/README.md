# CompStark backend

Proves Clean ensembles with [CompStark](https://github.com/zksecurity/CompStark), a STARK prover and verifier in Lean that is byte-compatible with Plonky3, and connects CompStark's knowledge soundness to Clean's soundness theorems.

This is a separate Lake package, so that Clean does not depend on CompStark. It requires Clean (`../..`) and CompStark; their dependencies resolve to the same revisions.

## Translation

- `CleanCompStark.Fields`: Clean's `F p = ZMod p` and CompStark's Montgomery field `FastField p` are isomorphic (`montEquiv`, `koalaBear`, `babyBear`). The translation is generic over a ring isomorphism `e : F ≃+* K` to any CompStark base field.
- `CleanCompStark.Air`: a component becomes one AIR (`toAir`), laid out as the Plonky3 backend does. The fixed columns are the preprocessed trace; the trace commits the rest of the row's own input and the witnesses; a two-row component's next-row cells read the next row and its selector cells are Plonky3's selectors. Every constraint is split by `Backends.gateConstraint` and becomes its body times its gate's selector (`when_first_row`, `when_last_row`, `when_transition`); Clean's subtraction `x + (-1) * z` becomes CompStark's `x - z` (`addExpr`), so that the quotient's program subtracts instead of multiplying. Every interaction becomes a global lookup on the bus named after its channel, with the negated multiplicity and weight `0`. `toRows` reads a trace back as Clean rows, `toTrace` drops the fixed and window cells of Clean rows.
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
- quotient kernel: the program of the Clean AIR's constraints (CompStark's `Prog.compile`, the same on every trace length) is the code of the quotient kernel `KeccakShowcase/Kernel.lean`, so that CompStark's fast backend runs it: straight-line code CompStark's `#gen_group_chunks` generates from the program in 19 chunks of 2000 instructions, in four modules (`KeccakShowcase/Kernel/`) that build in parallel, each chunk checked equal to the program on CompStark's group machine by the kernel's `rfl`;
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

times trace generation, the proof, both together and the proof's verification on `2 ^ 16` rows, `lake exe keccak_showcase bench CONFIG 16 3` (Lean: Clean's fast trace, CompStark's fast prover and its fast verifier `verifyFast`, Plonky3's verifier by `verifyFast_eq`, with the AIR, the prover's backend and the verifying key made once, as Plonky3's side makes its configuration once) interleaved with `rust/target/release/keccak-showcase bench CONFIG 16 3` (Plonky3, built for the native CPU), both configurations, medians of 3, two rounds each, with each process's peak memory. `LEAN_NUM_THREADS=1 RAYON_NUM_THREADS=1 scripts/showcase.sh bench 16 1` runs both sides on one thread.

At CompStark `80eefbd` (CompPoly `b8e2f94`) on a Ryzen 7 3700X (8 cores, 16 threads), shared with other jobs (load 5.3 to 6.0), all threads, medians of 3 in each of two interleaved rounds, the median of the rounds. Total is trace generation and proof, end to end from the inputs; the example configuration has 87 queries, the proven one (`keccak_soundness_ro`) 203:

| rows | config | Lean tracegen | Lean prove | Lean total | Plonky3 tracegen | Plonky3 prove | Plonky3 total | Lean / Plonky3 | Lean verify | Plonky3 verify | peak memory Lean / Plonky3 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| $2^{15}$ | example | 25 ms | 1.09 s | 1.12 s | 27 ms | 861 ms | 887 ms | 1.26 | 49 ms | 13 ms | 1.5 GB / 0.7 GB |
| $2^{15}$ | proven | 24 ms | 1.09 s | 1.11 s | 24 ms | 826 ms | 851 ms | 1.30 | 115 ms | 16 ms | 1.5 GB / 0.7 GB |
| $2^{16}$ | example | 50 ms | 2.09 s | 2.14 s | 48 ms | 1.84 s | 1.89 s | 1.14 | 51 ms | 11 ms | 2.8 GB / 1.3 GB |
| $2^{16}$ | proven | 47 ms | 2.12 s | 2.16 s | 48 ms | 1.83 s | 1.88 s | 1.15 | 125 ms | 16 ms | 2.8 GB / 1.3 GB |
| $2^{17}$ | example | 89 ms | 3.84 s | 3.93 s | 90 ms | 4.53 s | 4.62 s | 0.85 | 51 ms | 11 ms | 4.8 GB / 2.7 GB |
| $2^{17}$ | proven | 94 ms | 4.13 s | 4.22 s | 89 ms | 4.49 s | 4.58 s | 0.92 | 128 ms | 17 ms | 4.8 GB / 2.7 GB |
| $2^{18}$ | example | 184 ms | 8.04 s | 8.24 s | 178 ms | 10.82 s | 11.01 s | 0.75 | 56 ms | 11 ms | 9.0 GB / 5.3 GB |
| $2^{18}$ | proven | 175 ms | 7.97 s | 8.14 s | 180 ms | 10.79 s | 10.97 s | 0.74 | 133 ms | 17 ms | 9.0 GB / 5.3 GB |

On one thread (load 3 to 13), medians of 3 interleaved rounds of one proof each:

| rows | config | Lean tracegen | Lean prove | Lean total | Plonky3 tracegen | Plonky3 prove | Plonky3 total | Lean / Plonky3 | Lean verify | Plonky3 verify |
|---|---|---|---|---|---|---|---|---|---|---|
| $2^{15}$ | example | 100 ms | 6.37 s | 6.47 s | 170 ms | 4.16 s | 4.33 s | 1.50 | 51 ms | 10 ms |
| $2^{15}$ | proven | 100 ms | 6.50 s | 6.60 s | 170 ms | 4.14 s | 4.31 s | 1.53 | 112 ms | 16 ms |
| $2^{16}$ | example | 206 ms | 13.02 s | 13.22 s | 321 ms | 8.24 s | 8.58 s | 1.54 | 49 ms | 11 ms |
| $2^{16}$ | proven | 212 ms | 13.67 s | 13.88 s | 322 ms | 8.32 s | 8.64 s | 1.61 | 125 ms | 16 ms |
| $2^{17}$ | example | 394 ms | 29.39 s | 29.80 s | 640 ms | 17.14 s | 17.78 s | 1.68 | 54 ms | 14 ms |
| $2^{17}$ | proven | 400 ms | 27.55 s | 27.98 s | 643 ms | 16.88 s | 17.51 s | 1.60 | 123 ms | 17 ms |
| $2^{18}$ | example | 935 ms | 67.54 s | 68.87 s | 1.35 s | 33.45 s | 34.81 s | 1.98 | 62 ms | 11 ms |
| $2^{18}$ | proven | 793 ms | 61.47 s | 62.26 s | 1.34 s | 35.22 s | 36.56 s | 1.70 | 182 ms | 22 ms |

From $2^{17}$ rows on 16 threads, the Lean side proves faster than Plonky3 end to end, by a quarter at $2^{18}$; on one thread it takes 1.5 to 2 times as long. Clean's trace generation takes about the time of Plonky3's `generate_trace_rows` on 16 threads and 0.6 times it on one. The proven configuration's 116 more queries cost little to prove and add about 70 ms to the Lean verifier, which takes 50 to 180 ms against Plonky3's 10 to 22 ms.

The prover is CompStark's on its Keccak fixture (`CompStarkBench keccak`, Plonky3's `KeccakAir` written directly in CompStark, interleaved with the runs above): its proofs from the trace take 1.08 s, 2.00 s, 4.01 s and 8.01 s on $2^{15}$ to $2^{18}$ rows on 16 threads and 6.5 s, 12.9 s, 27.4 s and 56.8 s on one thread, the same as the showcase's within the noise, and its trace generation takes about twice Clean's. The Clean AIR's quotient is the fixture's: Clean writes `x - y` as `x + (-1) * y`, which the lowering turns back into a subtraction (`addExpr`), so that its program has the fixture's instruction mix (36212 instructions, 8941 multiplications, against 36069 and 8742) rather than 43048 instructions with 15777 multiplications; the showcase runs this program as the generated kernel `KeccakShowcase/Kernel.lean`, checked against the AIR by `check` and `kat`.

## Tests

`CleanCompStarkTests` proves and verifies Clean-generated traces with CompStark's specification prover over BabyBear: the two-row `SquaresTable` as a STARK (with its knowledge soundness instantiated), and a range check against a bytes lookup table as a batch. Tampered traces are rejected. `CleanCompStarkTests/Axioms.lean` checks the axioms of the headline theorems.

## Building

Run `lake build` and `lake build CleanCompStarkTests` in this directory, and `lake build keccak_showcase` for the showcase's executable. Point `.lake/packages` at existing checkouts with their builds rather than fetching and building Mathlib again.
