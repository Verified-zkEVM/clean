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
- Knowledge soundness, for any bridgeable component or ensemble and any STARK or batch proving it, whatever its FRI parameters and grinding: unless what the circuit proves holds of the rows read off some trace close to the committed one, the verifier accepts with probability at most `2 ^ (-bits)` for the bits CompStark's security calculator certifies in the kernel for the configuration (`knowledgeSoundness_of_secure`, and per oracle call in the random-oracle model `knowledgeSoundness_ro_of_secureRo`, for one component; `batchKnowledgeSoundness_of_secure` and `batchKnowledgeSoundness_ro_of_secureRo` for an ensemble). In terms of CompStark's knowledge and round errors at any radii, they are `knowledgeSoundness_of_tableSound`, `knowledgeSoundness_ro_of_tableSound`, `batchKnowledgeSoundness_of_witnessSound`, `batchKnowledgeSoundness_ro_of_witnessSound` and `batchKnowledgeSoundness_of_soundness`.
- `CleanCompStark.KeccakAir`: Plonky3's Keccak-f AIR over KoalaBear is a bridgeable component (`bridgeable_component`) that fits every trace domain (`fits`) and whose tables compute Keccak-f on every 24-row block starting at round 0 (`tableSound`, `BlocksCorrect`), so the theorems above apply to any STARK proving it; the showcase below is one instance.

The side conditions are explicit: `bridgeable` (no legacy lookups, gated constraints, cells within the row) is a decidable check; `Fits` asks for a trace domain in the two-adic subgroup, `u64` row indices and the fixed columns' height; `EnsembleBridgeable` asks for a verifier without interactions and channels told apart by their names; the number of interactions must stay below the characteristic.

## The keccak-air showcase

Plonky3's Keccak-f AIR, `p3-keccak-air` at `a4982ec` (2633 columns, 3182 constraints, 24 rows per permutation), is the two-row Clean component `KeccakAir.component`, with exactly upstream's layout and constraint order, proved sound against Clean's Keccak-f specification `Specs.Keccak256.keccakPermutation`. CompStark proves it, and the proof is Plonky3's: from the Clean AIR and Clean's fast trace, CompStark's prover produces Plonky3's proof byte for byte.

### The theorem

`CleanCompStark/KeccakShowcase.lean`, in the random-oracle model, an instance of the backend's `knowledgeSoundness_ro_of_secureRo` for the Keccak-f component; CompStark's calculator certifies any configuration the same way:

```lean
theorem keccak_soundness_ro (logN : ℕ) (h : Sized logN) (Q : ℕ)
    (prover : NIProver (stark 203 logN h)) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run (stark 203 logN h) [] prover}[
      verdict = .ok () ∧ proof.degreeBits = logN ∧
        ∀ trace ∈ closeTraces (stark 203 logN h) (2047 / 8192)
            (committedTrace (stark 203 logN h) log proof),
          ¬ BlocksCorrect (toRows koalaBear (component logN) logN trace)] ≤
      (Q + (stark 203 logN h).verifierQueries) * (2 ^ 100)⁻¹ +
        hashError KoalaBear.Fast.Field 3 (Q + (stark 203 logN h).verifierQueries)
```

On `2 ^ logN` rows, `2 ^ 12` to `2 ^ 21` (`Sized`), a prover making at most `Q` oracle calls gets a proof accepted while the rows read off every trace within `δ' = 2047 / 8192 = 1/4 - 2 ^ (-13)` of the one it committed to fail to compute Keccak-f on some 24-row block starting at round 0 with probability at most `q · 2 ^ (-100) + hashError q`, `q = Q + verifierQueries`: 100 bits per oracle call. `BlocksCorrect rows` says that every 24-row block starting at round 0 has its preimage in 16-bit limbs and its last row's output is `keccakPermutation` of its first row's preimage (`KeccakAir.table_block_soundness`).

`stark numQueries logN h` is the STARK over KoalaBear's quartic extension with FRI's parameters `params numQueries`: those of Plonky3's example `prove_prime_field_31` (blowup `2`, folding by arity up to `8` down to a constant, `16` bits of query grinding and `10` bits of batching grinding, Merkle caps of height `3`) with `numQueries` queries. The example's own configuration is `params 87`. The security calculator (CompStark's `CompStark/SecurityCalculator.lean`) reads the STARK's shape (`shape_setup`: 3182 constraints, the identity degree `3 n`, 5274 opened words, no lookups) and certifies each bound in the kernel, for every trace length of `Sized`, at an analysis its search finds, with the MCA bound up to the Johnson radius (`McaBound.uniqueOrJohnson`, which holds by `McaBound.uniqueOrJohnson_holds`). Each query count is the smallest the calculator certifies on all of `2 ^ 12` to `2 ^ 21` rows:

| theorem | queries | analysis | proven bits |
| --- | --- | --- | --- |
| `keccak_soundness_ro` | `203` | `δ = 1/4 - 2 ^ (-11)`, `δ' = 1/4 - 2 ^ (-13)`, loss `2 ^ (-60)` | `100` per oracle call |
| `keccak_soundness` (interactive) | `247` | `δ = 1/4 - 2 ^ (-10)`, `δ' = 1/4 - 2 ^ (-12)`, loss `2 ^ (-16)` | `100` |
| `keccak_soundness_ro_example` (Plonky3's example) | `87` | `δ ≈ 0.2916`, `δ' ≈ 0.2919`, loss `2 ^ (-60)` | `59` per oracle call |

Up to the Johnson radius `1 - √(1/2) ≈ 0.2929` of rate `1/2`, FRI's proximity `δ` goes beyond the unique-decoding radius `1/4`, so a query is worth up to `0.4985` bits instead of `log₂ (4/3) ≈ 0.415`: the `87` queries and `16` bits of grinding of Plonky3's example prove `59` bits per oracle call, where Plonky3 conjectures 100. Beyond the unique-decoding radius the Johnson list size multiplies the out-of-domain, batching and fold terms, so with Plonky3's grinding 100 bits per oracle call stay at the unique-decoding count, `203` queries, limited by the queries' term, `2 ^ (-100.06)`; the out-of-domain term is `2 ^ (-100.95)` on `2 ^ 21` rows, batching `2 ^ (-111.6)`, the largest fold `2 ^ (-102.1)` and constraint folding, which Plonky3 does not grind, `2 ^ (-112.3)`. More grinding, mostly before the batching challenge, buys fewer queries at the cost of prover time: `188` at `24` bits of batching grinding, `173` at `30`. Interactively, without grinding to credit, `247` queries reach 100 bits on `2 ^ 21` rows (`100.07`), limited by the sum of the out-of-domain, batching and query terms. At blowup `4` the calculator's search reaches 100 bits per oracle call with `124` queries; the showcase keeps the example's blowup.

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

At CompStark `fd2cbab` (CompPoly `7596b8e`) on a Ryzen 7 3700X (8 cores, 16 threads), shared with other jobs, all threads, medians of 3 in each of three interleaved rounds, the median of the rounds. Total is trace generation and proof, end to end from the inputs, at the example configuration (87 queries):

| rows | Lean tracegen | Lean prove | Lean total | Plonky3 tracegen | Plonky3 prove | Plonky3 total | Lean / Plonky3 | Lean verify | Plonky3 verify | peak memory Lean / Plonky3 |
|---|---|---|---|---|---|---|---|---|---|---|
| $2^{15}$ | 30 ms | 824 ms | 851 ms | 23 ms | 824 ms | 846 ms | 1.01 | 42 ms | 10 ms | 1.4 GB / 0.7 GB |
| $2^{16}$ | 42 ms | 1.90 s | 1.96 s | 46 ms | 1.85 s | 1.90 s | 1.03 | 44 ms | 11 ms | 2.4 GB / 1.4 GB |
| $2^{17}$ | 92 ms | 3.81 s | 3.93 s | 92 ms | 4.60 s | 4.69 s | 0.84 | 48 ms | 11 ms | 4.4 GB / 2.8 GB |
| $2^{18}$ | 181 ms | 6.46 s | 6.63 s | 182 ms | 11.24 s | 11.42 s | 0.58 | 46 ms | 11 ms | 8.4 GB / 5.5 GB |

On one thread, medians of 3 interleaved rounds of one proof each:

| rows | Lean tracegen | Lean prove | Lean total | Plonky3 tracegen | Plonky3 prove | Plonky3 total | Lean / Plonky3 | Lean verify | Plonky3 verify |
|---|---|---|---|---|---|---|---|---|---|
| $2^{15}$ | 95 ms | 6.21 s | 6.30 s | 159 ms | 4.03 s | 4.19 s | 1.50 | 45 ms | 11 ms |
| $2^{16}$ | 179 ms | 12.16 s | 12.34 s | 323 ms | 7.93 s | 8.25 s | 1.50 | 44 ms | 10 ms |
| $2^{17}$ | 366 ms | 24.14 s | 24.51 s | 630 ms | 15.85 s | 16.48 s | 1.49 | 46 ms | 10 ms |
| $2^{18}$ | 752 ms | 50.03 s | 50.79 s | 1.31 s | 33.62 s | 34.95 s | 1.45 | 51 ms | 10 ms |

On 16 threads, the Lean side is within 3% of Plonky3 end to end at the example configuration on $2^{15}$ and $2^{16}$ rows and faster from $2^{17}$ rows, by 40% at $2^{18}$; on one thread it takes about 1.5 times as long at every size. Clean's trace generation takes about the time of Plonky3's `generate_trace_rows` on 16 threads and 0.6 times it on one. The Lean prover's peak memory is 1.5 to 2 times Plonky3's. The proven configuration (`keccak_soundness_ro`) is the example's with 116 more queries and no other change: on $2^{16}$ rows its proofs take the example's time within the noise, and the Lean verifier takes about 90 ms against Plonky3's 16 ms (45 and 11 ms at the example).

The prover is CompStark's on its Keccak fixture (`CompStarkBench keccak`, Plonky3's `KeccakAir` written directly in CompStark, measured at CompStark `29aaf95` interleaved with the showcase): its proofs from the trace take 1.05 s, 1.74 s, 3.55 s and 6.79 s on $2^{15}$ to $2^{18}$ rows on 16 threads and 6.0 s, 12.3 s, 23.8 s and 48.9 s on one thread, the same as the showcase's within the noise, and its trace generation takes about twice Clean's. The Clean AIR's quotient is the fixture's: Clean writes `x - y` as `x + (-1) * y`, which the lowering turns back into a subtraction (`addExpr`), so that its program has the fixture's instruction mix (36212 instructions, 8941 multiplications, against 36069 and 8742) rather than 43048 instructions with 15777 multiplications; the showcase runs this program as the generated kernel `KeccakShowcase/Kernel.lean`, whose constraints `check` and `kat` verify are the AIR's.

## Tests

`CleanCompStarkTests` proves and verifies Clean-generated traces with CompStark's specification prover over BabyBear: the two-row `SquaresTable` as a STARK (with its knowledge soundness instantiated, also from a calculator certificate), and a range check against a bytes lookup table as a batch. Tampered traces are rejected. `CleanCompStarkTests/Axioms.lean` checks the axioms of the headline theorems.

## Building

Run `lake build` and `lake build CleanCompStarkTests` in this directory, and `lake build keccak_showcase` for the showcase's executable. Point `.lake/packages` at existing checkouts with their builds rather than fetching and building Mathlib again.
