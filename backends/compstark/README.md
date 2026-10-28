# CompStark backend

Proves Clean ensembles with [CompStark](https://github.com/zksecurity/CompStark), a STARK prover and verifier in Lean that is byte-compatible with Plonky3, and connects CompStark's knowledge soundness to Clean's soundness theorems.

This is a separate Lake package, so that Clean does not depend on CompStark. It requires Clean (`../..`) and CompStark; their dependencies resolve to the same revisions.

## Translation

- `CleanCompStark.Fields`: Clean's `F p = ZMod p` and CompStark's Montgomery field `FastField p` are isomorphic (`montEquiv`, `koalaBear`, `babyBear`). The translation is generic over a ring isomorphism `e : F ≃+* K` to any CompStark base field.
- `CleanCompStark.Air`: a component becomes one AIR (`toAir`), laid out as the Plonky3 backend does. The fixed columns, the fixed cells of the component's generation, are the preprocessed trace; the trace commits the other cells of the row's own input and the witnesses; a two-row component's next-row cells read the next row and its selector cells are Plonky3's selectors. Every constraint is split by `Backends.gateConstraint` and becomes its body times its gate's selector (`when_first_row`, `when_last_row`, `when_transition`). Every interaction becomes a global lookup on the bus named after its channel, with the negated multiplicity and weight `0`. `toRows` reads a trace back as Clean rows, `toTrace` drops the fixed and window cells of Clean rows.
- `CleanCompStark.Batch`: an ensemble becomes a batch with one instance per component (`toBatchSetup`).

## Theorems

- Lowering is correct (`eval_constraint_iff`): a constraint holds on a row read off the trace if and only if its lowered form vanishes on the trace's row. CompStark's selectors are scaled (`n` on the first row, `n ω` on the last, `ωⁱ - ω⁻¹` on transitions); they vanish exactly where Clean's 0/1 selectors do (`selectors_eq_zero_iff`).
- One component (`table_of_satisfied`): a trace satisfying the AIR of a `bridgeable` component is a table of the component, with the prover data of its rows, the fixed columns and the windows of its rows, whose constraints hold.
- An ensemble (`statement_of_satisfied`): traces satisfying a batch that proves an `EnsembleBridgeable` ensemble are a witness of `Ensemble.Statement`: the constraints hold and every channel balances, since its bus does (`rowBalance`; packing and bus numbering in `CleanCompStark.Buses`).
- Knowledge soundness, for any bridgeable component or ensemble and any STARK or batch proving it, whatever its FRI parameters and grinding: unless what the circuit proves holds of the rows read off some trace close to the committed one, the verifier accepts with probability at most `2 ^ (-bits)` for the bits CompStark's security calculator certifies in the kernel for the configuration (`knowledgeSoundness_of_secure`, and per oracle call in the random-oracle model `knowledgeSoundness_ro_of_secureRo`, for one component; `batchKnowledgeSoundness_of_secure` and `batchKnowledgeSoundness_ro_of_secureRo` for an ensemble). In terms of CompStark's knowledge and round errors at any radii, they are `knowledgeSoundness_of_tableSound`, `knowledgeSoundness_ro_of_tableSound`, `batchKnowledgeSoundness_of_witnessSound`, `batchKnowledgeSoundness_ro_of_witnessSound` and `batchKnowledgeSoundness_of_soundness`.
- `CleanCompStark.KeccakAir.knowledgeSoundness`: for a STARK proving Plonky3's Keccak-f AIR over KoalaBear, every 24-row block starting at round 0 of such rows computes Keccak-f.

The side conditions are explicit: `bridgeable` (no legacy lookups, gated constraints, cells within the row, fixed columns within the row's own input) is a decidable check; `Fits` asks for a trace domain in the two-adic subgroup, `u64` row indices and the height of a preallocated or standalone component; `EnsembleBridgeable` asks for a verifier without interactions and channels told apart by their names; the number of interactions must stay below the characteristic.

## Tests

`CleanCompStarkTests` proves and verifies Clean-generated traces with CompStark's specification prover over BabyBear: the two-row `SquaresTable` as a STARK (with its knowledge soundness instantiated, also from a calculator certificate), and a range check against a bytes lookup table as a batch. Tampered traces are rejected.

## Building

Run `lake build` and `lake build CleanCompStarkTests` in this directory. Point `.lake/packages` at existing checkouts with their builds rather than fetching and building Mathlib again.
