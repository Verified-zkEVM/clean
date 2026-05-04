# Poseidon1 proof: explanation

This note walks through the structure of the Poseidon arity-1 (t=2) soundness
and completeness proof for BN254, as implemented in `Poseidon.lean` against the
specs in `Clean/Specs/Poseidon.lean` and `Clean/Specs/PoseidonOptimized.lean`.

## 1. Start from a non-optimised output spec

`Clean/Specs/Poseidon.lean` defines a simple, **non-optimised** Poseidon
permutation, parameterised by `t`, used as an output-level reference spec:

- S-box `sigma(x) = x^5` (BN254)
- `ark`: add the round-constants slice `C[offset..offset+t]`
- `mix`: multiply by the full MDS matrix `M` (t×t)
- `fullRoundCircom`: `sbox_full → ark → mix`
- `partialRoundCircom`: `sbox` on element 0 only, `ark` on element 0 only, `mix` (full M)
- `poseidon1..poseidon4`: the complete hash at arities t=2..5, with the round
  schedule `ARK_initial → 4 full → nP partial → 3 full → (SBOX → MIX)`

This file is not a line-by-line model of either the optimised circom circuit
or the current circomlibjs reference implementation. In particular,
`poseidon_reference.js` uses the conventional add-round-constants-before-S-box
round order inside its loop. The role of `Clean/Specs/Poseidon.lean` is to give
a compact, full-MDS, output-compatible reference spec, checked against
circomlibjs vectors.

References:

- Grassi, Khovratovich, Rechberger, Roy, Schofnegger.
  _Poseidon: A New Hash Function for Zero-Knowledge Proof Systems_.
  USENIX Security '21. <https://eprint.iacr.org/2019/458>
- iden3 circomlibjs, `src/poseidon_reference.js` (the reference JS
  implementation used as the output oracle for test-vector cross-checks).
  <https://github.com/iden3/circomlibjs/blob/main/src/poseidon_reference.js>

The constants `C_t*`, `M_t*` are copied verbatim from circomlib's
`poseidon_constants.circom`.

## 2. Cross-check against circomlibjs

To guard against transcription errors in the constants and the round schedule,
the spec file includes test vectors from circomlibjs:

| Arity | Spec        | Test vectors (inputs)    |
| ----- | ----------- | ------------------------ |
| 1     | `poseidon1` | `1`, `0`, `123`          |
| 2     | `poseidon2` | `[1, 2]`                 |
| 3     | `poseidon3` | `[1, 0, 0]`, `[0, 0, 0]` |
| 4     | `poseidon4` | `[1, 2, 3, 4]`           |

Each test is an `example : poseidon_k inputs = known_hash := by native_decide`
(see `Clean/Specs/Poseidon.lean`, bottom). 7 vectors total.

## 3. Specialise to the circomlib-optimised variant

`Clean/Specs/PoseidonOptimized.lean` defines the variant corresponding to
circomlib's optimised `circuits/poseidon.circom` schedule (i.e.
`poseidon.circom` uses the optimised form — `Clean/Specs/Poseidon.lean` is
not a structural model of `poseidon.circom`, only of the intended output):

- A **pre-sparse** matrix `P` is used at the transition from the first full
  rounds into the partial rounds.
- The partial rounds use **sparse** mix matrices (`mixS`) that require only
  3 non-trivial constants per round instead of `t^2`.
- `poseidon1Opt`, `poseidon2Opt`, `poseidon3Opt` implement this schedule.

Mathematically this should be equivalent to the standard variant (it's the
standard "Poseidon optimisation trick" used by circomlib/snarkjs). The Lean
definition is a direct hand model of the optimised arity-1 circuit structure
that Clean proves constraint-by-constraint.

Reference:

- iden3 circomlib, `circuits/poseidon.circom` (the optimised circom circuit
  whose arity-1 structure this file hand-models).
  <https://github.com/iden3/circomlib/blob/master/circuits/poseidon.circom>

Equivalence is established empirically via `native_decide` test vectors in the
same file:

- `poseidon1Opt = poseidon1` at inputs `1`, `0`, `123`, `BN254_PRIME - 1`
- `poseidon2Opt = poseidon2` at `[1,2]`, `[0,0]`, `[1,0]`, `[0,1]`, `[3,4]`,
  `[12345, 67890]`, `[BN254_PRIME-1, 1]` — plus one match against the known
  circomlibjs hash.
- `poseidon3Opt = poseidon3` at `[1,0,0]`, `[0,0,0]`, `[1,2,3]` — plus two
  matches against known circomlibjs hashes.

(There is no formal proof of `poseidon1Opt = poseidon1`; it's validated only
against this test set.)

## 4. Soundness and completeness of each component circuit

`Clean/Circomlib/Poseidon.lean` introduces a `FormalCircuit` for every
Poseidon building block and discharges its `soundness` + `completeness`
obligations in isolation. Each of these is small enough to prove with
`circuit_proof_start` + a few-line tactic script:

| Component                          | Spec                                                                                                        |
| ---------------------------------- | ----------------------------------------------------------------------------------------------------------- |
| `Sigma.circuit`                    | `output = input ^ 5`                                                                                        |
| `InitialArk.circuit`               | `output = Specs.Poseidon.ark C_t2 0 #v[0, input]`                                                           |
| `FullRound_t2.circuit C M offset`  | `output = Specs.PoseidonOptimized.fullRoundOpt_t2 C M offset.val input`                                     |
| `ApplyFullRounds.circuit offset h` | `output = Specs.PoseidonOptimized.fullRoundsOpt_t2 C_t2 M_t2 3 offset input`                                |
| `PartialRoundOpt_t2.circuit round` | `output = Specs.PoseidonOptimized.partialRoundOpt_t2 C_t2 S_t2 (10 + round.val) round.val input round.isLt` |
| `ApplyPartialRoundsOpt.circuit`    | `output = Specs.PoseidonOptimized.partialRoundsOpt_t2 C_t2 S_t2 56 10 0 input ...`                          |

## 5. Composing the components into Poseidon1

The top-level `Poseidon1.main` circuit is composed of 6 phases:

```
let state ← InitialArk.circuit input
let state ← ApplyFullRounds.circuit 2 (by omega) state
let state ← FullRound_t2.circuit C_t2 P_t2 ⟨8, by omega⟩ state
let state ← ApplyPartialRoundsOpt.circuit state
let state ← ApplyFullRounds.circuit 66 (by omega) state
let state ← FullRound_t2.circuit (.replicate 72 0) M_t2 ⟨0, by omega⟩ state
return state[0]
```

## What the final theorem says

```lean
def circuit : FormalCircuit F field field where
  ...
  Spec (input : F) (output : F) :=
    output = Specs.PoseidonOptimized.poseidon1Opt input
  soundness := ...
  completeness := ...
```

So the Clean circuit model exactly realises `poseidon1Opt`. That optimised
spec agrees with `poseidon1` and with circomlibjs on every tested input.
Chaining these gives a high (though not fully formal) degree of confidence
that the arity-1 circomlib Poseidon circuit computes the specified hash.

## What is formally proved?

Formally proved:

- The Clean model `Poseidon1.circuit` is sound with respect to
  `Specs.PoseidonOptimized.poseidon1Opt`: any satisfying assignment produces
  the specified output.
- The Clean model `Poseidon1.circuit` is complete: for every input, the
  honest-prover witness satisfies the constraints.
- The component proofs cover the S-box, initial ARK, full rounds, folded full
  rounds, optimized partial rounds, folded partial rounds, and the complete
  arity-1 composition.

Not yet formally proved:

- The translation from the original `poseidon.circom` source to this Clean
  model is not mechanically checked; it is a direct hand model of the same
  optimised structure.
- `poseidon1Opt = poseidon1` is tested on representative inputs, but not
  proven for all field elements.
- The BN254 primality instance is still declared with `sorry`; it can be closed
  independently with a Pratt/Lucas certificate.

## Open items

- `instance : Fact (Nat.Prime BN254_PRIME)` is declared with `by sorry`
  (near the top of `Clean/Circomlib/Poseidon.lean`). Closing it requires a Pratt/Lucas
  certificate; Mathlib's `lucas_primality` is the tool.
- `poseidon1Opt = poseidon1` is checked only via `native_decide` on a handful
  of inputs, not proven.
- Arities 2, 3, 4 have specs and test vectors but no circuit/formal-proof.
