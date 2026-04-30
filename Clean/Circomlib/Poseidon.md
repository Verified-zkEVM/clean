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
  *Poseidon: A New Hash Function for Zero-Knowledge Proof Systems*.
  USENIX Security '21. <https://eprint.iacr.org/2019/458>
- iden3 circomlibjs, `src/poseidon_reference.js` (the reference JS
  implementation used as the output oracle for test-vector cross-checks).
  <https://github.com/iden3/circomlibjs/blob/main/src/poseidon_reference.js>

The constants `C_t*`, `M_t*` are copied verbatim from circomlib's
`poseidon_constants.circom`.

## 2. Cross-check against circomlibjs

To guard against transcription errors in the constants and the round schedule,
the spec file includes test vectors from circomlibjs:

| Arity | Spec        | Test vectors (inputs)                              |
|-------|-------------|----------------------------------------------------|
| 1     | `poseidon1` | `1`, `0`, `123`                                    |
| 2     | `poseidon2` | `[1, 2]`                                           |
| 3     | `poseidon3` | `[1, 0, 0]`, `[0, 0, 0]`                           |
| 4     | `poseidon4` | `[1, 2, 3, 4]`                                     |

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
`circuit_norm` + a few-line tactic script:

| Component                      | `main` body                                        | Spec                                                     |
|--------------------------------|----------------------------------------------------|----------------------------------------------------------|
| `Sigma.circuit`                | `in2, in4, out` witnesses                          | `output = input ^ 5`                                     |
| `Ark_t2.circuit c0 c1`         | two `<==` constraints                              | `out[i] = in[i] + c_i`                                   |
| `Mix_t2.circuit m00..m11`      | 2x2 matrix multiply                                | `out = M * in`                                           |
| `MixS_t2.circuit s0 s1 s2`     | sparse matrix multiply                             | `out[0] = s0*in[0] + s1*in[1]`, `out[1] = in[1] + in[0]*s2` |
| `FullRound_t2.circuit ...`     | two inlined `Sigma` + `ARK` + `MIX`                | `output = M * (sbox(input) + c)`                          |
| `PartialRoundOpt_t2.circuit ...`| one inlined `Sigma` + `ARK_first` + `MixS`         | `out[0] = s0*(x^5+c0) + s1*in[1]`, `out[1] = in[1] + (x^5+c0)*s2` |

These are stated generically over any prime `p` (via `variable {p : ℕ}
[Fact p.Prime]`), so they don't depend on BN254-specific reasoning.

## 5. Composing the components into Poseidon1

The top-level `Poseidon1.main` circuit is specialised to `F BN254_PRIME` and
composed of 6 phases:

```
state := [0, input]                      -- initial
state ← Ark_t2.main        C[0..1]       -- inline
state ← applyFullRounds1                 -- Circuit.foldl over FullRound_t2.circuit, C[2..7]
state ← transitionRound                  -- inline: SBOX → ARK(C[8..9]) → MIX(P)
state ← applyPartialRoundsOpt            -- Circuit.foldl over PartialRoundOpt_t2.circuit, C[10..65]
state ← applyFullRounds2                 -- Circuit.foldl over FullRound_t2.circuit, C[66..71]
state ← finalRound                       -- inline: SBOX → MIX(M)
return state[0]
```

Two composition styles appear here:

- **Inline** (`Ark_t2.main`, `transitionRound`, `finalRound`): the inner
  `Circuit`'s constraints are spliced directly into `main`'s operations.
- **Foldl subcircuits** (`applyFullRounds{1,2}`, `applyPartialRoundsOpt`):
  each iteration calls the corresponding `FormalCircuit` as a subcircuit. This
  is what `Circuit.foldl` gives us, and it mirrors the circomlib loop
  structure. It also keeps the per-round witness accounting tractable via the
  `ConstantLength` / `ConstantOutput` instances.

### Soundness composition (`poseidon1_soundness`)

The proof does not try to reduce the whole bind chain with `circuit_norm` —
that would unfold the 56 partial rounds and overload elaboration. Instead it
proves one **phase-level "bridge" lemma** per composition block and then
chains them:

| Lemma                         | From                         | Conclusion                               |
|-------------------------------|------------------------------|------------------------------------------|
| `ark_bridge`                  | initial ARK constraints      | `Specs.Poseidon.ark C_t2 0 [0,input] = [env.get i0, env.get (i0+1)]` |
| `applyFullRounds1_spec`       | foldl constraints + per-round bridge `fullRound_spec_to_fullRoundOpt` | `(output).map eval = fullRoundsOpt_t2 C_t2 M_t2 3 2 (state.map eval)` |
| `transition_bridge` / `transition_bridge_p1` | transition-round constraints | `[env.get (i0+40), env.get (i0+41)] = mix P (ark C 8 (sbox_full ...))` |
| `applyPartialRoundsOpt_spec`  | foldl constraints + `partialRound_circuit_spec_to_opt` + `partialRounds_induction` | `(output).map eval = partialRoundsOpt_t2 C_t2 S_t2 56 10 0 (state.map eval)` |
| `applyFullRounds2_spec`       | foldl constraints + per-round bridge | `(output).map eval = fullRoundsOpt_t2 C_t2 M_t2 3 66 (state.map eval)` |
| `final_round_bridge` / `final_round_bridge_p1` | final-round constraints | `[env.get (i0+414), env.get (i0+415)] = mix M (sbox_full ...)` |

A few supporting details worth flagging:

- **Abstract foldl offsets.** `applyFullRounds1_localLength` etc. and the
  `_output` lemmas let the soundness proof advance through the bind chain
  *without* unfolding each foldl body. Concretely, `main_output_eq` shows
  `(main input_var).output i0 = var ⟨i0 + 414⟩` using only these targeted
  lemmas — no `circuit_norm` — so inner bodies stay abstract.
- **`partialRounds_induction`.** Because 56 iterations can't be unrolled
  by `simp`, the partial-rounds phase is handled by a dedicated induction
  that mirrors the recursion of `partialRoundsOpt_t2`: given per-index
  circuit specs, it concludes the full-phase spec.
- **BN254 constants stay opaque.** `partialRoundConstants` is marked
  `irreducible` mid-file so the kernel doesn't try to evaluate a 56-element
  vector of field elements during typechecking. `m00..m11`, `p00..p11` are
  kept as named definitions and factored through `mix_t2_eq`, `mix_P_t2_eq`,
  `mixS_t2_eq`.
- **`transition_bridge_p1` / `final_round_bridge_p1`.** These absorb the raw
  bind-decomposition + offset arithmetic so the final `rw` chain in
  `poseidon1_soundness` can stay compact (and the narrow simp-set doesn't
  have to deal with hypotheses containing heavy proof terms).

The final step of `poseidon1_soundness` reduces the goal to a 2-element vector
projection and performs the `rw` chain in reverse spec order:

```lean
show (#v[env.get (i0 + 414), env.get (i0 + 415)] : Vector (F BN254_PRIME) 2)[0] = _
rw [hb5, hs4, hs3, hb2, hs1, ← hb0]
rfl
```

That is: bridge back through `finalRound → fullRounds2 → partialRounds →
transition → fullRounds1 → initial ARK`, which is exactly the definition of
`poseidon1Opt` (see `Clean/Specs/PoseidonOptimized.lean`, `poseidon1Opt`).

### Completeness

Completeness is easy once every subcircuit has its own `completeness` and the
`Assumptions` are trivially `True`. The whole proof is:

```lean
completeness := by
  circuit_proof_start [main, applyFullRounds1, applyFullRounds2, applyPartialRoundsOpt,
                       Ark_t2.main, transitionRound, finalRound, Sigma.main,
                       FullRound_t2.circuit, FullRound_t2.main,
                       PartialRoundOpt_t2.circuit, PartialRoundOpt_t2.main]
  simp_all +arith
```

`circuit_proof_start` unfolds the phase definitions, subcircuit completeness
reduces to each `FormalCircuit`'s `Assumptions` (all `True`), and the
remaining arithmetic/goal structure closes via `simp_all +arith`.

## What the final theorem says

```lean
def circuit : FormalCircuit (F BN254_PRIME) field field where
  ...
  Assumptions _ := True
  Spec (input : F BN254_PRIME) (output : F BN254_PRIME) :=
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
  expected witness satisfies the constraints.
- The component proofs cover the S-box, ARK, MDS mix, sparse mix, full rounds,
  partial rounds, and the complete arity-1 composition.

Not yet formally proved:

- The translation from the original `poseidon.circom` source to this Clean
  model is not mechanically checked; it is a direct hand model of the same
  optimised structure.
- `poseidon1Opt = poseidon1` is tested on representative inputs, but not
  proven for all field elements.
- The theorem currently relies on the BN254 primality `sorry`, which can be
  closed independently with a Pratt/Lucas certificate.

## Open items

- `instance : Fact (Nat.Prime BN254_PRIME)` is declared with `by sorry`
  (see top of `namespace Poseidon1`). Closing it requires a Pratt/Lucas
  certificate; Mathlib's `lucas_primality` is the tool.
- `poseidon1Opt = poseidon1` is checked only via `native_decide` on a handful
  of inputs, not proven.
- Arities 2, 3, 4 have specs and test vectors but no circuit/formal-proof.
