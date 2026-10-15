# Verifier challenges in Clean 2

A design proposal. Challenges are ordinary variables in ordinary circuits. The proof system
provides one thing, a `challenge` operation; protocols that use challenges (logUp, bus balance,
lookups, grand products) are gadgets, specified and proved at the circuit layer, on any backend,
with the challenge in the native field or in an extension.

```lean
-- logUp row: add m / (α - v) to the running sum. An ordinary gadget, with a pointwise spec.
main | (((v, m), acc), α) => do
  let vK ← karith .embed v
  let δ ← karith .sub (α, vK)
  let d ← karith .inv δ                            -- d * (α - v) = 1
  let md ← karith .smul (m, d)
  Circuit.assumeRareHonest (event kty v α)         -- the honest prover is stuck if α = v
  karith .add (acc, md)                            -- spec: out = acc + m / (α - v)

-- boundary: the final sum is 0 at α  ⇒  ∑ m / (X - v) ≡ 0 in K(X), up to rare α
main | ((c, x), α) => do
  karith .assertZero x
  Circuit.assumeRare (event kty d R c α)           -- x ≙[α] R c, R c ≢ 0, but α is a root

-- the protocol: commit to the input, draw the challenge, check. An ordinary `Impl` of the
-- contract, which mentions no challenge.
main x := do
  let α ← challenge (toElements x)
  check (x, α)
```

The end-to-end guarantee, for each protocol (`Protocol.soundness_error`, `completeness_error`):
**fix the committed input; the values of the challenge at which a false statement is accepted,
or the honest prover fails, are at most `errorBound` / `honestErrorBound` many**. These are
numbers of bad values in the challenge field `K`; the soundness error is `errorBound / |K|`.

## What ships

| Layer | What | Size |
|---|---|---|
| Core (`Core/Circuit`, `Formal`, `Measure`) | `RareEvent`; two operations `rare` / `rareHonest`; their semantics | ~250 lines |
| Core tactics (`Core/Spatial`) | leaf search by reachability (was exponential); pairs | ~70 lines |
| Backends | one native op each: R1CS `challenge` (gnark's `Commit`), Plonkish `challenge` (a phase) | ~80 lines |
| `Phase` | the phase contract `Impl.Phased`, `Impl.NoEvents`; tactics `phased`, `no_events` | 500 |
| `Basic` | `errorBound`, `honestErrorBound` (measures); `Impl.soundness_error`, `completeness_error` | 300 |
| `Protocol` | `Challenge.interface`, `withChallenge`, `Protocol.impl` and its two error theorems | 190 |
| `Field`, `Extension` | the challenge field: `KArith` vocabulary; `K = F`; any extension from a basis | 590 |
| `Symbolic`, `AssertIdentity` | `x ≙[α] R`; the boundary, the only soundness cost | 300 |
| `Fractions` | partial fractions, bus balance, logUp, multisets as roots | 210 |
| `LogUp`, `GrandProduct` | row gadgets, running sums/products, `Balance`, `Lookup`, `PermutationCheck` | 740 |
| `Examples` | the stack on any backend and field; closed on R1CS (`F`, extension), Plonkish | 450 |

Circuits that use no challenge are untouched: every existing gadget, backend and measure builds
unchanged, and `NoEvents` is all they need (only when a challenge-using parent calls them).

## Results

| Protocol | Boundary identity | Soundness error | Completeness error |
|---|---|---|---|
| `Balance` (bus balance, signed multiplicities) | `∑ m / (X - v) ≡ 0` | `n` | `n` |
| `Lookup` (table `t`, multiplicities `μ`, lookups `f`) | `∑ μ / (X - t) - ∑ 1 / (X - f) ≡ 0` | `n + l` | `n + l` |
| `PermutationCheck` (grand product) | `∏ (X - a) / (X - b) - 1 ≡ 0` | `n` | `n` |
| `LookupAndPermutation` (one shared challenge) | both | `n + l + k` | `n + l + k` |

Closed end to end (`Examples.lean`), with the same gadgets and the same proofs:

- `lookupAndPermutationProtocolR1CS_error`: R1CS, challenge in `F`;
- `lookupAndPermutationProtocolExtR1CS_error`: R1CS, challenge in an extension `K` of degree `d`,
  drawn as `d` native challenges, bounds counted in `K`;
- `lookupAndPermutationProtocolPlonkish_error`: Plonkish, challenge in `F`.

## What a gadget author proves

1. **Pointwise specs, no probability.** A row's spec is `out = acc + m / (α - v)`. Its
   constraint `d * (α - v) = 1` already rules out `α = v`, so it costs no soundness.
2. **One symbolic step, at the boundary.** The final value stands for a rational function of
   committed values (`x ≙[α] R`, carried through `+ - * /`, sums, products by `Symbolic`). That
   `R ≡ 0` means what the protocol claims is one lemma about rational functions (`Fractions`).
   Its degree bound is static (`NumDegLE`).
3. **The phase contract**, by `phased [impl, event]`: every rare event depends only on what the
   interface declares committed (`Interface.Phases`). One line per gadget.
4. **The errors**, by `measure`: `Impl.Measured errorBound`, like cost, from the parts.

## Design decisions

- **The proof system provides challenges, nothing else.** A backend's `challenge` op is a fresh
  cell that constrains nothing; what the backend must guarantee is that its value is sampled
  uniformly from `K` after the listed variables are committed. Everything else (which values
  are committed, which protocol, which identity) is circuit-level and proved.
- **Rare events instead of probabilistic semantics.** A gadget that needs "`α` is not a root of
  this nonzero polynomial" *assumes* it, as an operation that is not a constraint. The verifier
  never checks it (`ConstraintsHold` ignores it); soundness proofs may use it. Counting is done
  once (`Impl.soundness_error`): a rare event is a predicate on committed values and the
  challenge that holds at no more than `bound` challenges, whatever the committed values.
- **Soundness and completeness events are separate.** Division is a completeness cost (the
  honest prover is stuck at `α = v`), the boundary a soundness cost. Both are measures.
- **Committed values must be fixed first.** A cheating prover chooses everything filled after the
  challenge as arbitrary functions of it. So a rare event may only depend on committed values,
  and constraints mentioning a challenge are never read as identities in `F[X]`
  (`NaiveSymbolic`: `w * w = X` has no polynomial solution, but holds at every square). The phase
  contract makes this compositional: each interface says which part of its input is committed
  and which is the challenge, and a parent proves its contract from its children's. All cells
  outside the committed ones are quantified after the challenge, which over-approximates the
  real protocol.
- **The challenge field is a synthetic type.** `K` is laid out in native cells by a
  `kty : CType F K`, which must be faithful (layouts and values are in bijection), so that
  counting bad layouts counts bad values of `K`. The protocols are written once against the
  `KArith` vocabulary (embed, `+ - *`, scale by a native value, invert, assert zero,
  constants) and instantiated with `KArith.native` (`K = F`) or `KArith.ofBasis b` (any
  extension with a basis `b`; multiplication by structure constants, `d²` products).
- **Row-level gadgets, not whole-expression identities.** An earlier design built the whole
  rational expression and asserted it at once (`Clean2/Challenge/Variants/` at `df379ba0`).
  Rows compose like any gadget and keep the symbolic reasoning in one place.

## Open questions

- **Several rounds.** A protocol draws one challenge after committing its input. Interleaving
  (commit, challenge, commit, challenge) needs the events of a closed protocol to be discharged
  into a probability, or a phase contract with several phases.
- **Computable extension arithmetic.** `KArith.ofBasis` is generic and noncomputable (it reads
  coordinates through `Basis.equivFun`). Witness generation needs concrete structure constants:
  a `KArith` for binomial extensions `F[X]/(X^d - W)` (BabyBear, Goldilocks), with fewer
  multiplications.
- **What a backend commits to.** The `challenge` op lists the variables it is drawn after; the
  backend's soundness has to match that list to its commitment scheme (gnark's `Commit`, Halo2's
  phases). That obligation is stated in prose, not in Lean.
- **Fiat–Shamir** is out of scope: the model is the interactive protocol.
