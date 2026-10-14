# Verifier challenges in Clean 2

Experimental. Challenges in ordinary circuits, with symbolic reasoning for users and the soundness
error tracked by the framework.

## The model

- **A challenge is an ordinary variable.** A gadget that needs one takes it as an input, like any
  other. Circuits that do not use challenges are unchanged.
- **Rare events** (`RareEvent`, `Circuit.assumeRare`, in `Core/Circuit.lean`). A circuit may assume
  that a rare event does not happen: a predicate on *committed* variables and a challenge that holds
  at no more than `bound` challenges, whatever the committed values. Soundness proofs may use the
  assumption (`SoundnessHold`); the verifier does not check it (`ConstraintsHold` ignores it).
  Subcircuits carry their events up. Normal circuits emit none, and their proofs never see them.
- **The error is a measure** (`errorBound`). `Measure` now also measures rare events
  (`rare`, default `0`, so existing measures are unaffected). A parent reads its error off its
  children's `Measured errorBound` instances, like cost.
- **One theorem** (`Impl.soundness_error`): fix the committed cells (the inputs, and what every
  event depends on). The challenges at which the real constraints hold but the spec fails are at
  most `errorBound` many. For a circuit without events, that is ordinary soundness.

## What users write

`Identity.interface e` is a functionality like `arith`: its input is `k` committed values and the
challenge, its spec is the **symbolic** identity `sym x e = 0`, an equation in `K⟮X⟯`. The
challenge does not appear in the spec. `e : RExpr F k` is any rational expression in the committed
values (`leaf i`), constants, and the challenge `X`, with `+ - * /`, `sum`, `prod`, `^`.

`Identity.impl` implements it on any backend with `Arith`: evaluate `e` at `α` (a witness and a
`mulEq` per division), assert zero, assume the rare event that `α` is a root of a divisor or of a
nonzero numerator. Bound: `degN e + divDeg e`, static.

| Protocol | Expression | Error (bad challenges) | Completeness needs | User proof |
|---|---|---|---|---|
| `ZeroCheck` | `∑ c i X^i` | `n - 1` | nothing | coefficients of `0` |
| `Permutation` | `∏ (X - a i) - ∏ (X - b i)` | `n` | nothing | equal roots |
| `PermutationQuotient` | `∏ (X - a i)/(X - b i) - 1` | `2n` | `α ∉ b` | equal roots |
| `PermutationRunning` | hand-written running product, own event | `n` | `α ∉ b` | pointwise loop proof |
| `LogUp` | `∑ m i/(X - t i) - ∑ 1/(X - f j)` | `≈ 2(n + l)` | `α ∉ t, f` | partial fractions |
| `PermutationChain` | two `Permutation`s, one challenge | `2n` (R1CS, via the measure) | — | transitivity |

`PermutationQuotient` and `PermutationRunning` implement the same interface: same spec, different
circuits, different error. The generic identity pays for every root of a divisor; the
hand-written argument cross-multiplies and does not.

## Findings

- **Phases are enforced by the proof obligation, not by types.** An event may only depend on
  committed values. A gadget that feeds a value chosen after the challenge into an identity cannot
  state the event it needs. Challenge-dependent values belong *in the expression* (e.g. a random
  linear combination `a + X * b`), not in a variable.
- **Constraints are never read symbolically, only expressions.** `NaiveSymbolic.lean`:
  `w * w = X` has no polynomial solution but is satisfied at every square.
- **Division costs error.** A division by `d` makes the roots of `d` bad. With no division, the
  identity is complete at every challenge.
- **User proofs are short** once `simp` knows the meanings: the permutation and logUp gadgets'
  soundness and completeness are one to three lines each, on top of one math lemma. What helped:
  `simp` lemmas for `sym`/`evalAt`/`NZ`/`Good` through `+ - * /`, `sum`, `prod`, `^`;
  `RatFunc.X_sub_C_ne_zero` and `prod_X_sub_C_ne_zero` (so `simp` discharges divisor side
  conditions and `div_eq_one_iff_eq`); right-nested leaf vectors (`t ++ (m ++ f)`), which `simp`
  indexes into without arithmetic on `Fin`.

## Not done

- **The phase hypothesis of `soundness_error` is not compositional yet.** It asks that every event
  of the top-level circuit depends on committed cells and the given challenge. That should be a
  per-`Impl` contract, like `Measured`.
- **One challenge.** Several challenges, sampled in rounds after cells that depend on earlier
  ones, need a game-based statement.
- **No `challenge` operation.** Sampling, transcripts and Fiat–Shamir are out of scope; the top
  level designates the challenge variable.
- **Base field only.** Extension-field challenges are not modelled.
