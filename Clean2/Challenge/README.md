# Verifier challenges in Clean 2

Experimental. Challenges in ordinary circuits: users write row-level gadgets with pointwise specs,
reason symbolically only where a protocol concludes, and the framework tracks both the soundness
and the completeness error.

## The idea

```lean
-- logUp row: add m / (α - v) to the running sum
main | (((v, m), acc), α) => do
  let d ← inverse (α - v)              -- d * (α - v) = 1
  return acc + m * d                   -- spec: out = acc + m / (α - v)

-- boundary: the final sum is 0 at α  ⇒  ∑ m / (X - v) ≡ 0 in F(X), up to rare α
main | ((c, acc), α) => assertIdentity acc
```

- **Values computed after the challenge can stand for a rational function** of committed values
  and `X` (`x ≙[α] R`, `Symbolic.lean`). Gadgets keep ordinary pointwise specs; generic lemmas
  carry meanings through `+ - * /`, sums and products.
- **The boundary** (`AssertIdentity`) turns "`x = 0` at `α`" into "`R ≡ 0`". That step assumes a
  soundness rare event: `R ≢ 0` but `α` is a root of its numerator, at most `deg` challenges.
  It is the only soundness cost. Rows cost no soundness: `d * (α - v) = 1` already excludes `α = v`.
- **Division costs completeness**: the honest prover is stuck at `α = v`, a completeness rare event.
- **Both errors are measures** (`errorBound`, `honestErrorBound`): they add up like cost.
  `Impl.soundness_error` and `Impl.completeness_error` turn them into bounds on bad challenges, once.
- **The proof system only provides challenges.** Protocols like logUp are specified and proved at
  the circuit layer.

## Core change (`Core/Circuit.lean`, `Core/Formal.lean`, `Core/Measure.lean`)

Two circuit-level operations, `rare` and `rareHonest`: assumptions that a rare event does not
happen, for soundness and for completeness. The verifier never checks them (`ConstraintsHold`
ignores them); `SoundnessHold` / `HonestCompleteness` may use them; subcircuits carry them up;
`Measure` measures them (default `0`). Every existing gadget, backend and measure builds unchanged.

## Files

| File | What |
|---|---|
| `Basic.lean` | the two error measures, `soundness_error`, `completeness_error` |
| `Symbolic.lean` | `x ≙[α] R`, its algebra, the boundary lemma, static degree bounds (`NumDegLE`) |
| `AssertIdentity.lean` | the boundary gadget: spec `R c = 0`, soundness error `d` |
| `Fractions.lean` | the symbolic arguments: partial fractions, bus balance, logUp, multisets as roots |
| `LogUpRow.lean` | `LogUpRow`, `LogUpSum`, `Balance` (bus balance), `Lookup` (table + lookups) |
| `GrandProductRow.lean` | `ProductRow`, `ProductLoop`, `PermutationRow` |
| `Examples.lean` | `LookupAndPermutation` on one challenge; both errors on R1CS from the parts |
| `NaiveSymbolic.lean` | why constraints are never read symbolically |
| `Variants/` | whole-expression identities (`Identity`, `RExpr`), and a hand-written check with its own event |

## Protocols (row-level)

| Protocol | Rows | Boundary identity | Soundness error | Completeness error |
|---|---|---|---|---|
| `Balance` | `acc + m / (α - v)` | `∑ m / (X - v) ≡ 0` | `n` | `n` |
| `Lookup` | two sums | `∑ μ / (X - t) - ∑ 1 / (X - f) ≡ 0` | `n + l` | `n + l` |
| `PermutationRow` | `acc * (α - a) / (α - b)` | `∏ (X - a) / (X - b) - 1 ≡ 0` | `n` | `n` |
| `LookupAndPermutation` | both, one challenge | both | `n + l + k` | `n + l + k` |

User proofs: pointwise algebra for the rows (no probability), one symbolic lemma for the
conclusion (`Fractions`), and a degree bound for the boundary (`NumDegLE`).

## Not done yet

- **Phase hypothesis.** `soundness_error` / `completeness_error` ask that every event depends on
  committed cells and the given challenge. That should be a per-`Impl` contract, like `Measured`,
  discharged by the spatial machinery once challenges are a backend operation.
- **A challenge operation in the backends**, recording the phase boundary in the heap state; named,
  shared challenges across rounds and across tables (a table's final sum as a boundary output, the
  ensemble asserting the total).
- **Extension-field challenges.**
