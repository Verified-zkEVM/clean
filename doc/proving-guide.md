# Proof Finding Guide

This document describes certain well-trodden paths for finding proofs. These are just suggestions that might work.

## Opening moves

* Start a soundness or completeness proof with `circuit_proof_start`.
* The simpset `circuit_norm` is supposed to bring the goal state to well-trodden forms: `simp only [circuit_norm]`.
* Often, custom definitions like `MySubgadget.circuit` need to be unfolded. You can do so by passing them along in the simp set: `circuit_proof_start [MySubgadget.circuit]` or `simp only [circuit_norm, MySubgadget.circuit]`.
* In many cases, it's needed to keep unfolding things so that only the math content remains.

## In the middle

* The most usual moves are just `simp only [...]`.
* Most `Clean` definitions are meant to be unfolded away.
  * Clean's subcircuit mechanism prevents you from seeing the internal operations of subcircuits, so it's usually fine to unfold everything that you don't know about.
  * Exceptionally, it's usually better not to unfold loop constructions like `Circuit.foldl`. Use `simp only [circuit_norm]` to transform them into plain statements like `∀ i < m, ...`. To deal with the result, it can be beneficial to state a separate lemma for lifting properties to the loop, using induction.
* When a context has an assumption `h : something → something`, probably it's helpful to `specialize h (by ...)`. 
* If math is involved, you use lemmas from Mathlib or `Utils`. The goal state in Clean is usually too large for `rw?` (and also usually for `apply?`), so Loogle is your friend.

## Closing branches

Once there is nothing about Clean and the goal is just about math, the proof branch is about to be closed.

* When `simp_all`, `aesop` or `grind` quickly solves a goal, that proof is very maintainable.
* When it's about natural numbers, addition, equality and less-than, `omega` or `linarith` might be useful.
* When it's about `1 + 1` and `2` (as field elements), or distributing multiplication over addition, try `ring_nf` or `field_simp`.

## What (not) to unfold

* Spec-level definitions (`MyChild.circuit`, `Assumptions`, spec *predicates you plan to prove directly*) are safe in the `circuit_proof_start` list.
* Do **not** unfold expression-formula helpers that occur inside loop bodies — they multiply term size by the iteration count. Unfold them only inside per-row extracted hypotheses.
* Do **not** unfold a child's `Spec` when you plan to apply a generic lemma stated over it — matching the folded `Spec <args>` application is cheap, while unifying against its unfolded `∀`-body can eat the whole heartbeat budget (see `performance-problems.md`).

## Probing goals the LSP can't print

Very large proof contexts can exceed the LSP's printing budget. The productive loop is `lake env lean <file>` plus deliberate type-mismatch probes:

```lean
have hX1 : True := h_loop   -- the error prints h_loop's type, bounded by pp depth
exact (trivial : True)      -- the error prints the goal
```

combined with `set_option pp.explicit true in` when instance-level differences are suspected.

## Assorted quirks

* getElem bounds don't elaborate inline in *statement* types: `(v ++ w)[i]'(by omega)` inside a `have`/`∃` type runs the tactic against an unresolved metavariable and fails. State a helper lemma over an abstract `v : Vector _ k` (plus `hv : v = <concrete>` if cell values matter) and instantiate with `_ rfl`.
* `[OfNat K (2 ^ 130)]`-style gate parameters produce `OfNat.ofNat (2 ^ 130)` terms that don't unify with `(2 : Fp) ^ 130` (recursion past `maxRecDepth`). Bridge explicitly first: `have : (OfNat.ofNat (2 ^ 130) : Fp) = 2 ^ 130 := by norm_num`.
* Inside structure literals in theorem statements, dot-notation like `[1, 1, 1].sum` can fail to parse where `List.sum [1, 1, 1]` is fine; type-ascribed structure literals in argument position can fail with misleading "expected '}'" errors — drop the ascription.

