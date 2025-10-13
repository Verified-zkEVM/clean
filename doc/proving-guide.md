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

