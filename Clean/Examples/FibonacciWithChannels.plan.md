# FibonacciWithChannels soundness proof plan

This note captures learnings and a concrete plan for completing
`fibonacciEnsemble_soundness` in `Clean/Examples/FibonacciWithChannels.lean`.

## General guidelines

This is a large proof, so try to make incremental progress. Prove intermediate statements (with `have`) or work backwards from the  
goal with `suffices`.

Report back to the user when either:

- You have finished the proof. In this case, start you message with "SUCCESS!".
  - Hard requirement for calling success: `lake build  Clean.Examples.FibonacciWithChannels` succeeds.
- You feel entirely stuck. You have tried to make progress from a lot of different angles, but you're at a point where no further progress seems to be possible. In this case, start your message with "I am entirely stuck, because".

## What we learned so far

- The soundness proof must **derive the ensemble spec from the given hypotheses**
  (`Constraints`, `BalancedChannels`, `VerifierAccepts`), without modifying their intent.
- It is **invalid** to finish by deriving `False` from the hypotheses (e.g. by
  changing `ConstraintsHold` or collapsing `VerifierAccepts` into a contradiction).
- The local soundness theorems for `FormalCircuitWithInteractions` are the key:
  each circuit proves
  ```
  (constraints ∧ channel guarantees) ⇒ (spec ∧ channel requirements).
  ```
  If we can establish **channel guarantees globally**, we can upgrade these to
  ```
  constraints ⇒ spec.
  ```
- The **channel balance** hypothesis is intended to derive global guarantees
  from requirements: a pulled element (multiplicity -1) should be matched by a
  push (positive multiplicity), and the push side is where requirements are proved.

## High-level plan

1. **Use local soundness on tables**:
   For each table circuit (`pushBytes`, `add8`, `fib8`), apply its soundness
   theorem to obtain:
   - The circuit spec (when available), and
   - The channel **requirements** emitted by that circuit.

2. **Prove channel guarantees from balance + requirements**:
   - **Bytes channel**:
     - Only `pushBytes` emits non-(-1) multiplicities.
     - Its requirements trivially imply the byte-range property for emitted
       elements (constants 0..255).
     - With channel balance, any `-1` pull must match some positive emission,
       so the **guarantee** “pulled element is a byte” follows.
   - **Add8 channel**:
     - Only `add8` emits; `fib8` pulls.
     - Once byte guarantees hold, `add8` soundness gives requirements for
       add8 emissions, and balance yields guarantees for add8 pulls.

3. **Use guarantees to upgrade soundness**:
   With global guarantees for bytes/add8, the local soundness statements become
   `constraints ⇒ spec` for the affected circuits.

4. **Fibonacci channel (hard part)**:
   - The `fib8` table both pulls and pushes Fibonacci states in each row.
   - A balance-only argument is likely **insufficient** without an induction
     across interactions.
   - Likely need an induction on the number of interactions (or on the trace
     rows), using `fib8` soundness to propagate valid states forward.

5. **Final step**: combine the verifier spec with the globally established
   Fibonacci-state guarantees to prove the ensemble spec for public input.

## Likely challenges / extra hypotheses

- **Balance strength**:
  The current `BalancedChannels` checks only the _sum of multiplicities_, not
  per-message balance. To justify “every `-1` has a matching `+1` for the same
  message,” we may need a stronger balance notion (e.g. equality of
  `toFinsupp`/multiset over messages).

- **No-overflow assumption**:
  The balance-to-matching argument uses a “no overflow” intuition. We may need
  an explicit bound or lemma that `(-1)` multiplicities cannot be canceled by
  other values unless a matching emission exists.

- **Acyclic dependency**:
  For bytes/add8, the channel dependency graph is monotone:
  `pushBytes` → bytes guarantees → `add8` requirements → add8 guarantees → `fib8`.
  For Fibonacci, the dependency is cyclic; this is where induction is needed.

- **Missing proofs**:
  `pushBytes.soundness` is currently `sorry`, but its guarantees are trivial and
  should be easy to fill in (emits constants 0..255).
