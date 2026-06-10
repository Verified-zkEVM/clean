# Witgen IR — work plan

Goal: replace shallow-embedded witness callbacks (`ProverEnvironment F → …` closures)
with a deep-embedded witness IR, so that witness generation becomes serializable data
that Rust proving backends (e.g. plonky3) can interpret or compile — mirroring how
constraints already export. Direction decided in
[PR #401 discussion](https://github.com/Verified-zkEVM/clean/pull/401#issuecomment-4667490863).
Feature requirements derived from the existing gadgets: see
[witgen-ir-requirements.md](./witgen-ir-requirements.md).

## Shape of the work: ONE pull request

This entire effort is a single PR on the `witgen-ir` branch. Rationale: accepting the
core change (IR in `Operation.witness`) depends on downstream usability, which can only
be judged by seeing a substantial set of ported gadgets. So core change + interpreter +
ports ship and get reviewed together.

Within the branch, the always-green discipline still applies: each phase below is a
milestone (one or a few commits) after which `lake build` is fully green. The `.native`
escape hatch is what makes this possible.

Key invariants for all work on this branch:
- `lake build` green at every milestone commit.
- Core library files stay sorry-free (AGENTS.md rule); never modify maxHeartbeats.
- Existing gadget proofs should survive ports with at most local fixes — if a port
  forces broad proof rewrites, the IR/eval design is wrong; stop and reconsider.

## The `.native` migration device

The IR gets a constructor `| native (f : ProverEnvironment F → Vector F m)` with
`eval (.native f) env = f env` definitionally (`rfl`). Consequences:
- The core integration phase wraps every existing callback in `.native` via the
  existing `witness`/`witnessField`/`witnessVector`/`<==` primitives — zero gadget
  changes, all proofs see definitionally identical terms.
- Porting a gadget = replacing its `.native` nodes with structured IR.
- `.native` is not serializable; an exportability checker (phase 6) reports remaining
  native/unregistered-intrinsic nodes, giving a monotone coverage metric.

## Phases

### Phase 1 — IR sketch
Design `WitgenIR` (working name) against the requirements doc:
- Two-sorted expression language: field exprs (reuse/embed `Expression F`, extended
  with inverse) and Nat exprs (`+ * / % &&& ^^^ 2^k testBit`), with explicit
  `val` (F→Nat) and `cast` (Nat→F) bridges. [req B.2-B.5]
- Vector formers: bounded `ofFn`/`mapRange`-style build, indexing, literals, `set`,
  `append`. [req B.6]
- `let`-bindings; conditionals on field-equality and Nat-`<` predicates, composing
  with struct results. [req B.7-B.8, E.7]
- Struct packing matching `ProvableType` serialization. [req B.9]
- Constant tables indexed by computed Nat. [req B.10]
- Named intrinsics with a registry (Lean spec per intrinsic); hint/ProverData lookup
  as the first intrinsic (FemtoCairo memory reads). [req C.3]
- `.native` escape hatch.
- `eval : WitgenIR F m → ProverEnvironment F → Vector F m`.

Acceptance: a design note (or the Lean file itself) showing every requirement in
sections B/C of the requirements doc maps to a former or intrinsic; in particular
FemtoCairo `memoryValue`, SHA `Add32`, Keccak `Xor64`, `IsZeroField` expressible.

### Phase 2 — Core integration (green, zero gadget changes)
- `Operation.witness m (code : WitgenIR F m)` replaces the closure field.
- Existing witness primitives wrap their lambda in `.native`.
- Restate `UsesLocalWitnesses`, `dynamicWitnesses`, `ComputableWitnesses`,
  completeness machinery over `code.eval`; add `eval_native` (+ basic eval lemmas)
  to `circuit_norm`.
- Fix everything that pattern-matches on `Operation.witness` (core theorems, tactics).

Acceptance: full `lake build` green with no gadget file modified.

### Phase 3 — Array-backed reference interpreter
- `witgen : List (FlatOperation F) → ProverHint F → Array F → Array F` — linear fold,
  array-backed `ProverEnvironment` (O(1) reads), scalar fast path to avoid per-cell
  `Vector` allocation.
- Prove once, by induction: agreement with `dynamicWitnesses` (under
  `ComputableWitnesses`).
- This is also the standalone witgen speedup (current implementation is accidentally
  quadratic: list-indexed env reads, list append per op) and later the oracle for
  differential-testing the Rust side.

Acceptance: theorem `witgen_eq_dynamicWitnesses` (or equivalent) sorry-free; green.

### Phase 4 — Minimal authoring surface
Smart constructors / notation so ports don't write raw IR constructors. Deliberately
minimal: do a few manual ports first (phase 5 starts here), let them drive the syntax.
A fancier elaborator (surface syntax close to today's lambdas) is a possible follow-up,
not a blocker.

### Phase 5 — Port gadgets (the usability evidence)
Bottom-up; each port is a small green commit replacing `.native` with structured IR.
Order (leaves first; upper Keccak/SHA/Poseidon layers are witness-free composition and
need no porting):
1. `IsZeroField` (field inverse, conditional)
2. `And8` / `And64` (Nat `&&&`)
3. `Xor64`, `Xor32` (Nat `^^^`, U64 struct packing)
4. `Add32` (Nat sums, `% 2^32`, per-bit decomposition)
5. `Bits` / `fieldToBits` (testBit decomposition)
6. `U64.witness` / `decomposeNat` (base-256 limbs)
7. Poseidon `<==` sites (pure field arith, constant tables)
8. Maj32/Ch32 + remaining SHA leaf witnesses (intra-circuit witness reads)
9. FibonacciWithChannels (`floorDiv`/`mod256`)
10. FemtoCairo (stress test: conditionals-into-structs, program table reads,
    memory-hint intrinsic)

Also in this phase: decidable `ComputableWitnesses` for structured IR (syntactic
read-below-offset check), replacing semantic side-condition proofs where possible.

Port pattern observed (IsZeroField, And8, Xor64, Xor32): the circuit change is a
1:1 transliteration of the callback into IR; proofs survive untouched except where
they used the *default* simp set on witness residue (`simpa using h_env 0`-style) —
those need `circuit_norm` (which carries the IR eval lemmas) added to the simp call.


Acceptance: the seven target families (Keccak, SHA256, FemtoCairo,
FibonacciWithChannels, Bits, IsZero, Poseidon) fully free of `.native` in their
witness paths; proofs intact; green. This is the basis on which the PR is judged.

### Phase 6 — Export & checking
- `#assert_exportable circuit` command: fails if reachable witgen contains `.native`
  or unregistered intrinsics.
- Serializer for `WitgenIR` (format co-designed with the existing/planned constraint
  export; JSON first is fine).
- (Separate track, possibly outside this PR: Rust-side interpreter + differential
  test harness against the phase-3 reference interpreter.)

### Phase 7 — Cleanup
- Audit remaining `.native` uses outside the target families; port or justify.
- Decide final status of `.native` (keep for prototyping vs. demote to test-only).
- Docs: authoring guide for witness IR; update AGENTS.md gadget checklist.

## Status

- [x] Direction decided (PR #401 comment)
- [x] Requirements survey (doc/witgen-ir-requirements.md)
- [x] Phase 1 — IR sketch (`Clean/Circuit/WitnessIR.lean`)
- [x] Phase 2 — core integration
- [x] Phase 3 — reference interpreter + equivalence proof (`Clean/Circuit/WitnessGeneration.lean`)
- [x] Phase 4 — authoring surface (witnessField/witnessVector/ProvableType.witness + ofFExpr(s)/ofExprs; <== emits IR)
- [ ] Phase 5 — gadget ports (done: IsZeroField, And8, Xor64, Xor32)
- [ ] Phase 6 — exportability checker + serializer
- [ ] Phase 7 — cleanup
