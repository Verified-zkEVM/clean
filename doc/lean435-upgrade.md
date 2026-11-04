# Halo2 branch: Lean 4.35 upgrade

This branch preserves the Halo2/Orchard development at upstream
`Verified-zkEVM/clean`, `halo2-clean-2`, commit
`a77b48e85facda02c9ae910364314201836e67ae`. It does not replace that development
with the separately evolved `main` branch.

The compiler and Mathlib are upgraded together to 4.35.0, matching upstream
Clean main's toolchain (rechecked at
`1356fc7fb914535ba87d72b40a3a6922e51afa64`). CompPoly uses its `v4.35.0`
release. CompElliptic uses the public Lean 4.35 compatibility port at
`zksecurity/compelliptic-lean4-35`, commit
`f26a235f2f647b10fe63bc4ec4c7ee394b3c8f43`. Its source tree matches the compatible checkout used
for the historical build results below; only the downstream-independent port
notes were cleaned up. Exact transitive revisions are in `lake-manifest.json`.

## What changes

Proof scripts explicitly unfold record projections, monadic `pure`, array/list
bridges, and natural-number identities which the newer elaborator/simplifier
no longer reduces implicitly. Deprecated theorem aliases are updated where
needed. `Expression.eval_sub` records the existing subtraction interpretation
as a proved normalization lemma. Three corresponding equations expose witness-IR
subtraction, negation, and inversion. The expression representations are unchanged.
Concrete witness instance projections are included in `circuit_norm`, and the
proved Halo2 subtraction/negation tree equations feed selector/query proof
automation.
The separate proof-only `Clean/Gadgets/WitnessEvaluation.lean` supplies bounded
expression/constant-vector read equations and direct equations for IR XOR,
division, and remainder. Its read bounds are proved at the call sites (finite
indices or modular residues); they are not new unproved circuit assumptions.
These helpers expose the existing interpreter and avoid evaluating opaque field
or table expressions during elaboration. These changes restore normalization; they do
not alter circuit or witness execution.

The unchanged struct-tactic regression test also exposed a Lean 4.35 issue with
the public `Var` type alias. Structure detection now explicitly unwraps that
alias before checking its `ProvableStruct` instance. This is restricted to the
type of a variable; ordinary structure detection retains reducible transparency.
The original regression test is preserved, and the affected proof closures are
rebuilt after this tactic change.

Lean 4.35 rejects two old constructor-instance registrations in
`Circuit/Explicit.lean` and six in `Circuit/Loops.lean`, because their explicit
arguments cannot be inferred through typeclass search.
They remain the same explicitly callable, instance-reducible constructors with
the same argument types and proof bodies; the valid typeclass wrapper remains
registered, and the existing explicit-circuit tactic examples still check.
The two channel-valued declarations in `Examples/FibonacciWithChannels.lean`
likewise become explicitly callable, instance-reducible definitions: a `Channel`
is not a typeclass in Lean 4.35. Their names, values, and circuit uses remain the
same.
A few record/tuple wrappers consequently provide their already required
elaboration certificates explicitly, after splitting the input constructor.
Some bounded-vector accesses spell their existing index proofs explicitly to
avoid automatic bound search through large contexts; no new index hypothesis
is added. Long fold/update proofs factor out small, proved equations over
abstract element types to keep concrete field and hash metadata opaque.
Merkle layer metadata now names its existing output references explicitly;
the required `output_eq` fields prove agreement with circuit execution. The
explicit constant-output proof argument of the Merkle fold is erased by
`Circuit.foldl`; `main_eq_foldlM` proves that its executable fold is unchanged.

The package opts into Lean's supported compatibility settings:

- `backward.do.legacy = true` retains the old mutable-loop lowering, avoiding
  changes to the algorithms or their internal state representations.
- `backward.isDefEq.respectTransparency = false` retains the old implicit-argument
  unification behavior. Lean's implementation makes this also disable the
  narrower `respectTransparency.types` check.

A few concrete selector-requirement proofs and metadata certificates locally restore
`backward.isDefEq.respectTransparency = true` to prevent unnecessary unfolding
of Pallas field implementations. This affects proof elaboration, not the
circuit or verifier.

These are elaboration settings. Lean 4.35 still kernel-checks the generated proof
terms. No kernel check is skipped, heartbeat limit raised, new axiom admitted,
or theorem obligation weakened by these settings.

## Validation scope

The final combined ordinary build passes all 3,620 Lake jobs, covering the
`Clean` default library, `CleanTests`, `Clean.Halo2`, `Clean.Ironwood`,
`Clean.Orchard`, and all 15 existing modules under `Clean/Halo2/Tests`. This
includes rebuilding the affected local closure after the `Var` tactic fix and
preserving its original regression test. The checked-in consecutive-empty-lines
check and `git diff --check` also pass.

The new witness-evaluation helper module passes a strict direct check with
`autoImplicit=false` and `warningAsError=true`; all seven helper axiom closures
contain only `propext`, `Classical.choice`, and `Quot.sound`. Selected changed
proof modules also pass direct checks with those strict options. These checks
are distinct from the ordinary combined build and its disclosed warnings.

These builds reuse toolchain-matched external dependency objects. Changed Clean
modules and their affected local proof closures are rebuilt; a cache-free rebuild
of all Mathlib is not claimed. Lean 4.30 project objects are not reused.

An additional direct check of the whole aggregate `Action.Bundle` module capped
at 4 GiB exhausts interpreter memory in the unchanged
`synthWitness_lookupSelectorsAnchoredBy` prefix. That constrained check is not
reported as passing. The authoritative aggregate build uses the normal Lake
resource settings; no source-level resource limits are raised by this port.

The existing pdqsort test now reports only `propext` and `Quot.sound`; its
message guard is updated to remove the no-longer-used `Classical.choice`.

The existing CI warning-fatal policy is not satisfied by this preserved branch.
Actual `lake build Clean --wfail`, `lake build Zcash --wfail`, and
`lake build Orchard --wfail` runs return failure on the replayed warnings,
including Mathlib module-system migration notices, deprecations, and existing
linter/draft warnings. These warnings have not been hidden with global
suppression flags. A successful ordinary build must not be reported as a clean
warning-fatal CI run.

New module-system/deprecation linter warnings are distinct from proof failures.
Selected changed files have also been checked directly
with `autoImplicit=false` and `warningAsError=true`; this does not imply that
the entire preserved branch is warning-free.
The preserved development also contains pre-existing `sorry` declarations and
unfinished examples. A successful module build does not remove those gaps or
upgrade their assurance; no new `sorry`, axiom, or admission is introduced by
this port. Existing theorem assumptions and executable circuit definitions are
preserved; the documented output metadata changes carry checked equivalence
proofs.
