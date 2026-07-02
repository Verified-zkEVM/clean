# Witgen IR porting: sites left on `witnessNative`

Context: after merging Clean's witgen-IR `main` (PR #403) into this branch, witness
generation across `Clean/Orchard` was ported from closure-based `witnessNative` calls to
the new typed IR (`witness`/`witnessProgram`/`witnessVectorProgram`, see
`doc/witgen-authoring.md`) wherever the underlying computation is expressible in it. This
file tracks every site left on `witnessNative`, with the reason it wasn't (yet, or ever)
ported. It is a living document — update it as further porting work lands.

## External hints: `Unconstrained`/`UnconstrainedNat` migration

Correction (superseding an earlier, wrong version of this section): a genuinely top-level
circuit's "external hint" `Input` fields are *not* exempt from the `Unconstrained`/
`UnconstrainedBool`/`UnconstrainedNat` upgrade. `Var (Unconstrained M) F` is just a type —
as opaque a bound variable as any `Expression F`/`Point (Expression F)` field — so nothing
about it requires a parent circuit to construct a value from already-committed data. The
`unconstrained`/`unconstrainedBool`/`unconstrainedNat` *constructor* functions are only
needed by callers building a hint out of other in-scope expressions (see
`Clean/Utils/Test/TestMixedCircuitType.lean`, `Clean/Examples/HintExample.lean`); a
genuinely top-level struct field with no caller inside Clean just changes type, with no
construction step needed anywhere.

**Migrated** (`Unconstrained M`/`UnconstrainedNat` now used):
- `Clean/Orchard/Ecc/WitnessPoint.lean`: `WitnessPoint.circuit`/`WitnessNonIdentityPoint.circuit`,
  `Input := Unconstrained Point` (was `UnconstrainedDepNative Point`), read via
  `witnessProgram` (was `witnessNative`).
- `Clean/Orchard/Action.lean`'s `Input`: 15 fields — `gdOld/pkdOld/cmOld/akP/gdNew/pkdNew :
  Unconstrained Point`, `vOld/rhoOld/psiOld/nk/vNew/psiNew/vNetMagnitude/vNetSign :
  Unconstrained field` — migrated, with `main`'s plain pass-through reads switched from
  `witnessNative input.X` to `witnessProgram input.X`, and the `WitnessPoint.circuit`/
  `WitnessNonIdentityPoint.circuit` subcircuit calls now type-aligned automatically (no
  wrapper needed — the field flows straight from `Action.Input` into the callee's `Input`).

**Not yet migrated, with reasons**:
- `Clean/Orchard/Action.lean`'s `path : UnconstrainedDepNative (fields 32) F` and
  `pos : UnconstrainedNative (Vector Bool 32) F`, and the matching fields in
  `Clean/Orchard/Sinsemilla/Merkle.lean`'s `CalculateRoot.Input`/`Layer.Input`
  (`sibling`/`posBit`), and `Clean/Orchard/Utilities.lean`'s `CondSwap.Swap.Input`
  (`b`/`swap`, consumed by `Layer.main`). `path`/`pos` are field-independent *vector*
  hints (`fields 32` fits `Unconstrained` fine; `Vector Bool 32` doesn't fit any
  `Unconstrained*` shape directly — there's no vector-hint carrier besides the two scalar
  ones, `UnconstrainedBool`/`UnconstrainedNat`, so `pos` would need packing into a single
  `UnconstrainedNat` with per-layer bits read back via `NExpr.testBit`).
  **Attempted and reverted**: migrating `path`→`Unconstrained (fields 32)` alone (even
  before touching `pos`) made `CalculateRoot.completeness`'s `circuit_proof_start` hit a
  `(deterministic) timeout at whnf` — a genuine kernel/elaborator size cliff, the same
  class of problem `Ecc/MulFixed/BaseFieldElem.lean` hit and eventually fixed (see
  `doc/performance-problems.md`), but this one is unresolved. Root cause hypothesis (not
  confirmed): `Circuit.foldl (.finRange 32) ...` constructing a fresh
  `unconstrained (do return (← input.path)[i])` term on each of the 32 unrolled
  iterations is a much larger term for `circuit_proof_start`'s default unfold to chew
  through than the old closure `fun env => (show Vector Fp 32 from input.path env)[i]` —
  unlike `Unconstrained`/`UnconstrainedBool`/`UnconstrainedNat` on non-looped call sites
  (`WitnessPoint.lean`, the Point/field `Action.Input` fields above, and
  `Utilities.lean`'s `CondSwap.Swap.b` field in isolation — verified independently green),
  which have no such blowup. Needs a dedicated investigation (likely an "opaque prefix"
  extraction analogous to `BaseFieldElem.lean`'s `prefixCircuit` fix, or restructuring
  `CalculateRoot`'s 32-layer fold into a bundled subcircuit) before attempting again — not
  done here given the risk of an open-ended kernel-cliff debugging session on a proof this
  size. `CondSwap.Swap.swap`/`Layer.posBit`/`CalculateRoot.pos` are entangled with this
  same fold (the `swap` field flows into `Layer.main` which flows into `CalculateRoot`'s
  32x unrolled construction), so they're reverted alongside `path` rather than left
  half-migrated.
- `Clean/Orchard/Action/AddressIntegrity.lean` (`rivk : UnconstrainedNative Fq F`),
  `Clean/Orchard/Action/SpendAuthority.lean` (`alpha : UnconstrainedNative Fq F`),
  `Clean/Orchard/Action/ValueCommit.lean` (`rcv : UnconstrainedNative Fq F`), and
  `Action.lean`'s own `rcmOld`/`rcmNew : UnconstrainedNative Fq F`: `Fq` (the Pallas
  *scalar* field, fixed and independent of the circuit's own field `Fp`) has no
  `Unconstrained*` carrier of its own — the natural fit is `UnconstrainedNat` holding
  `Fq.val : ℕ` (mirroring the `NExpr.val`/`FExpr.ofNat` `F ↔ ℕ` bridge used elsewhere), but
  this wasn't attempted: the *downstream* consumer (`MulFixed`'s window-decomposition
  witness generation, reading the scalar via `.testBit`/`.val` on the actual `Fq`
  element) is itself blocked on the abstract fixed-base generator tables (see the
  "Fixed-base multiplication window tables" section below) having no concrete backing
  data — so migrating just the scalar's carrier type wouldn't unlock anything further
  down the chain, and risks its own version of the same kernel-cliff class of issue seen
  above given no `Unconstrained*`/`Fq` combination has been tried yet.
- `Clean/Orchard/Ecc/Mul/{Incomplete,Complete,Assign}.lean`'s per-round bit hints and
  `Clean/Orchard/Utilities.lean`'s `WitnessShort.Input` — not attempted this round; see the
  "Type-level native" section below for the design (packed `UnconstrainedNat` +
  `NExpr.testBit`/`.range`), which carries the same open kernel-cliff risk given how
  `Ecc/Mul/*` also loop over many rounds (`Circuit.foldlRange`/`foldl` over 3–83
  iterations, structurally similar to `CalculateRoot`'s 32-layer fold).

## Fixed-base multiplication window tables (abstract, no concrete backing data)

- `Clean/Orchard/Ecc/MulFixed/FullWidth.lean` (`FullWidth.main`, 3 sites: `row₀`/`row`/
  `row₈₄`), `Clean/Orchard/Ecc/MulFixed/Short.lean` (`Short.main`, 3 sites: `t₀`/`t`/`t₂₁`),
  `Clean/Orchard/Ecc/MulFixed/BaseFieldElem.lean` (`RunningSumMul.main`, 5 sites: `t₀`/`t`
  ×2/`t₄₃`/`t₈₄`): all compute `rowValue`/`rowTailValue B scalar w`, which reads
  `B.point`/`B.u` — fields of the abstract `MulFixed.FixedBase` structure
  (`Clean/Orchard/Ecc/MulFixed.lean`), universally quantified functions `ℕ → CoordsParams
  Fp` / `ℕ → ℕ → Fp` satisfying algebraic axioms, not backed by any concrete `Array`/
  `Table`/`ProverData`. The IR's table-reading primitives (`.listGet` on a literal
  `List`/`Vector`, `.dataGet`/`.hintGet` on committed/uncommitted `ProverData`) all need
  *some* concrete data to index into; there is none here — no `FixedBase` instance is
  ever concretely instantiated anywhere in the repo (all generator bases —
  `NoteCommit^Orchard_R`, `CommitIvk`'s base, `ValueCommitV`/`ValueCommitR`, `K^Orchard`,
  `SpendAuthG` — are threaded through as abstract `Params` fields, per `Action.lean`).
  **This would need the actual concrete generator tables (halo2's precomputed Pallas
  point coordinate lookup tables) materialized as literal data before it's portable at
  all** — a substantially larger undertaking than a witness-generation rewrite, out of
  scope here. The Nat-decomposition-only parts of the SAME functions (bit/window index
  arithmetic, with no table lookup) have no table dependency and are in principle
  portable — see `BaseFieldElem.lean`'s `alpha0Prime`/`alpha1`/`alpha2` (canonicity
  region, pure `.val`/div/mod). `BaseFieldElem.lean` itself needed extensive, dedicated
  repair this session for a separate, pre-existing kernel/heartbeat performance cliff
  (see `doc/performance-problems.md`, now resolved — the file builds clean with zero
  sorries). A follow-up attempt to port `alpha0Prime`/`alpha1`/`alpha2` produced a
  `soundness`-proof-shape mismatch (a `rw` pattern no longer matching, one more instance
  of the "witness normal form changed" class of issue documented elsewhere in this file)
  — given how much dedicated effort it took to stabilize this file's build at all, that
  port was deliberately reverted rather than risk destabilizing it again; these 3 sites
  remain `witnessNative` as the more conservative choice. `MulFixed/Short.lean`'s
  `yP = sign * magnitudeMul.y` (pure multiplication, no table) WAS successfully ported.
- `Clean/Orchard/Sinsemilla/HashToPoint.lean` (`HashPiece.main`, 5 sites: `xPs`/`l1s`/
  `l2s`/`xAs`/`Output.yANext`): reads a Sinsemilla generator table `G.S : ℕ → Point Fp`
  (the `Generators` structure), same abstract-function shape as `FixedBase` above —
  investigated in depth (checked `generatorTable`/`StaticTable.row`/`Table.dataGet`/
  `hintGet` and confirmed no `"sinsemilla generators"`-keyed `ProverData`/`ProverHint`
  entry exists anywhere, and `Generators` is never concretely instantiated in the repo).
  [If a later pass ports this after all — e.g. because concrete generator tables get
  materialized — update this entry.] `zRest` in the same function (a pure `.val`/Nat-div
  running-sum slice, no table) WAS successfully ported.

## Type-level native by declared `Unconstrained*`/hint-carrying Input types

These sites' *arithmetic* would be expressible in the IR (some trivially so — plain
copies, simple conditionals), but the *type* of the value they read from is currently
`UnconstrainedNative`/`UnconstrainedDepNative` (the closure-backed escape hatch), not the
IR-backed `Unconstrained`/`UnconstrainedBool`/`UnconstrainedNat`. Upgrading the type is a
separate, larger migration (changes the `Input` struct's field type, hence every caller
that constructs that struct, hence potentially proofs downstream) — not attempted as part
of a routine per-file witness-generation port. Flagged here as candidates for that
follow-up migration, roughly in decreasing order of expected payoff:

- `Clean/Orchard/Ecc/Mul/{Incomplete,Complete,Assign}.lean`: the per-round scalar-bit
  hints (`bits : UnconstrainedNative BitsHint F` / `bit : UnconstrainedNative Bool F`).
  **Highest-value candidate**: the scalar `alpha` these bits are extracted from
  (`kBits alpha i = (alpha.val + tQNat).testBit(254-i)`) is a *committed* `Fp` expression
  at the entry circuit (`Assign.lean`'s top-level `Input`), not itself a hint — so in
  principle the entry circuit could construct each round's bit via `unconstrainedBool (do
  return ((alpha.val + tQNat) >>> (254 - i)) % 2 =? 1)` (all `NExpr`-expressible: `.val`,
  `+`, `>>>`, `%`, `=?`), threading `UnconstrainedBool`-typed hints down through
  `Complete.AssignRegion`/`Incomplete.DoubleAndAdd`/`Assign.ProcessLsb` instead of
  `UnconstrainedNative Bool`/`BitsHint`. This would then make those functions' own
  witness generation (`z`, `yP`, `corrX`, `corrY`, etc. — currently native specifically
  because they read the hint bit via `env`) portable to typed `witness` with `.ite`.
  Not attempted here: touches 3 files' `Input` struct shapes plus every call site plus
  the soundness/completeness proofs that currently destructure `UsesLocalWitnesses`-style
  facts about the closure form — a genuinely separate, higher-risk migration.
- `Clean/Orchard/Utilities.lean`: `CondSwap.Swap.Input` (`b : UnconstrainedDepNative
  field F`, `swap : UnconstrainedNative Bool F`) and `WitnessShort.Input`/`taggedMain`
  (`Input := UnconstrainedDepNative field F`). At real call sites (`Merkle.lean`), these
  ARE constructed from already-committed expressions (`fun env => eval env someExpr`) —
  i.e. they're internal plumbing, not genuine external secrets, and are exactly the shape
  the `Unconstrained`/`UnconstrainedBool` upgrade targets. **Partially attempted**: `b :
  Unconstrained field F` alone, migrated and verified independently green (zero warnings,
  zero sorries). `swap : UnconstrainedBool F` was also migrated, but its only real
  consumer (`Merkle.lean`'s `Layer.main`, inside `CalculateRoot`'s 32-layer
  `Circuit.foldl`) hit the same kernel/elaborator size cliff documented above under
  "External hints" — reverted alongside `path`/`pos`/`Layer.posBit`/`CalculateRoot.pos`
  rather than left half-migrated. `b`'s migration was reverted too, purely so this file's
  `CondSwap.Swap.Input` stays internally consistent (`a`/`b` migrated but `swap` not would
  be a strange, undocumented halfway state) — not because `b` itself had any issue.
- `Clean/Orchard/Sinsemilla/HashToPoint.lean` (`Chain.Nil.main`'s `yFin`, reading
  `input.yA : UnconstrainedDepNative field F`): the `Y_A` accumulator value is
  *deliberately* kept off the constraint system as a hint by the halo2 source design
  (see the file's own comments) — this one is a genuine design choice to keep as a hint,
  not just an artifact of the old API; even after an `Unconstrained` migration elsewhere,
  this specific site should probably stay hint-shaped (needs source-conformance review
  before touching, not just a mechanical type swap).

## Point-arithmetic sites needing shared-formula conditional restructuring

- `Clean/Orchard/Ecc/Add.lean` (`Add.main`): `r` (= `input.p + input.q`, i.e.
  `Point.add`/`ShortWeierstrass.add`), `lambda`, and `delta`. `ShortWeierstrass.add`
  dispatches on `Decidable`-equality of *point pairs* (`p = (0,0)`, `q = (0,0)`,
  `p.1 = q.1`, nested) — porting it to the IR requires decomposing pair-equality into
  component `BExpr.feq`s (`.ite ((p1=?0) &&& (p2=?0)) ...`), which is a genuine rewrite of
  shared spec-level branching logic, not just a witness-level annotation; `lambda`/`delta`
  (which only need scalar equality, not pair equality) were attempted directly via
  `.ite`/`=?` but produced a soundness/completeness proof-shape mismatch downstream (the
  `Gate.Spec` conjunction's `simp`-normal-form differs between the `lambdaValue`-unfolded
  path and the raw `.ite`-evaluated path in a way that didn't reconcile with a
  reasonable amount of `simp`-lemma tuning) — reverted to `witnessNative` rather than
  force a fix. `alpha`/`beta`/`gamma` (pure `⁻¹`, no conditional) WERE successfully
  ported. `Clean/Orchard/Ecc/AddIncomplete.lean`'s single witness site (also point
  arithmetic, but *without* any conditional — `nondegenerateAdd`, a straight-line
  `-,*,⁻¹` formula) was fully ported by generalizing `Point.nondegenerateAdd` to work
  over any `{K} [Sub K][Mul K][Inv K]` and calling it directly at `K := Witgen.FExpr Fp`.
