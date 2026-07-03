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

**Also migrated** (second round, after the struct-level-obligation framework work):
- `Clean/Orchard/Utilities.lean`'s `CondSwap.Swap.Input` (`b : Unconstrained field F`,
  `swap : UnconstrainedBool F`), `Clean/Orchard/Sinsemilla/Merkle.lean`'s `Layer.Input`
  (`sibling : Unconstrained field F`, `posBit : UnconstrainedBool F`) and
  `CalculateRoot.Input` / `Clean/Orchard/Action.lean`'s `path : Unconstrained (fields 32)
  F` and `pos : UnconstrainedNat F`. Since there is no vector-hint carrier besides the two
  scalar ones, `pos` (32 Merkle position bits) is *packed into a single natural number*
  (bit `i` = layer `i`) and unpacked per-layer via `NExpr.testBit`; `path` element reads
  are per-index `unconstrained (do return (← input.path)[i])` programs inside the
  32-layer `Circuit.foldl`.
  A **first attempt at this migration was reverted** after `CalculateRoot.completeness`
  hit `(deterministic) timeout at whnf` at the theorem header, then believed to be a
  kernel/elaborator size cliff. It was not: the timeouts were *cascading elaboration
  failure* from a missing `circuit_norm` normalization path — `FExpr.eval ctx xs[i]`
  (evaluating one stuck element read of an opaque `Unconstrained (fields n)` hint) had no
  lift to the vector level, so `h_env` couldn't meet `h_input`'s whole-vector equation,
  and the resulting ill-typed applications blew up `whnf` downstream. The fix is the
  framework lemma `Witgen.FExpr.eval_getElem` (`FExpr.eval ctx xs[i] = (Witgen.eval ctx
  xs)[i]`, the vector analogue of the `evalProjection` simproc; a post-rewrite so literal
  vectors still reduce via `Vector.getElem_ofFn` first). With it, the whole migration goes
  through with only spelling-level proof adjustments in `CalculateRoot.completeness`, and
  `Utilities.lean`/`Action.lean` need zero proof changes.
- The `Fq` scalar hints (`rivk`/`alpha`/`rcv`/`rcmOld`/`rcmNew` across `SpendAuthority`/
  `ValueCommit`/`AddressIntegrity`/`CommitIvk`/`NoteCommit`/`CommitDomain`/`Action.lean`):
  migrated to `UnconstrainedNat` carrying `Fq.val`, as part of the fixed-base table port
  (see the next section) — `ProverAssumptions` gains `scalar < PALLAS_SCALAR_CARD`,
  `ProverSpec` casts `(scalar : Fq)`, verifier-side contracts unchanged.
- `Clean/Orchard/Ecc/Mul/{Incomplete,Complete,Assign}.lean`'s per-round bit hints: the
  *bits themselves* could be packed into `UnconstrainedNat`, but the consuming witnesses
  (`z`, `l1`, `l2`, `xANext`, `yAFinal`) are **recursive accumulator computations** — each
  row's value chains r prior EC additions (`accVal`/`zRunValue`/`rowLambdaValue`). The IR
  has no fold/accumulator loop former (`VExpr` is `lit`/`mapRange`/`append` only; the
  `TODO WITGENIR do we need fully general (foldl) loops?` in `WitnessIR.lean` is exactly
  this), so a compact IR expression per row is impossible today — per-row expansion would
  be O(n²) term size for n=254 rounds. **This is a genuine IR-extension candidate (fold
  loops), not portable as-is.** `Utilities.lean`'s `WitnessShort.Input` remains on the old
  carrier for now (small, non-blocking).

## Fixed-base multiplication window tables

**PORTED for `FullWidth.lean`** (prototype; replication to `Short.lean`/`BaseFieldElem.lean`/
`HashToPoint.lean` in progress): the earlier claim that these need concrete backing data
was wrong (per review) — the abstract `B.point`/`B.u` functions are turned into per-window
8-entry tables *inline* with `Vector.ofFn`, and indexed by the NExpr window value using the
IR's `v[k]`/`.listGet` sugar (the FemtoCairo pattern):

```lean
def rowProgram (B : FixedBase) (scalar : Var UnconstrainedNat Fp) (w : ℕ) :
    Witgen.M Fp (CoordsRow (Witgen.FExpr Fp)) := do
  let xs := Vector.ofFn fun k : Fin 8 => (windowPoint B.point w k.val).x  -- ys, us likewise
  let s ← scalar
  let k := s / (8 ^ w : ℕ) % 8
  return CoordsRow.mk k.toField xs[k] ys[k] us[k]
```

Prerequisite folded in: the `Fq` scalar hints became `UnconstrainedNat` carrying `s.val`,
with `ProverAssumptions` gaining `scalar < PALLAS_SCALAR_CARD` and `ProverSpec` casting
`(scalar : Fq)` — verifier-side `Spec`/`Assumptions` untouched (this covers the previously
deferred `rivk`/`alpha`/`rcv`/`rcm*` items: `SpendAuthority`, `ValueCommit`,
`CommitDomain.r`, `NoteCommit.rcm`, `CommitIvk.rivk`, `AddressIntegrity.rivk`, and
`Action.lean`'s five scalar fields are all migrated). No new framework lemmas were needed;
notable design point: read the scalar with a plain `let` after `← scalar` (not
`Witgen.letN`) — a `letN` behind an opaque program prefix lands at a step index with no
`circuit_norm` evaluation path today (see fix-patterns #24-29).

### Still remaining in this section

- Replication of the `FullWidth.lean` pattern to `Clean/Orchard/Ecc/MulFixed/Short.lean`
  (3 sites), `Clean/Orchard/Ecc/MulFixed/BaseFieldElem.lean` (5 sites), and
  `Clean/Orchard/Sinsemilla/HashToPoint.lean`'s generator reads (`xPs`/`l1s`/`l2s`/`xAs`,
  reading `G.S : ℕ → Point Fp` — a 2^10-entry `Vector.ofFn` table indexed by `pieceWord`)
  — in progress.
- (superseded text below kept for the original site inventory)
  `Clean/Orchard/Ecc/MulFixed/Short.lean` (`Short.main`, 3 sites: `t₀`/`t`/`t₂₁`),
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
  component `BExpr.feq`s (`.ite ((p1=?0) &&& (p2=?0)) ...`), a genuine rewrite of shared
  spec-level branching logic; still native. `lambda`/`delta` **are now ported** via
  `.ite`/`=?` (second attempt): the original proof-shape mismatch is resolved by
  instance-generic bridge lemmas (`ite_lambdaValue`/`ite_deltaValue`, stated with the
  `Decidable` instances as variables) applied right after `circuit_proof_start` — needed
  because `BExpr.feq`'s evaluation decides field equality through its own instance, which
  is not syntactically the canonical `DecidableEq Fp`, so `decide`-spelled patterns never
  match (convert conditions propositional with `decide_eq_true_eq` first, then bridge
  before mathlib's `mul_ite`/`ite_mul` distribution can scatter the `if` into products). `alpha`/`beta`/`gamma` (pure `⁻¹`, no conditional) WERE successfully
  ported. `Clean/Orchard/Ecc/AddIncomplete.lean`'s single witness site (also point
  arithmetic, but *without* any conditional — `nondegenerateAdd`, a straight-line
  `-,*,⁻¹` formula) was fully ported by generalizing `Point.nondegenerateAdd` to work
  over any `{K} [Sub K][Mul K][Inv K]` and calling it directly at `K := Witgen.FExpr Fp`.
