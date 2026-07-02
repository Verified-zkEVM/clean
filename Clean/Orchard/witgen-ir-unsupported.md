# Witgen IR porting: sites left on `witnessNative`

Context: after merging Clean's witgen-IR `main` (PR #403) into this branch, witness
generation across `Clean/Orchard` was ported from closure-based `witnessNative` calls to
the new typed IR (`witness`/`witnessProgram`/`witnessVectorProgram`, see
`doc/witgen-authoring.md`) wherever the underlying computation is expressible in it. This
file tracks every site left on `witnessNative`, with the reason it wasn't (yet, or ever)
ported. It is a living document — update it as further porting work lands.

## Genuine external hints (no parent-committed expression to derive from)

These are the actual private witness inputs to the whole proof — there is nothing "more
primary" within the circuit tree to construct an IR program from, so they must stay
`UnconstrainedDepNative`/`UnconstrainedNative`/`witnessNative` regardless of what the IR
supports elsewhere.

- `Clean/Orchard/Ecc/WitnessPoint.lean`: `WitnessPoint.circuit` and
  `WitnessNonIdentityPoint.circuit`, both `GeneralFormalCircuit.WithHint Fp
  (UnconstrainedDepNative Point) Point`. Callers (`Action.lean`) always supply these from
  the action circuit's own top-level `Input` fields (`cmOld`, `gdOld`, `akP`, `pkdOld`,
  `gdNew`, `pkdNew` — diversified generators / public keys / note-commitment points),
  which are themselves genuine external secrets, not derived values.
- `Clean/Orchard/Action/AddressIntegrity.lean` (`rivk : UnconstrainedNative Fq F`),
  `Clean/Orchard/Action/SpendAuthority.lean` (`alpha : UnconstrainedNative Fq F`),
  `Clean/Orchard/Action/ValueCommit.lean` (`rcv : UnconstrainedNative Fq F`): all
  pure pass-throughs of `Action.lean`'s own top-level `Fq`-valued scalar inputs
  (`rivk`, `alpha`, `rcv`) down into the fixed-base multiplication gadgets. These
  scalars are genuinely external (random blinding factors / the incoming viewing key /
  the spend-authorization randomizer) — see the fixed-base-table note below for why even
  an `Unconstrained`→`UnconstrainedNat` upgrade at this boundary wouldn't unlock porting
  the *downstream* window-decomposition witnessing (that's blocked by the table, not by
  the scalar's hint-ness).
- `Clean/Orchard/Action.lean` (`main`): the `Input` struct's `UnconstrainedDepNative`/
  `UnconstrainedNative`-typed fields describing the actual note plaintexts, keys, and
  blinding scalars (`vOld/vNew/rhoOld/psiOld/psiNew/nk/rcmOld/rcmNew/rcv/rivk/alpha/
  vNetMagnitude/vNetSign/path/pos/gdOld/pkdOld/cmOld/akP/gdNew/pkdNew`) are the circuit's
  true external witness — not eligible for the `Unconstrained`/`UnconstrainedBool`/
  `UnconstrainedNat` (IR-backed) upgrade, since that mechanism is for hints a *parent*
  constructs from its own already-committed values, and `Action.main` has no parent
  within Clean. The plain pass-through reads of these fields (`psiOld`, `rhoOld`, `nk`,
  `vOld`, `vNew`, `vNetMagnitude`, `vNetSign`, `psiNew`) — i.e. "commit the external value
  as-is with no arithmetic" — stay on `witnessNative (inst := inferInstanceAs
  (Witnessable Fp field (Var field))) input.X`: since the *value itself* is a raw
  `ProverEnvironment F → Hint` closure (per `UnconstrainedDepNative`'s definition), only
  `witnessNative` can accept it — bare `witness` (the typed-IR entry) fundamentally cannot,
  it expects an `FExpr`-shaped value. (An earlier pass mistakenly used bare `witness` here;
  caught and fixed once `Action.lean` finally compiled far enough to type-check it — see
  the fix-patterns scratch notes, gotcha #20, for the misleading error this produces.)
  These 8 sites are correctly-named plumbing, not a porting gap.

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
  the `Unconstrained`/`UnconstrainedBool` upgrade targets. Not attempted here for the
  same reason as above (struct-shape + call-site + proof migration, not a routine port).
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
