# Handoff: full VK matching arc (Mul.lean) + parked tasks

Branch `halo2-clean-2` (PR #418). Everything referenced below is pushed. Read
`Clean/Halo2/vk-matching-design.md` first for the framing; the state below supersedes its
"Phase 2 deferred" status.

## Where VK matching stands

Goal (Gregor): match the *full* VK content — CS structure AND everything `synthesize` adds
(selector activations, copy constraints/σ, fixed-column values incl. lookup tables and
constants). MSM commitments stay a trusted deterministic function of that data.

Done and green:

- CS-structure fixtures pre+post selector compression, `#guard`-pinned:
  `TestVkMatchMul`/`TestVkMatchAdd`, plus per-circuit `Sinsemilla*`/`Merkle*`
  Pre/Post/SelMap in `Clean/Halo2/Fixtures/` (commit `4b45ed6e` — each header documents the
  exact Rust call chain).
- **Layout fixtures** (commit `2631644a`): `MulLayout`/`SinsemillaLayout`/`MerkleLayout` —
  region placements, permutation column order, **ordered raw copy list** (σ's cycle
  rotations depend on copy order), exact keygen σ (sparse), constants-allocation map
  (floor-planner-routed rows), full fixed contents including loaded tables. k=11 keygen
  view, `Value::unknown()`.
- **Lean reconstruction machinery** (commit `fb5d88ee`): `Clean/Halo2/Fixtures/Layout.lean`
  (reusable — lockstep place-walk incl. `table_idx` region slots; ordered copy extraction
  with constants deferred to region end; verbatim `permutation/keygen.rs` Assembly port;
  `usableRows = n − 6`; `compress_selectors` assignedRoot encoding) +
  `Clean/Halo2/Tests/TestVkLayoutMul.lean`. Machinery fully validated (σ replay from the
  dump's own copies, exact table/constants reconstruction).

## DONE (2026-07-17 night run): the mul relayout arc is complete

The main task below is finished and pushed; the three `TestVkLayoutMul.lean` `#guard`s
(copyList/σ/fixed) are ON, unmodified, and green, with `TestVkMatchMul` still green.
What happened, in order:

- `MulIncomplete`: start-copy order fixed to Rust's z, x_a, y_a (`incomplete.rs:273-287`) —
  the dump's ordered copy list pins it (`(5,4,4,3)` x_a before `(6,3,5,3)` y_a).
- `Mul.lean` `mainRegion` re-laid to Rust's exact scheme: `offInit=0`, `offHi=offLo=1`
  (side-by-side), `offComp=129`, `offLsb=135`. **Both proofs survived unchanged** — they
  address cells through the symbolic offsets, and the overlapping `x_p`/`y_p` writes carry
  equal values, so the completeness witness-env equations coincide.
- The parked `mul-relayout-wip` "regenerated fixture" claim was verified INDEPENDENTLY and
  confirmed: the fixture's `regions` line was wrong for regions 3/6 (recorded 0/1; truth
  2/140). Evidence: the fixture's own copyList places the init-add copies at absolute rows
  2/3, and `single_pass.rs:97-105` places the main region at the advices-0/1 tail (= 2).
- Per Gregor's go-ahead ("write your own fixture dumping logic in the sibling halo2
  folder"), a fresh dumper now lives at `halo2_gadgets/src/ecc/chip/layout_dump.rs`
  (sibling checkout `/root/code/halo2`, tag `halo2_gadgets-0.5.0`, commit LOCAL to this
  machine per the dumper ruling; run
  `cargo test -p halo2_gadgets --lib ecc::chip::layout_dump -- --nocapture`). It rebuilds
  the MulDumpCircuit harness and reproduces the original dump's 56-entry ordered copy list
  **byte-for-byte** — harness equivalence — so its placement line is authoritative:
  `[0, 0, 1, 2, 139, 139, 140]`. `MulLayout.lean`'s regions line (only) was regenerated
  from it, with provenance in the fixture header.

Still open from the queue below: #34, #30, #22, #23, #31, #32, and the Sinsemilla/Merkle
layout tests (other agent's arc).

## The headline finding + the main task (historical — done, see above)

The mul port's `mainRegion` layout **diverges from Rust**: `Mul.lean` stacks
hi/lo/complete vertically (~264 rows, the old "disjoint row ranges" soundness strategy),
but `mul.rs:171-296` runs the hi/lo `double_and_add` halves **side-by-side at the same
rows** on disjoint column sets sharing only `x_p/y_p` (~137 rows; the floor planner places
the overflow siblings at row 139, which collides with the stacked layout).

Task: re-lay `mainRegion` to Rust's exact row scheme (child bundles are offset-generic —
change instantiation, not contracts; configure/gates are VK-frozen, `TestVkMatchMul` must
stay green), absorb the proof fallout in `Mul.lean` (non-overlap now by
column-disjointness; overlapping `x_p/y_p` writes carry equal values — there is
same-cell-double-assign precedent in the file), then **turn on the three disabled
`#guard`s in `TestVkLayoutMul.lean` (copyList/σ/fixed) unmodified** — they are the
acceptance criteria. Never weaken a check; the ordered copy list's first divergence is the
diagnostic.

Partial prior work is parked on branch **`mul-relayout-wip`** (do-not-merge): its last
finding was that after the row change, a regenerated fixture differed *only* in region
placements (main 0→2, overflow 1→140) with copyList/σ/fixed identical — close, but verify
independently; it may have assumed a harness tweak.

**Caveat**: the Rust dumper lives only on Gregor's main machine (halo2 checkout, local
branch `lean-fixture-dump`; fixture headers carry regeneration commands). If the fixture's
placement line genuinely needs regenerating, coordinate with Gregor rather than
hand-editing dumped data.

## Settled rulings (don't relitigate)

- Generated layout fixtures' `maxRecDepth` is an accepted allowances exception (data-only,
  8–21s builds); chunked rendering is the eventual cleanup.
- halo2 dumper commits stay local to Gregor's machine.
- Equality-set question resolved as a **layered structure**: core chip Pre/Post fixtures
  stay chip-only; the Layout fixtures index against an *orchard-consistent wrapper*
  (test-prelude `enableEquality` on all 10 advices — which also adds rot-0 queries);
  optionally dump a wrapper-level Pre to pin the wrapper CS.
- Sinsemilla/Merkle layout tests belong to the agent porting those files — coordinate,
  don't collide.

## Queued follow-ups (after the mul arc)

- **#34**: add `output` to `derive_contract_bridges`' fields so `circuit_proof_start`'s
  on-the-fly bridges subsume hand-written `round_output`/`loop_output`-style lemmas
  (verify the whnf-derived RHS reduces as cleanly as the folded `reads` form).
- **#30**: kernel deep-recursion root cause (explicitly owed to Gregor; memory-capped
  fail-fast repro only).
- **#22** env-spelling unification; **#23** full-exercise pass; **#31** env-generic
  `deriving CircuitType` for mixed hint structs; **#32** `Witgen.M` builder port +
  `UnconstrainedNat`/vector IR hints (prereqs for non-native witgen; TODOs in
  `MulIncompleteRound.lean` name them).
- Refactors that only shift code around stay on ice until the VK arc is done.

## Style contract

Follow `MulIncompleteRound.lean`/`MulIncomplete.lean`: `circuit_proof_start [<own defs>,
<child bundles>]` (bundle entries auto-derive contract bridges), positional neighborhoods
in Witness/extract, specs in domain language, improve the tactic layer rather than adding
bespoke plumbing, never delta-unfold a bundle def in simp. Only remove TODOs that are
done. Full `lake build Clean` + `lake build CleanTests` before any push (a partial build
once masked a broken file); commit in reviewable increments, append-only git.
