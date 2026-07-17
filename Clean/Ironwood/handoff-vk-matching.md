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

## mul_fixed stack (2026-07-18 continuation, in progress)

Gregor's follow-up goal: the mul_fixed stack — circuits, proofs, VK tests with OWN
fixtures. State:

**DONE (pushed, all green):**
- `Clean/Ironwood/Utilities/DecomposeRunningSum.lean`: strict `copy_decompose` bundle,
  soundness + completeness PROVEN (backward-chain lemma `chain_shifts` pins every
  interior running sum). Range-check gate = exact halo2 `range_check` fold AST, bridged
  to the donor `rangeCheckPoly`/`InRange` machinery by `eval_rangeCheckExpr`.
- `Clean/Ironwood/Ecc/MulFixed.lean`: core Config/coords-gate/configure +
  `assign_fixed_constants`/`process_window` pieces over `FixedBaseData` (proof-free
  data; donor `FixedBase.toData` bridges).
- `Clean/Ironwood/Ecc/MulFixed/BaseFieldElem.lean`: canonicity gate (exact AST),
  configure, full 4-piece synthesize. NOTE the z_0 aliasing: Rust binds
  `alpha := running_sum[0]` — all canonicity-region references use the z_0 CELL.
- Own fixtures via the sibling-checkout dumper (`layout_dump.rs::dump_layout_base_field`
  + LOCAL-ONLY `lean_dump_*` helpers in halo2_proofs/src/plonk/circuit.rs — replicates
  compress_selectors to get real SelectorAssignments): `BaseFieldLayout`/`BaseFieldSelMap`/
  `BaseFieldParams` fixtures + fixture generator
  (scratchpad `gen_bf_fixtures.py` — regenerate command in fixture headers).
- `TestVkLayoutBaseField`: ALL guards green (placements/copyList/σ/fixed).
- Framework: `enableEquality`/`enableConstant` dedup (Rust add_column semantics);
  `cellAt`/`cellVec`/`readCell` promoted to `Basic.lean`; `provable_type_simp`
  single-vector-eq fix (`obtain <ident>` on a bare Eq substitutes — skip the obtain);
  Layout machinery: `selectorFixed` dedups activations, new `regionAssignFixed`.

**REMAINING (the proof arc):**
- Bundle the inner region (copyDecompose ✓ done + fixed-constants coords facts +
  AddIncomplete window chain) as a FormalRegionCircuit; donor value algebra:
  `Orchard/Ecc/MulFixed/BaseFieldElem.lean` `RunningSumMul` (soundness 503-921,
  completeness 922-1297) + `MulFixed.FixedBase.coords_eq_windowPoint`/`partialSum`.
- Canonicity gate spec: donor `BaseFieldElem.Gate` (Spec/soundness ready to transplant).
- Top-level `FormalCircuit` (layouter): needs a positional/bundled witnessCheck13
  (currently a plain Circuit def — bundle it when proofs need the lookup facts, or
  positionalize `LookupRangeCheck.rangeCheck` like the short variant was).
- CS Pre/Post fixture (symbolic gates/queries, TestVkMatchMul-style) — needs a gate-AST
  emitter in the halo2_proofs local helpers; queued.
- full_width/short wrappers after base_field_elem.


## Sinsemilla/Merkle arc status (2026-07-18, overnight run)

All pushed, `lake build Clean`+`CleanTests` green, tree sorry-free:

- **Chain completeness closed** — the whole round/loop/slot/chain restructure is proven.
  Honest-prover runs require `ns ≠ []` (`Chain.ProverAssumptions`).
- **CS VK matches green**: `TestVkMatchSinsemilla`, `TestVkMatchMerkle` (pre+post).
  `SinsemillaChip::configure` made VK-exact (equality on all five advices, `q_s2`
  allocated inside, lookup-before-gates, Rust const-mul orientations — the eraser maps
  right-mul-by-const to `Scaled`). `MerkleChip::configure` ported (CondSwap + q_decompose).
- **Layout VK matches green end-to-end**: `TestVkLayoutSinsemilla` (6/6 copies, 12/12 σ,
  6241/6241 fixed), `TestVkLayoutMerkle` (17/17 copies, σ, fixed). New machinery:
  `assignedFixed` (in-region assign_fixed extraction), `dedupFixed`. Placement lines of
  both fixtures regenerated via a new sibling-checkout dumper
  (`halo2_gadgets/src/sinsemilla/layout_dump.rs`, local-only commit — same min-touched
  attribution bug as mul regions 3/6).
- **Rust-faithfulness refactors**: `shortRangeCheck` positional (no copy-in — Rust
  `short_range_check`) + `witnessShortCheck` layouter wrapper; Merkle `Gate` takes `l`
  from a constant (9 copies), both directions proven; `CondSwap.swap` gadget fully proven
  (Bool-valued swap program).
- **`hash_message` FORMAL bundle proven** (`HashToPoint.hashRegion`/`hashCircuit`): the
  public-Q init pins the chain's ∀-A contract to the hash from `Q`; Spec exposes chunking
  + ZsFacts + the flat `z1View`; ProverSpec the honest hash. Chain exports the public
  composition lemmas (`circuit_output_eval`(_prover), `output_point_x/y`).
- **`HashLayer.synthesize`** (Rust `hash_layer`) is real and layout-validated, consuming
  the formal hash bundle.

### Remaining (the ⊤-level proof compositions)

1. `HashLayer` as a `FormalCircuit` (Mul.lean-style layouter peel): children all proven
   (witnessShortCheck ×2, hashCircuit, Gate); the value glue is in place
   (`assemble` for soundness, `honest_pieces`/`honest_gate` for completeness; the z_1
   values come from the hash Spec's `ZsFacts`+`z1View` — unfold at `merkleNs`).
2. `Layer` = CondSwap.swap + HashLayer; `CalculateRoot` = the 32-fold
   (`merkleRoot_of_steps`/`honestNode` algebra ready).
3. `CommitDomain.commit` = hashCircuit + Ecc.Add + the abstract `MulFixed.FullWidth`
   boundary (`BlindSpecPinned` pattern; the mul_fixed arc on the other machine will
   discharge it).
