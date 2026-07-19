# Handoff: VK-matching arc

> **STATUS (July 18, 2026): the mul_fixed family is COMPLETE** — `base_field_elem`,
> `full_width`, `short`: circuits, VK layout fixtures + tests (all three entry points),
> and all proofs (inner + layouter bundles, soundness AND completeness) sorry-free.
> Shared proof infra lives in `Clean/Ironwood/Ecc/MulFixed.lean` (`chain_ladder`,
> `partialSum_congr`, bounds/eta helpers, `ofFn8_get_windowVal`,
> `addinc_output_cells`); `rangeCheckAt` (positional `witness_check` body) in
> `LookupRangeCheck.lean`. Storm-pattern notes: see the commit messages on
> `dd995c6d`..`a3e47935` (rw-vs-simp on chunk hypotheses, no chunk-typed `have`s,
> `seal <region> in` on consuming decls, explicit `@getElem!` spellings,
> explicit-output `ElaboratedRegionCircuit` instances).

# Ironwood arc status (was: VK-matching handoff)

## Action-circuit assembly arc (2026-07-18, in progress — "everything else" agent)

Gregor's split: the other agent owns the Sinsemilla ⊥-case specs + commit_ivk
bundling/proofs; this arc owns everything else. DONE so far (all pushed):
`Action/DeriveNullifier.lean`, `Action/ValueCommit.lean`, `Action/SpendAuthority.lean`
(knowledge-sound Specs at extracted witnesses), `Action/AddressIntegrity.lean` — all
fully proven; `CommitIvk/Gadget.lean` (structure-only stub, VK-exact region order);
`Ecc/Chip.lean` (EccChip::configure aggregate); `Action/Circuit.lean` (the FULL
`Circuit::configure`, VK-exact: q_orchard gate + all chips in Rust order).

REMAINING:
1. `assign_advice_from_instance` region op (framework: Operations.lean op +
   Constraints/ExtendsWitnesses cases + Lemmas circuit_norm + Fixtures/Layout
   compilation incl. the instance-side copy for σ) — needed only by the final
   `"Orchard circuit checks"` region.
2. `Action/Circuit.lean` synthesize: table load, witness regions (load private ×5,
   witness point cm_old, non-id g_d_old/ak_P/g_d_new/pk_d_new), Merkle root, the four
   proven composites via `.call`, commit_ivk stub call, note_commit old/new
   (`NoteCommit.Main.synth`), cm_old "constrain equal" region, constrain_instance rows
   (CV_NET_X/Y, NF_OLD, RK_X/Y, CMX + ANCHOR/ENABLE_SPEND/ENABLE_OUTPUT via
   assign_advice_from_instance), the q_orchard region. ScalarFixed/ScalarVar::new are
   region-FREE (lazy witnessing) — no regions for rcv/alpha/rivk/rcm/ivk wrappers.
3. STATUS 2026-07-19: ARC COMPLETE — TestVkMatchAction (CS pre+post) AND
   TestVkLayoutAction (regions/copies/σ/allFixed, 17566 cells) ALL GREEN against the
   real orchard Circuit. Layout-machinery additions: copyListDeferred (halo2-0.5
   planner order: constants deferred past the whole synthesis, constrain_instance
   copies inline advice-left), assign_advice_from_instance copies advice-left.
   Assembly merged onto the Bundle arc's stage-split Circuit.lean (abb981de).
   (superseded interim status: CS half DONE GREEN (TestVkMatchAction, both guards, first
   run). synthesize assembly DONE (region count 395 == dump exactly). ActionLayout.lean
   fixture generated+builds (regions/permcols F3=constants/copies 2964/σ 1602/fixed
   10186/constants 166; the two empty "constrain equal" regions store start 0).
   TestVkLayoutAction recipe settled (2026-07-19): use the REAL Action.Circuit.configure
   (CS already matches) with dump-derived aG (ncG pattern); mirror the synthesize with
   data-level mul_fixed calls (FixedBaseData: u := 0, point := 0 — only params matter
   for keygen fixed). ActionParams extraction from action_layout.json fixed data:
   z = F11[row], coeffs k = F(3+k)[row] at each mul region's start+window rows (fixed
   col map: F0-2 table, F3-10 lagrange, F11 fixedZ, F12/13 = qS2 sinsemilla1/2; 5 bases:
   valueCommitV short 22w, valueCommitR/spendAuthG/commitIvkR fw 85w, nullifierK bfe 85w;
   noteCommitR EXISTS = NoteCommitParams). Q on-curve proofs by decide (ncQ pattern).
   Guards per TestVkLayoutNoteCommit: copyList/σ/allFixed + region lockstep.
   REMAINING for TestVkLayoutAction: the data-level mirror synthesize (TestVkLayoutNoteCommit
   pattern — bundles → raw synthesize at FixedBaseData; needs param fixtures for the 6
   bases read off the dump's lagrange/fixed data + Q points + ncG-style generator table),
   PACKED/FILLS selector sections extraction, then the layout guards. Dump log:
   scratchpad action_dump.log; parse json: action_layout.json; orchard-side test:
   dump_layout_action (local commit).)
4. (was 3) VK fixtures: orchard checkout has `src/circuit/layout_dump.rs` (other agent's
   FullRecorder for NoteCommit) — add a whole-`Circuit` keygen-view dump test (real
   `Circuit::default()`); reuse halo2-side `lean_dump_cs_fixture`/`lean_dump_compressed`
   (from the mul_fixed CS arc) for configure-level Pre/Post; then
   `TestVkMatchAction` (CS) + `TestVkLayoutAction` (σ/regions/copies/fixed).

Live status log for the in-flight arcs, shared across machines. The original mul
VK-matching handoff is COMPLETE (mul is fully VK-matched, CS + layout — see
`Clean/Halo2/vk-matching-design.md`'s implementation-status banner for the machinery
summary); completed narrative sections were retired 2026-07-18.

## Settled rulings (don't relitigate)

- Generated layout fixtures' `maxRecDepth` is an accepted allowances exception (data-only,
  8–21s builds); chunked rendering is the eventual cleanup.
- halo2 dumper commits stay local to Gregor's machine.
- VK-matching target: the orchard `ebfull/ironwood` branch (`ironwood-dump` local branch
  in the checkout = ironwood + dump commits). The MAIN circuit is post-NU 6.3
  (`Action.Circuit.synthesize`, fixture `ActionLayout`); the pre-ironwood fixed post-NU
  6.2 circuit is `Action/CircuitPreIronwood.lean` (fixture `ActionBaseLayout`, and the
  proven `Action.Bundle` targets it). The CS is version-independent (verified: 6.2 CS on
  ironwood == 0.14.0 == 6.3 CS), so `ActionPre/Post/SelMap` are shared.
- Equality-set question resolved as a **layered structure**: core chip Pre/Post fixtures
  stay chip-only; the Layout fixtures index against an *orchard-consistent wrapper*
  (test-prelude `enableEquality` on all 10 advices — which also adds rot-0 queries);
  optionally dump a wrapper-level Pre to pin the wrapper CS.
- Sinsemilla/Merkle layout tests belong to the agent porting those files — coordinate,
  don't collide.

## Witness programs are the circuit INPUT, Unconstrained-style (2026-07-20)

Gregor's rulings: (1) private data enters through the circuit input like Clean/Orchard,
(2) with a real prover-hint type in the `Unconstrained` pattern — NOT an opaque
type-marker (the interim `ProverParams` commit was reverted), and (3) no adapter
wrappers — the bundle theorems themselves are stated input-style. Landed:
`Witnesses` is `F`-generic; `WitnessData F` is the evaluated prover view;
`PrivateInputs` (Circuit.lean) is the hint TypeMap — `Var = Witnesses F`,
verifier value erased, `evalProver` genuinely runs the witness programs
(WitgenIR eval for scalars/sibs, `Witgen.eval` for points/windows, closure
application for swaps). `main`/`mainPost` take `Var PrivateInputs Fp`;
`soundness`/`completeness`(`Post`) are restated at that main (proof bodies:
`W` ↦ the introduced `input_var`); `baseCircuit G B` / `circuit G B` /
`orchardActionCircuit` carry `PrivateInputs` as Input with no wrapper layer.
`ProverAssumptions` still states honesty at the extracted witness (input-level
PA via `WitnessData` is a possible later refinement).

## Concrete Sinsemilla generators — DONE (2026-07-19)

The last hypothetical constant is gone: `Orchard.Specs.Sinsemilla.orchardGenerators`
(`Clean/Orchard/Specs/SinsemillaGenerators.lean`, generated) carries the real 2^10-point
`S` table (extracted from the `ActionLayout` dump's fixed cols 1/2, python-validated)
with on-curve proofs via a linear list-walk checker + `decide +kernel`, reusing
`CertCheck.checkOnCurve(_sound)`. `orchardActionCircuit` now takes ONLY the witness
programs `W`; the layout tests' `aG` is the certified family, so the allFixed guard
cross-validates the extracted table against the dump on every CI run.

## ARC COMPLETE (2026-07-19): CONCRETE FixedBases — DONE, no workarounds

All six real orchard fixed bases are proof-carrying constants
(`Orchard.Ecc.MulFixed.Certs.*`, via `CertCheck.ofCert/ofCertShort` from
python-validated certificates; ~30s kernel verification each), `orchardBases` is the
complete concrete `Bases` (+ the three Q points), the layout tests run the REAL
circuits at it (mirror deleted), and `orchardActionCircuit` instantiates the proven
Bundle at the deployed constants. Evaluation (RULED by Gregor): the cert checks use
`native_decide` (~0.2s/base; approved trust extension) — `decide +kernel` (fully
kernel-checked, ~23s/base) was the original proof and remains a drop-in switch-back
(noted in each cert file); `rfl`/norm_num hit the heartbeat-counted elaborator
evaluator on this scale.

## (original plan, executed)


Goal: construct the six real `FixedBase`s (nullifierK, valueCommitR, spendAuthG,
commitIvkR, noteCommitR : `Orchard.Ecc.MulFixed.FixedBase`; valueCommitV :
`Short.FixedBase`) with all proof fields discharged, so the layout tests call the REAL
circuits and the Action bundle instantiates at the real Orchard constants.

The generation procedure (halo2_gadgets/src/ecc/chip/constants.rs):
- window table: `W[w][k] = [(k+2)·8^w]B` for w < N−1; MSB window
  `[k·8^(N−1) − Σ_{j<N−1} 2^(3j+1)]B` (mod q) — `compute_window_table`.
- Lagrange coeffs: degree-7 interpolation of the x-coords over k=0..7
  (`compute_lagrange_coeffs`); z/u: `find_zs_and_us` searches z per window with
  `u_k² = y_k + z` and `z − y_k` a NON-square for all k.
- The u tables and base points are Rust constants (orchard/src/constants/fixed_bases/*.rs
  — `GENERATOR`, `U`, `Z` arrays); dump them like the Q points (byte-array parse).

REVISED (Gregor 2026-07-19): define bases as the PROCEDURE's output, not as checked
tables — `FixedBase.ofBase B hB` smart constructor:
- `params w := lagrangeCoeffs ((windowPointFast B w ·).x)`, `(z, u)` from a ported
  self-checking `find_zs_and_us` (sqrt returns are self-certifying; non-square test IS
  the Euler exponentiation).
- GENERIC one-time theorems (no per-base field computation): `interpolate_eq` = the
  eval-at-node property of `lagrangeCoeffs` (64 concrete basis identities over the fixed
  nodes 0..7, or Mathlib `Lagrange.eval_interpolate_at_node`); on-curve of every window
  point from `Point.nsmul_onCurve`; `u_mul_u`/`z_sub_y_not_square` = the search's
  by-construction postcondition (`ZMod.euler_criterion` for the negative direction).
- Computational reflection ONCE: `smulFast` (binary double-and-add) with
  `smulFast n P = n • P` (from `nsmul_add_nsmul`) — needed because evaluating
  `ShortWeierstrass.smul` unfolds n≈2^255 times; this makes the derived tables
  kernel-computable (~2k curve adds per base).
- Per base, only three concrete `decide`s: `B.OnCurve`; the search succeeds; derived
  `toData` values = the dumped fixture values (the VK-matching content).
- REFINED (Gregor): witness everything, compute nothing in-kernel.
  (a) Incremental table: entries step by ONE addition (`(k+3)·8^w·B = (k+2)·8^w·B +
  [8^w]B`; step point 3 doublings/window) — ~930 curve ops/base, and NO smulFast needed
  (the chain induction on `nsmul_add_nsmul` is the whole bridge).
  (b) Witnessed slopes kill ALL inversions: per addition check `λ(qx−px)=qy−py`,
  `rx=λ²−px−qx`, `ry=λ(px−rx)−py` (3 mulmods); distinctness `qx ≠ px` is a plain
  literal disequality (decidable compare — NO witness needed on concrete values;
  Gregor). Dumper emits window tables (compute_window_table is pub) + a script
  computes slopes.
  (c) z SEARCH not re-run (dumped Z reach ~240k → ~1e5 Euler tests/window infeasible);
  z/u are certified inputs checked by the verifier form of find_zs_and_us.
  (d) Euler non-squareness is the ONLY surviving power (non-residuosity has no shorter
  certificate). SETTLED (Gregor): in-kernel binary Nat powMod (small files), no
  witnessed square chains. ~680 facts/base dominates the budget.
  (e) All checks as a Nat-level straight-line program (avoid ZMod instance-unfolding
  whnf overhead) with once-proven Nat↔ZMod op bridges.
  (h) DIRECTIVE (Gregor, final): AVOID `decide` — norm_num / simp-eval / reduce_mod_char
  are faster for pure value equations — or even plain `rfl` (kernel Nat-literal
  reduction is GMP-accelerated and skips the Decidable wrapper; benchmark it alongside). Consequences: NO Nat-level checker layer; Euler
  facts via the existing `rw [ZMod.euler_criterion ..]; reduce_mod_char` pattern
  (NormNum.PowMod, five_not_isSquare precedent); witnessed chain/slope/u checks stated
  as ZMod equations over dumped literals, discharged by reduce_mod_char/norm_num
  (generated files, batched `<;> reduce_mod_char`). The decide benchmark (g) stands
  only as a feasibility floor; first implementation step: benchmark the norm_num route
  the same way, then build the generators.
  (i) PROGRESS (2026-07-19, task #16 in flight): tactic benchmark SETTLED — rfl on
  Nat-stated fuel-based powMod ≈ free (~50ms/exp); ZMod-stated SAME algorithm times
  out >10min (>200x cliff: OfNat/cast towers + per-op ZMod-unfolding — see
  BenchFixedBase.lean) → checker equations at .val/Nat level, once-proven cast bridges
  to the ZMod facts. Window tables DUMPED: orchard local commit a9a9069
  (dump_fixed_base_tables → scratchpad base_tables.log, 3576 WPT lines, six bases,
  format `WPT w k (x-limbs) (y-limbs)`; GEN lines carry the base points). NEXT:
  slope/inverse-witness generation script (python: pow(x,-1,p)) + Lean fixture
  generation; then the generic lemmas (chain induction, eval-at-node, euler wrapper,
  zu-verifier postcondition); then ofBase + six bases.
  (j) CHAIN DESIGN (checker shape the fixtures must match): step points come FREE from
  the table — `S_w = [8^w]B = P_(w-1,6)` (k+2=8), `S_0 = B`. Checked ops per 85-window
  base: doublings `P_(w,0) = 2·S_w` (λ = 3x²/2y form; y≠0 generic from
  neg_five_not_isCube), in-window steps `P_(w,k+1) = P_(w,k) + S_w` (7×84), the MSB
  offset chain `T_j = T_(j-1) + P_(j,0)` (83 adds, T points witnessed, reusing the
  P_(j,0) entries; sum = Σ 2·8^j), `P_(84,0) = −T_83` (negation check, no slope), then
  7 MSB steps with `S_84 = P_(83,6)`. ≈678 ops/base; witnesses = slopes per op + the
  83 T points. Equations at .val level with `+p` for subtraction; lifted per-op by
  nondegenerateAdd_eq_add / a doubling analogue, stitched by the nsmul_add_nsmul
  induction. Short (22-window) analogous with its own MSB formula.
  (g) BENCHMARK DONE (Clean/Halo2/Tests/BenchFixedBase.lean, 2026-07-19): fuel-based
  binary `powMod` (structural, kernel-friendly) + 3000-step mulmod chain + 40-exp bulk
  all elaborate in ~3s TOTAL under kernel `decide +kernel`. ≈10-25ms per Euler exp →
  ~7-17s per base for the 680 facts; table checks negligible. Kernel decide is
  FEASIBLE — no comppoly escalation needed at this scale. Next: dumper window-table
  emission + slope script, then the Nat-level checker + generic lemmas (task #16).
  (f) If Nat-level checking benchmarks too slow: Gregor's team has faster CERTIFIED
  field arithmetic in the upstream comppoly repo (only `PrattCertificate` is vendored
  under `Clean/Orchard/Specs/CompPoly` so far) — vendor and swap the checker's field
  layer onto it rather than reaching for native_decide.

Superseded original plan (bulk-checking framing, kept for reference):
1. Window table in Lean by k-chains: start `(k+2)•B` (small, unary `nsmul` fine),
   then 3 complete-addition doublings per window step (2·n•P = n•P + n•P via
   `Point.nsmul_add_nsmul hOnCurve` — Pallas.lean:306). Generic lemma
   `chainTable_eq : chainTable B hB w k = windowPoint B w k` by induction (ONE shared
   proof, both 85- and 22-window and MSB variants). MSB window: compute
   `[k·8^(N−1)]B − [sum]B` via chains + `Point.neg`; bridge the mod-q `.val` scalar with
   `Point.nsmul_eq_zero_iff hOnCurve` (Pallas.lean:404 — prime-order curve, no
   per-base order proof needed).
2. `interpolate_eq` / `u_mul_u`: single bulk `decide` per base over a Bool program that
   computes the chain table ONCE (fold) and checks all 8·N equalities (ZMod eq on Fin p
   — GMP-fast; complete-add inversions via `ZMod.inv` = xgcd, also GMP).
3. `z_sub_y_not_square`: Euler's criterion — the repo's OWN pattern at
   `CompElliptic/Curves/Pasta.lean:62-65` (`five_not_isSquare`):
   `rw [ZMod.euler_criterion CARD (by decide : c ≠ 0)]; reduce_mod_char; decide`, where
   `reduce_mod_char` uses Mathlib `NormNum.PowMod` (fast modular pow). For bulk (680 per
   base ×6): either generate per-window lemmas, or (faster builds) a structurally
   recursive `powMod` + `powMod_eq_pow` bridge lemma + `euler_criterion` wrapper →
   ONE bulk `decide` per base. (`PrattCertificate.powMod` exists but is Id.run/while —
   not kernel-friendly; write the binary-recursive one, ~30 lines.)
4. `point.OnCurve`: `decide` (as `merkleQ_onCurve` already does).
Cost estimate: table ≈ 2k complete adds per base; Euler ≈ 680×255 mulmods per base —
seconds-to-minutes kernel time per base; fixture-style slow files are accepted.
Payoff: drop the data-level mirror from TestVkLayoutAction[Base] (call the real
synthesize), and instantiate the proven Action bundle at the real constants — the
end-to-end theorem about the deployed circuit.

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

**DONE (2026-07-18 continued):** full_width + short circuits (shared `windowChain`/
`coordsCheck`/toggle-parameterized `fixedConstantsLoop` refactor of the core), own
fixtures + `TestVkLayoutFullWidth`/`TestVkLayoutShort` — ALL THREE mul_fixed entry
points VK-layout-matched green. full_width input = `Unconstrained` window hints
(85 × FExpr; scalar is prover-side only). Short: 22 windows, msw region with sign row.

**REMAINING (the proof arc — the goal is NOT done until these are sorry-free):**
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
- full_width/short wrappers after base_field_elem: DONE at circuit+fixture level; their
  proofs join the same arc (short: donor `Short.lean` Gate + signed-magnitude algebra;
  full_width: donor `FullWidth.lean` + the extractor-form spec upgrade).

**Proof-arc progress (2026-07-18, working tree):** the base_field_elem INNER-REGION
bundle (`BaseFieldElem.inner`) SOUNDNESS IS FULLY PROVEN — decompose consumption via
bridges, the ∀-window coords/window-point fact (`hWP`, via `eval_interpolatedX` +
`readParams`/`interpolate_congr_params` + `shift_word_eq`), the complete 83-step
incomplete-addition ladder (opaque-scalar pattern; context-free bound lemmas
`base_bounds`/`step_bounds` because `omega` whnf-scans big hypotheses), the MSB row,
z-shifts. Key infra learned/added: region-level `FormalRegionCircuit.output_call`
(Subcircuit.lean), hand `copyDecompose_output`/`innerRegion_output_*` lazy projection
lemmas (rfl cliffs at concrete 85 — use the simp walk), `addinc_output`, donor
`inv_lt_card`/`step_sum_lt` de-privatized, `interpolatedX` unrolled (fold ASTs resist
`ring` under `Fin.succ` atoms; unrolled AST is data-identical — layout tests still
green). REMAINING sorry: `inner_completeness` (now a STANDALONE theorem — per-declaration
heartbeat budgets; contract fields factored into `InnerSpec`/`InnerEnvAssumptions`/
`InnerProverAssumptions` defs, pass them to `circuit_proof_start`'s list).

**inner_completeness state + the whnf-storm dossier (read before continuing):**
- PROVEN prefix: peel (append-lemmas ONLY — adding `*_nil`/`operations_pure` to the simp
  makes it hunt []-patterns and whnf the 85-window op lists), `hWdec/hWfix/hWchain`
  obtained, dec-child consumed via `SubcircuitRw.region_completeness_leaf_placed` +
  `region_completeness_derived_placed` + bridges (hDecC/hDecS reduce to clean
  cell-level facts), `hPA'`, honest `hZs` (z-cells = input shifts, on `window` via hZW).
- BLOCKER: ANY goal-splitting tactic after the prefix (⟨⟩-refine, And.intro-refine,
  constructor, or exact/convert on a conjunct) triggers ~515k `List.append` unfolds
  (`set_option diagnostics true`: List.append 515176, fixedConstantsWindow 85,
  assignFixed 765, loopAux 86 — the whole fixed-constants op list quadratically
  normalized) and blows the 200k budget. The SAME split succeeds under the LSP
  (bigger budget) with clean goals. Plain closing `sorry` (no split) builds.
- Completeness plan (unchanged): conjunct 2 = coords rows via B.interpolate_eq/u_mul_u/
  windowPoint_onCurve on honest digits (hZs + shift_word_eq + hWfix's fixed-value
  witness equations); conjunct 3 = per-addinc leaf lemmas + the honest partialSum
  ladder (mirror of the PROVEN soundness induction — reuse base_bounds/step_bounds);
  conjunct 4 (pure) = rw [RegionCircuit.operations_pure].
- Candidate storm fixes: (a) find why conjunct-granular isDefEq whnfs the chunk
  (suspect: mvar-motive instantiation over the ⊢-simp-rewritten goal), (b) restructure:
  state the three chunk-Constraints as standalone lemmas parameterized by the peel
  products and assemble with a single non-splitting term, (c) framework: a
  `constraints_of_chunks` splitter lemma applied via `apply` (no ⟨⟩ heuristics).

Also learned: `ElaboratedRegionCircuit.output_eq` is the bridge when h_output arrives
in elaborated-accessor form (a file-level `instance innerElab` changes the spelling);
`omega`/anonymous-⟨⟩ whnf-scan pitfalls; `Fin.mk`-val spellings normalize with
`rw [show ((⟨k, _⟩ : Fin n) : ℕ) = k from rfl]`.

**Proof-arc plan (worked out, next up):**
1. `MulFixed.windowChain` soundness/completeness lemmas over an abstract per-window
   fact family (the coords facts arrive from the toggled gate enables; the chain
   induction mirrors `MulIncomplete.loop_fold` with `partialSum` from the donor;
   `coords_eq_windowPoint` turns per-row gate facts + window values into window-table
   points). Bundle per wrapper (the row/word sources differ: running-sum words for
   base_field/short, witnessed window cells for full_width).
2. base_field_elem: inner bundle consumes `copyDecompose`'s Spec (already proven) —
   words = `V/8^w % 8` via the cast-word helper; canonicity gate + donor
   `BaseFieldElem.Gate` spec; `witnessCheck13` needs bundling (positionalize
   `LookupRangeCheck.rangeCheck` like the short variant, or a dedicated bundle whose
   Inputs are the α/z_84 cells and whose witgen builds α₀′ internally); top-level
   `FormalCircuit` with donor Spec `output = (α.val : Fq) • B`, Assumptions True.
3. full_width: top-level with extractor-form spec (`Witness := Fq` from the window
   cells — the requirements-doc upgrade of the donor's `∃ s, output = s • B`).
4. short: msw-region sign algebra (donor Short value lemmas), spec
   `∃ m < 2^64, magnitude = ↑m ∧ (sign = ±1 cases)`.
5. CS Pre/Post fixtures for the three chains (gate-AST emitter in the local
   halo2_proofs helpers) — the symbolic half of "match vk fixtures on all entry
   point circuits".


## Sinsemilla/Merkle arc: COMPLETE (2026-07-18)

All pushed, `lake build Clean` + `CleanTests` green, tree sorry-free: chain/hash_message/
HashLayer/Layer/CalculateRoot/CommitDomain proven; VK CS + layout tests green. Details in
git history (section retired).

## Poseidon arc: COMPLETE (2026-07-18)

Code is fully landed and sorry-free: Pow5 config + VK-exact gates, full/partial round
bundles, `permuteRegion`, layouter init/addInput + the hash `FormalCircuit`
(`Clean/Ironwood/Poseidon/{Pow5,Rounds,Permute,Hash}.lean`), Poseidon fixtures +
`TestVkLayoutPoseidon`. (This section had gone stale mid-sprint; details in git history.)

## NoteCommit/CommitIvk gate-layer arc (started 2026-07-18, goal-hooked)

Goal: steps 1-3 — canonicity/decomposition gates with phase-1-shaped semantic specs.

- DONE (pushed): `Clean/Ironwood/NoteCommit/Gates.lean` (11 VK-exact gates + configure,
  col_l/m/r/z = advices[6..10]); `Clean/Ironwood/CommitIvk/Gate.lean` (the 14-constraint
  two-row gate); `Clean/Ironwood/NoteCommit/Decompose.lean` — ALL FIVE MessagePiece
  bundles FULLY PROVEN (FormalRegionCircuit wrapping the Rust assign region; Spec =
  donor `Decompose*.Gate.Spec`; PA = honest decomposition over extracted readings).
- KEY PATTERN (Decompose completeness): abstract WitgenIR params sever the read↔program
  link, so use the MANUAL prefix `intro cfg offset; rw
  [FormalRegionCircuit.completeness_iff]; intro self env input_var input output h_input
  h_output hwit _hE hA hPA; simp only [circuit_norm, gate, boolCheck] at hwit h_input
  h_output hPA ⊢` — everything lands in READ language with hwit kept; land h_input via a
  `show`-rw to the literal GET-record + per-component `congrArg Inputs.<f> h_input`
  haves; close polys by rcases/ring + linear_combination.
- NEXT (canonicity bundles, `Clean/Ironwood/NoteCommit/Canonicity.lean`): Input = donor
  `*.Gate.Row` (ALL cells copied in the Rust assigns — pure-copy bundles, Witness :=
  unit), Assumptions = donor `Gate.Assumptions` (rely), Spec = donor `Gate.Spec`.
  For the VALUE ARGUMENTS: the DONOR-REPLAY bridge (tried in
  `Ironwood/NoteCommit/Canonicity.lean` ValueCanonicity.soundness, parked) gets the
  donor applied but main-Clean `const`'s toElements chain whnf-walls on the
  ConstraintsHold conversion. GO WITH THE FALLBACK: refactor the donor gates
  (`Clean/Orchard/Action/Canonicity.lean`, `CommitIvkGate.lean`) to expose row-level
  `spec_of_eqs (row) (hAss) (heq1) ... : Spec row` value lemmas — mechanical extraction:
  each donor soundness body already works over `input_*` component values after its
  peel; rename to `row.*` and have the donor soundness call the lemma. Ironwood
  soundness then calls the same lemma with its landed equations (watch ℕ-cast
  constants: donor spells `((2^8:ℕ):Fp)`, Ironwood gates `(2^8:Fp)` — push_cast or
  linear_combination absorbs). Completeness stays Ironwood-local (short boolean case
  splits; ValueCanonicity's is DONE and green as the template). (superseded plan: try the DONOR-REPLAY bridge first — apply the
  donor `Gate.circuit.soundness/completeness` (a main-Clean FormalAssertion) at offset 0,
  a trivial env, and CONST-lifted input expressions; the main-Clean ConstraintsHold
  reduce (simp [circuit_norm]) to exactly the Ironwood-landed field equations, so the
  donor's value proof is reused wholesale. If the replay fights main-Clean plumbing,
  fall back to refactoring the donors to expose row-level `spec_of_eqs`/`eqs_of_spec`
  value lemmas (mechanical: the donor proof bodies already work over `input_*` values).
  Gates: Gd (5 eqs), Pkd (4), Value (1), Rho (4), Psi (5), Y (7, advices[5..9] two-row),
  CommitIvk (14, two-row, advices[0..8]). Rust assigns: note_commit.rs 789-841 (g_d,
  all copies), 905-956 (pk_d), 994-1035 (value), 1098-1150 (rho), 1240-1274 (psi),
  1345-1409 (y — witnesses LSB and k_3 in-region from Value params, rest copies!),
  commit_ivk.rs 237-320 (all copies over two rows).
- THEN (step 3): `LookupRangeCheck.CopyCheck.Telescoped` bundle variant if missing
  (K-generic telescope value lemmas already ported), then the composite per-input
  canonicity bundles (donor `NoteCommit.{Gd,Pkd,Value,Rho,Psi,Y}Canonicity` in
  NoteCommit.lean = gate bundle + telescoped copy-checks, Spec = bit-slice payoff).

### NoteCommit arc — Step 2 COMPLETE (2026-07-18, pushed b2c6abc9)

All 12 gate bundles FULLY PROVEN with phase-1 semantic specs: Decompose B/D/E/G/H,
canonicity Value/Gd/Pkd/Rho/Psi/Y, CommitIvk. Donor gates refactored to row-level
`spec_of_eqs`/`eqs_of_spec` value lemmas (extraction is verbatim body-move + input_→row.
renames; donors' own proofs now call them). Wired into `Clean/Ironwood.lean`; full build
green, --wfail clean on my files.

Established patterns (beyond the earlier notes):
- Witnessed-bit gates (Y: LSB/k3; CommitIvk: b1/d1): witness programs as bundle params,
  readings in `Witness := fieldPair`; input-only rely-conditions in `Assumptions`, the
  witnessed-bit implications / booleanity move to `ProverAssumptions` (Y uses a
  conditional Spec: `IsBool out → DSpec …` since lsb's booleanity is enforced by the
  DECOMPOSE gates' bool_check on the copied cell, as in Rust).
- Index-cast spelling hazards: constraint-derived reads spell `↑(place self + offset)`
  (cast-of-sum), extract-derived Spec holes spell `↑place + ↑offset` (sum-of-casts), and
  row-1 sometimes `↑place + (↑offset + 1)` vs `… + 1` association. Fix: pin equation
  `have`s at the GOAL's spelling (never `_`-holes into `by`-wrappers — metavar
  corruption), `rw [hidx…]`/`▸` normalize hypotheses, `ring_nf at h ⊢` as last resort.
- `simp only [toDonor]` before `linear_combination` whenever the goal has stuck
  `(toDonor …).field` projections.

### Step 3 REMAINING (the composites)

- Lookup infra: `copyCheck` (toFormal of rangeCheck; Spec exposes z0 = element + the
  TELESCOPED decomposition ∃ lo < 2^(K·numWords), … ✓) and `rangeCheckAt` (positional,
  mul agent) EXIST. MISSING: the word-wise `witness_check` wrapper (Rust
  `lookup_range_check.rs:witness_check` — witness element from a program + range check;
  mirror `witnessShortCheck` but over `rangeCheckAt K numWords strict`).
- Then the six composite canonicity bundles (donor `NoteCommit.{Gd,Pkd,Value,Rho,Psi,Y}Canonicity`
  in `Clean/Orchard/Action/NoteCommit.lean` 1112-1445 + YCanonicity 525-646): layouter
  FormalCircuits = witness_check region(s) for the shifted values (a', b3_c', e1_f',
  g1_g2', j', j) + the gate bundle region; Assumptions = the remaining rely (ranges,
  running-sum tails from Sinsemilla zs); Spec = the donor composite bit-slice payoffs.
  Layer-compose pattern: Merkle.Layer / CommitDomain (2-child layouter, h_spec auto-lift).
- CommitIvk composite analogue lives in donor `CommitIvk.lean` (uses the same shape).

### Step 3 continuation notes (post-52ad905d)

- `LookupRangeCheck.witnessCheck` (word-wise Rust `witness_check`) ADDED — assignRegion
  "Witness element" (assign from program + `rangeCheckAt.call`).
- CONTRACT FIX REQUIRED before the composites: the canonicity gate bundles currently
  carry the shift equations (`aPrime = a + 2^130 − tP` etc.) in `Assumptions`, mirroring
  the donors — but the composite CANNOT supply them soundly (phase-1's Telescoped child
  pinned z0 = the input EXPRESSION; Ironwood's positional `witnessCheck` only pins
  z0 = the read). The gate itself enforces the shift (the `a_prime_check`-family
  constraints my bundle soundness currently IGNORES). Rework per canonicity bundle
  (Gd/Pkd/Rho/Psi/Y + CommitIvk's two shifts): move the shift conjunct(s) from
  `Assumptions` to `ProverAssumptions`, and in soundness derive them from the landed
  shift constraints (`by linear_combination -hapC`-style) before calling `spec_of_eqs`.
  (The donor row-lemmas take the shift via hAss — construct hAss from hA + the derived
  shift.) Completeness unchanged except PA now carries the shift (the honest prover
  computes a' by that very formula).
- THEN the six composites: Input = {piece cells + subpiece cells + Sinsemilla z-tails};
  synthesize = witnessCheck(s) for the shifted value(s) (programs computing
  `readCell a + 2^130 − tP` etc.) + assignRegion(gate bundle .call) — Rust region
  sequence per note_commit decompose/canonicity flow; Assumptions = donor composite
  Assumptions (IsBool b1, ranges, z13A = a/2^130 …); Spec = donor composite Spec
  (bit-slice payoffs, NoteCommit.lean 1112-1445). 2-child layouter compose w/ h_spec
  auto-lift; the gate child's PA gets the shift + witnessed-bit facts from the
  witnessCheck child's derived facts + own PA.

- CONTRACT FIX progress: Gd/Pkd/Rho DONE (template: rw the shift constraint's copies
  (`rw [hc-args] at hg2`), `have hshift := by push_cast at hg2 ⊢; linear_combination
  -hg2`, construct the donor hAss tuple with hshift in the donor position; completeness
  hAss-tuple takes hPA.2 in that slot, spec from hPA.1). REMAINING: Psi (shift = g1 +
  g2·2^9 + 2^130 − tP, constraint hg2, donor slot 5 of 7-tuple ⟨hh1, g1_lt, g2_lt,
  h0_lt, hg1g2P, hz13G, hzgDec⟩ — my Psi Assumptions must become input-only 6-tuple),
  Y (jPrime shift from hjpc, my Y Assumptions conjunct 4 → PA), CommitIvk (TWO shifts
  from hapC/hb2cpC — donor hAss slots 6 and 10 of the 13-tuple; my 11-conjunct
  Assumptions drops slots 6/9 → 9 conjuncts, PA gains both).
- THEN: the six composites per the earlier notes (witnessCheck child + gate child).

## Step-3 composites: state as of 179d46f5

DONE (fully proven, in `Clean/Ironwood/NoteCommit/Composites.lean`):
- Gd/Pkd/Rho/Psi canonicity composites (`*CanonicityCheck.circuit`), each a two-child
  layouter FormalCircuit = `witnessCheck` region + gate-bundle `.toFormal` region.
  THE FILE ITSELF IS THE TEMPLATE — parameterized `rangeCheckAt_*_eq` bridges at the top
  (rfl, child stays folded), `synth_regionCount` via `FormalCircuit.call_regionCount`,
  soundness = peel (`simp only [synth, witnessCheck, circuit_norm] at hc`) →
  `subcircuit_rw at hWC/hGate` → discharge → donor `Gate.Spec` projections; completeness =
  `subcircuit_rw` → replay child contract via `h_spec_0` → tail vanishing via
  `base_val_lt_tP_val`/`high_bit_canonical` + `shifted_high_zero`.
- Value composite = `ValueCanonicity.bundle` itself (donor composite is gate-only).

STEP 3 COMPLETE as of 04bea3a6. All six canonicity flows (Gd/Pkd/Value/Rho/Psi/Y) plus
CommitIvk are covered by fully-proven composites:
- Clean/Ironwood/NoteCommit/Composites.lean (Gd/Pkd/Rho/Psi; Value = ValueCanonicity.bundle)
- Clean/Ironwood/CommitIvk/Composite.lean
- Clean/Ironwood/NoteCommit/YComposite.lean (five children; new infra:
  LookupRangeCheck.chain_read + rangeCheckAtDecomposed (numWords-generic, keeps the loop
  folded) + witnessCheckDecomposed)

Y-composite patterns worth reusing:
- Bundled-call witness opacity: to read a gate child's in-region witness programs from the
  parent (lsb/k3), prove a per-child projection lemma
  `ExtendsWitnesses place env (((child.call cfg row).operations i)) i =
   RegionOperations.ExtendsWitnesses place i env ((bundle.synthesize cfg 0 row).operations i)`
  by `simp only [childDef, FormalRegionCircuit.toFormal, FormalCircuit.call,
  Circuit.operations, assignRegion, ExtendsWitnesses, and_true]; rfl`, rw it at the hwit
  chunk AFTER subcircuit_rw (rewriting before breaks the engine's chunk matching), then
  destructure like the bundle's own completeness.
- Non-vacuous child ProverAssumptions on extraction data need the haves stated in the
  goal's extract spelling: `(show Fp from (child).extract … ⟨place,env⟩.toEnvironment).val`
  with an extract→advice rfl/simp bridge.
- Witness the honest values by canonical bit-slice programs (not by replaying the Rust
  value dataflow) whenever the payoff is a bitrange fact — the parent then gets the value
  equations directly from its own hwit (no cross-child value plumbing).

NEXT (beyond the original steps 1-3 scope): the NoteCommit main circuit itself, composing
the decompose bundles + these composites + Sinsemilla, per the donor
Orchard.Action.NoteCommit top level.
## Ironwood (post-NU 6.3) Action bundle — COMPLETE (2026-07-19)

The retargeted MAIN circuit (`Action.Circuit.synthesize` = base + cross-address) is now
fully proven, layered on the base bundle **as a subcircuit**:

- `synthCrossAddressChecks` retyped over `Var AddressPoints Fp` (the Rust
  `AddressPoints`; new `ProvableStruct` in Circuit.lean) and its raw `for … in [0:4]`
  loop swapped for `RegionCircuit.forRange'` — the `circuit_norm ↓` split lemmas then
  hand both proof directions the per-row `∀ i : Fin 4` form for free.
  `synthesizeBase` (the three stages, returning the points) is the shared base;
  `CircuitPreIronwood.synthesize := synthesizeBase`. Region stream unchanged —
  TestVkLayoutAction/Base both green, no fixture churn.
- The pre bundle was reshaped to `baseCircuit : FormalCircuit … unit AddressPoints`:
  concrete `elaborated` output (the four witnessed point cells at i₀+3/301/347/348,
  `output_eq` by `with_unfolding_all rfl`), `Spec := SpecBase ∧ output-tie clauses`
  (ties close by `congrArg … h_output` + rfl). `ActionData`/`extract` gained
  `disableCrossAddress` (instance row 9) — additive, base proofs untouched otherwise.
- The post bundle (`Action.Circuit.circuit`, the MAIN bundle) is small:
  `mainPost = (baseCircuit …).call + synthCrossAddressChecks`. Soundness:
  `subcircuit_rw` on the call delivers the whole base Spec in one step; the region
  gives four `dca·(old−new) = 0` products → `SpecPost`'s clause
  (`disableCrossAddress ≠ 0 → gdOld = gdNew ∧ pkdOld = pkdNew`) by
  `mul_eq_zero`/`sub_eq_zero` + `Point.ext_coords`. Completeness: ONE
  `layouter_completeness_leaf` on the base call (PA = base PA projected from
  `ProverAssumptionsPost`), then per-row EW equations + `linear_combination` off the
  honest products. Extractor composition is literal: post extract = base extract.

## E2E Action circuit bundle (base stages) — COMPLETE (2026-07-19)

`Clean/Ironwood/Action/Bundle.lean`: the whole-circuit `FormalCircuit Fp Unit Config
unit unit` over the 394-region `synthesize`, soundness AND completeness fully proven,
`circuit` bundled, imported by `Clean/Ironwood.lean`.

- **Contract**: `ActionData` (9 primary-instance rows + shared witness cells + the six
  witnessed points + merklePath + five `fwExtract` window/scalar readings); `extract`
  reads it off the region map documented at `synthesize_regionCount`. `Spec` is the
  §4.17.4 statement, breaks-as-data (`SpecOrBreak`) for the three Sinsemilla legs,
  knowledge-sound at the extracted data. `EnvAssumptions` = GeneratorTableExact
  (sinsemilla1's own load, needed for load completeness) + 4× GeneratorTableLoaded +
  the mul-family env facts + range TableLoaded + qLookup≠qRunning.
- **Proof idioms that made it go through** (see also the NoteCommit sections): stage
  split (`synthWitness`/`synthChecks`/`synthNotes`) against kabstract walls; per-child
  concrete `*_call_regionCount`/`*_spec_eq`/`*_pa_eq` rfl-bridges + record-eval
  transports (`XInputs_eval_eq(_prover)`); goal-side `refine ⟨?_, ?_⟩` BEFORE
  per-stage simp; derived contracts (`layouter_completeness_derived`) established
  before the leaves so honest cell values (`hCVval`/`hSAval`/`hDNval`/`hNCoval`/
  `hNCnval`/`hIvkVal`/`hM1mid`/`hM2root`) exist for equal-region/instance/gate goals.
- Merkle: `CalculateRoot` generalized to `(l₀ d, l₀ + d ≤ 2^10)` (Rust layers_per_chip
  = 16, two chips); `ProverSpec` strengthened to the pathNode-landing fact; the two
  chained fold calls tie via `pathNode_congr`/`pathNode_congr₂` + `MerkleRoot.trans`.
- The orchard-gate region completeness reverses the soundness recipe: normalize
  `nextRegionIndex_constrainInstance`, discharge the 8 copy/instance equalities from
  the region's ExtendsWitnesses conjuncts, then `linear_combination` the four gate
  polys from the PA value checks after rewriting reads through those equalities.
- No VK fixture work here (TestVkMatchAction/TestVkLayoutAction already green, see the
  assembly arc above).

## Breaks-as-data (ironwood#45) + CommitIvk main — COMPLETE (2026-07-19)

- `Clean/Orchard/Specs/SinsemillaBreak.lean`: `BreakData`/`hashToPointB` Σ-refinement
  of the ⊥-chain, projection lemma to §5.4.1.9, `ValidBreak` (computational Thm 5.4.4:
  honest prefix + resolved escape equation), `SpecOrBreak`, and the one-line
  `breaksOfGuarded` soundness-upgrade bridge.
- Relations restated as `SpecOrBreak` (prover-side stays guarded): donor
  `NoteCommitRelation`, donor `CommitIvk.Spec`, `AddressIntegrity.Spec`'s ivk clause,
  Ironwood `NoteCommit.Main.Spec`. All soundness proofs upgraded via the bridge; the
  guarded bodies slot in unchanged.
- **CommitIvk main circuit** (`Clean/Ironwood/CommitIvk/Main.lean` + `MainBundle.lean`):
  14-region `synth` (7 pieces/shorts, 4-region `short_commit` via `CommitDomain.commit`
  at `ns = [24,0,23,0]`, the proven 3-region Canonicity composite as a unit — contiguous
  in Rust), output = extracted x-coordinate. Soundness AND completeness fully proven;
  `Spec` breaks-as-data from the start; bundled `circuit`; imported by
  `Clean/Ironwood.lean`. The structure-only `Gadget.lean` stub was replaced by this
  (Action/Circuit.lean repointed). No VK layout fixture for CommitIvk-main yet (the
  orchard dumper pipeline from NoteCommit applies directly when wanted).

## NoteCommit main — COMPLETE (2026-07-18)

The full goal is done: `Clean/Ironwood/NoteCommit/Main.lean` (defs/contract layer) +
`MainBundle.lean` (soundness AND completeness fully proven, `circuit` bundled, imported
by `Clean/Ironwood.lean`) + VK layout matched. VK fixture chain:
- orchard-crate dumper `orchard/src/circuit/layout_dump.rs` (LOCAL-ONLY commit in the
  sibling orchard checkout; `[patch.crates-io]` to the sibling halo2 for the
  `lean_dump_*` helpers; vendored `FullRecorder`/`full_dump`). Dump circuit = the
  `note_commit::tests` harness truncated after `gadgets::note_commit` (keygen view).
- fixtures `NoteCommitLayout` (constants map + expanded table fills, fixed list chunked
  against elaboration limits) / `NoteCommitSelMap` / `NoteCommitParams` (the NoteCommitR
  window table read off the mul rows).
- `TestVkLayoutNoteCommit`: full configure chain (range check, sinsemilla, 11 NoteCommit
  gates, whole `EccChip::configure` registration sequence) + the 49-region synthesize
  mirror (commit block mirrored data-level via raw `FullWidth.synthesize` on the dumped
  params — `Main.synth` takes a proof-carrying `FixedBase`, and `indexedRegions`
  recurses through subcircuit wrappers so the region stream is identical). ALL guards
  green: names lockstep, copyList, σ, full fixed contents.
- NOTE: `CommitDomain`'s add region renamed "M + [r] R" → "complete point addition"
  (the Rust region name).

## NoteCommit main — assembly design (read note_commit.rs:1596-1800 alongside)

Goal (active hook): fully port NoteCommit + deps, proven bundles + VK matching.
CommitDomain de-abstraction DONE (24cdc725): commit now composes MulFixed.FullWidth
directly; scalar = extraction data (fwExtract), validity via FixedBase.smul_valid.

KEY LAYOUT FACT: Rust's region order interleaves — the four canonicity witness_checks
(a'/b3c'/e1f'/g1g2') run mid-flow, the TEN gate regions all run at the END. So the
Gd/Pkd/Rho/Psi composites (witnessCheck+gate contiguous) canNOT be called as units in
NoteCommit (wrong region order for VK layout). Main calls the individual bundles in
Rust call order; the composites' soundness scripts are the exact glue template to
inline. The Y composites ARE contiguous in Rust and are called as units. CommitIvk
composite: verify commit_ivk.rs region order before reusing it in its parent.

Region sequence (ns := [25,1,25,6,1,25,25,1]; pieces a..h):
 1 piece a (witnessMessagePiece, aWit = br(gdX,0,250))
 2 short 4 b0=br(gdX,250,4)   3 short 4 b3=br(pkdX,0,4)     4 piece b (b0+b1·2^4+b2·2^5+b3·2^6)
 5 piece c (br(pkdX,4,250))
 6 short 8 d2=br(value,0,8)   7 piece d (d0+d1·2+d2·2^2+d3·2^10, d3=br(value,8,50))
 8 short 6 e0=br(value,58,6)  9 short 4 e1=br(rho,0,4)      10 piece e (e0+e1·2^6)
11 piece f (br(rho,4,250))
12 short 9 g1=br(psi,0,9)     13 piece g (g0+g1·2+g2·2^10, g0=br(rho,254,1), g2=br(psi,9,240))
14 short 5 h0=br(psi,249,5)   15 piece h (h0+h1·2^5, h1=br(psi,254,1))
16-20 YCanonicityCheck.circuit (wlsb=br(gdY,0,1)) input {y:=gdY} → b2 cell
21-25 YCanonicityCheck.circuit (wlsb=br(pkdY,0,1)) input {y:=pkdY} → d1 cell
26-29 CommitDomain.commit G ns R windows Q … input {pieces := #v[a..h]} → cm point
      (blind 2 regions at 26/27, hash at 28, add at 29)
30 witnessCheck 13 aPrimeWit(aPiece)       31 witnessCheck 14 b3CPrimeWit(b3,c)
32 witnessCheck 14 e1FPrimeWit(e1,f)       33 witnessCheck 13 g1G2PrimeWit(g1, z1_g cell)
34 (DecomposeB.bundle wb1=br(gdX,254,1)).toFormal {b, b0, b2:=Ygd-out, b3} → b1
35 (DecomposeD.bundle wd0=br(pkdX,254,1)).toFormal {d, d1:=Ypkd-out, d2, d3:=z1_d} → d0
36 DecomposeE.bundle.toFormal {e, e0, e1}
37 (DecomposeG.bundle wg0=br(rho,254,1)).toFormal {g, g1, g2:=z1_g} → g0
38 (DecomposeH.bundle wh1=br(psi,254,1)).toFormal {h, h0} → h1
39 GdCanonicity.bundle.toFormal {gdX, b0, b1, a, aPrime:=r30.z0, z13A:=z13_a, z13APrime:=r30.zLast}
40 PkdCanonicity.bundle.toFormal {pkdX, b3, d0, c, b3CPrime:=r31.z0, z13C:=z13_c, z14B3CPrime:=r31.zLast}
41 ValueCanonicity.bundle.toFormal {v:=value, d2, z1D:=z1_d, e0}  (check Row field names!)
42 RhoCanonicity.bundle.toFormal {rho, e1, g0, f, e1FPrime:=r32.z0, z13F:=z13_f, z14E1FPrime:=r32.zLast}
43 PsiCanonicity.bundle.toFormal {psi, h0, g1, h1, g2:=z1_g, g1G2Prime:=r33.z0, z13G:=z13_g, z13G1G2Prime:=r33.zLast}

Hash z cells (positional, hash region iH = i₀+28, column hcfg.bits, offset base 0):
z(i,j) = AssignedCell.of iH (prefixRows ns i + j) hcfg.bits; iH = i₀+27 (NOT +28); prefixRows for ns:
[0,26,28,54,61,63,89,115]. z13_a=(0,13)→row 13; z13_c=(2,13)→41; z1_d=(3,1)→55;
z13_f=(5,13)→76; z1_g=(6,1)→90; z13_g=(6,13)→102.

Main.circuit params: (R : FixedBase) (windows : Vector (FExpr Fp) 85) (G Q hQ …).
Inputs {gdX gdY pkdX pkdY value rho psi}. Output Point (cm).
Config: (NoteCommit.Config × HashPiece.Config × LookupRangeCheck.Config 10 ×
MulFixed.FullWidth.Config × Ecc.Add.Config), configure := pure (NoteCommit.configure
in Gates.lean is the VK-exact gate registration; the outer test circuit composes).
Spec target: donor Orchard.Action.NoteCommit top-level Spec.

Plan: (1) Main.lean defs (witness programs + synthesize + regionCount) compile-clean,
commit. (2) soundness/completeness (the giant compose; inline the Gd/Pkd/Rho/Psi
composite glue; keep proofs local until sorry-free). (3) VK layout fixture: needs a
dump harness for orchard's note_commit test circuit (orchard crate, not halo2_gadgets —
FullRecorder is pub(crate) there; vendor or expose), convert_dump.py, fixture files,
TestVkLayoutNoteCommit.

## NoteCommit bundle phase (next; defs milestone a5328282 DONE — Main.lean compiles)

Main.lean synth compiles with all ~30 children wired (iHash = i₀+27; currentRegion
primitive anchors positional zCells). Next: the FormalCircuit bundle around synth.

Donor top-level to mirror (Clean/Orchard/Action/NoteCommit.lean:1806-1930 + 2523):
- Spec = NoteCommitRelation G Q R input cm; PA = ProverNoteCommitRelation-side
  (OnCurve gd/pkd, value < 2^64, rcm canonical, honest hash defined).
- Ironwood deltas: Inputs are coordinate CELLS {gdX gdY pkdX pkdY value rho psi};
  rcm scalar = FullWidth extraction data (CommitDomain pattern: wit.2.2-style);
  Assumptions = gd/pkd OnCurve stated on the coord evals.
- REUSE the donor value-theory connectors (all value-level, no circuit traces):
  PieceExtraction section — MessageCellFacts, pieceBounds_of_cellFacts,
  noteCommitChunks / noteChunksOfScalars / note_chunks_eq_of_cellFacts,
  honestChunks_eq_noteCommitChunks_of_cellFacts, z13G_tail_of_decompose_g,
  valueCanonicity_assumptions_of_commit (donor NoteCommit.lean 1600-1800, 1880-2520).
  The Ironwood soundness = 30-child subcircuit_rw peel (template: the composite
  soundness scripts in Composites.lean/YComposite.lean/CommitIvk/Composite.lean,
  esp. chaining witnessCheck telescopes into gate-bundle rely-conditions) + these
  donor connectors for the value algebra.
- Witness/extract: ChainWit (hash) × fwExtract (scalar) × per-gate bit cells as needed;
  output = Point (cm).
- Proof scale: expect the largest proof in the tree; keep the bundle LOCAL (uncommitted)
  until sorry-free; sub-lemmas that are pure value algebra may be committed early.

VK fixture (parallel track): needs orchard-crate dump harness (halo2_gadgets
FullRecorder is pub(crate) — expose or vendor into orchard test), the note_commit
test circuit (note_commit.rs:2054+) as dump target, convert_dump.py, fixture files,
TestVkLayoutNoteCommit mirroring TestVkLayoutPoseidon.

### synth_regionCount blocker (Main.lean, = 43)
The one-shot simp peel leaves 13 folded call chunks; `rw` on them (even with
specialized per-child rfl-bridges `toFormal_call_regionCount`/`yc_call_regionCount`/
`commit_call_regionCount`, and even with the circuits `seal`ed) hits the 200k-heartbeat
isDefEq wall — kabstract tries defeq of the pattern against every other chunk.
`simp only [bridge]` never fires on call chunks (known simp-vs-rw asymmetry).
`with_unfolding_all rfl` on the whole thing fails (not defeq at rfl).
RECOMMENDED FIX: split synth into 3 stage defs (pieces 15 regions / checks 18 =
2×Y(5)+commit(4)+4 wchecks / gates 10), prove each stage's count separately (small
goals, short rw chains), combine. The stage split will also make the 30-child
soundness peel tractable (hc splits into 3 then further). Cells thread across stages
via small record types. The bridges compile and are kept... (removed with the failed
lemma — recover from this note or git history at the failed attempt).

## NoteCommit soundness state (MainBundle.lean WIP, un-imported)

WORKING (compiles, ~10s): circuit_proof_start → 3-stage peel → stage 1 (7 short-check
bound facts hb0..hh0 in read language) → stage 2 (hY1S/hY2S IsLowBit conditionals at
the lsb cells (i₀+15+4)/(i₀+15+5+4) advices6; hCmS = commit chunks/ZsFacts/point
contract; 4 telescope facts haz0/htelA..hgz0/htelG) → pieceChunks_donor_iff bridge
(unlocks donor pieceChunks_val_lt + chunk-equality connectors).

KERNEL CLIFF hit at stage 3: normalizing hGt's indices (Operations.regionCount simp +
yc/commit rw + 9× toFormal_call_regionCount rw) exceeds the kernel budget when inlined.
FIX (per doc/performance-problems.md "kernel size cliffs"): factor the three stage
peels into standalone private lemmas, each kernel-checked alone:
  private theorem peelGates (cfg input pcs ccs iHash i₀ place env)
    (h : Constraints place env ((synthGates cfg input pcs ccs iHash).operations i₀) i₀) :
    <10-conjunct of folded gate-call chunks at clean numeric indices>
(statements = the folded `(bundle.toFormal name).call` chunks subcircuit_rw expects, at
i₀, i₀+1, ..., i₀+9; proofs = the existing simp/index-normalization + exact). Same for
peelChecks (indices i₀..i₀+17: Y at i₀/i₀+5, commit i₀+10, wchecks i₀+14..17) and
optionally peelPieces. Main soundness then applies these and stays small. Bridges for
stage 3 already in the file: toFormal_{spec,assumptions,envAssumptions,extract}_eq
(generic), decomposeB/D/G/H_output, toFormal_call_regionCount.
Remaining after stage 3: A-discharges for the 5 canonicity gates (chain telescope
facts + piece bounds via pieceChunks_val_lt/donor bridge + hb0.. shorts + hGbS
booleans — exactly the Composites.lean glue), then the donor chunk-equality assembly
(pieceChunks_eq_noteCommitChunks_of_indexed_piece_values, NoteCommit.lean:447/1661)
to land Spec. Then completeness (mirror), circuit def, VK fixture.

### NoteCommit soundness: z-value plumbing (next block)
Peel now complete through clean read-language facts (a6eb4489). Next: the six hash
z-cell value facts (z13_a/z13_c/z1_d/z13_f/z1_g/z13_g). Route:
1. zsFacts_donor_iff (mirror pieceChunks_donor_iff; HVec/zLengths defeq across trees).
2. donor zsFacts_cell (NoteCommit.lean:1525): PieceChunks+ZsFacts → zs[i][r] =
   ↑(pieces[i].val / 2^(10r)).
3. extract-side: hashCircuit.extract's .zs = eval of Chain.zsCellsVal (rfl at
   HashToPoint.lean:314-317) + Chain.eval_zsCellsVal → zsFam f — then getElem of zsFam
   at (i,r) = f (prefixRows ns i + r) = env.advice bits ↑(place iH + prefixRows+r)
   (zsFam_elems / z1View_zsFam patterns in HashToPoint.lean:76-127).
Then the canonicity-gate A-discharges: Gd = ⟨hGbS.1 (b1 bool), piece-a bound
(pieceChunks_val_lt via donor bridge, idx 0), hb0, hz13a, telescope ⟨loA,...⟩ via
haz0/htelA⟩ — mirror Composites.lean; then Pkd/Val/Rho/Psi; then the donor
chunk-equality assembly (pieceChunks_eq_noteCommitChunks_of_indexed_piece_values +
gate Specs) to land Spec at the extracted scalar (commit's wit.2.2 = rcmExtract via
commit_extract_eq at i₀+25 spelling).

### CRITICAL CORRECTION (found via donor zsFacts_cell bound): ns convention
Chain's ns entries are WORDS − 1 (donor messagePieceRounds = [24,0,24,5,0,24,24,0]).
Main.ns := [25,1,25,6,1,25,25,1] is WRONG. Fix to [24,0,24,5,0,24,24,0]. Cascades:
- zCell rows (zLengths = [25,1,25,6,1,25,25,1] cells/piece; piece starts
  [0,25,26,51,57,58,83,108]): z13_a=13, z13_c=39, z1_d=52, z13_f=71, z1_g=84, z13_g=96.
- zs_get_* lemma literals accordingly.
- hpos (∀ x ∈ ns, 0 < x) FAILS for the zero entries: hashCircuit's z1s output
  (z1View, Merkle sugar) requires every piece ≥ 2 words. NoteCommit needs a
  point-only hash variant WITHOUT hpos: add hashRegionP/hashCircuitP in
  HashToPoint.lean (same proofs minus the z1s clause), switch CommitDomain.commit to
  it and DROP its ns_pos parameter; Main drops ns_pos. Merkle keeps the z1s variant.

### NoteCommit completeness route (soundness DONE at f838d63d)
Stage-1/2 witness facts + generic toFormal_call_witnesses land (9f5b9f47). The
goal-side one-shot stage simp + subcircuit_rw hits the kernel cliff (like stage 3 of
soundness). FIX: (a) build-direction stage lemmas (mpr of the peel pattern):
buildSynth/buildPieces/buildChecks/buildGates — `<child-chunk conj at clean indices> →
Constraints ((stage).operations i) i`, each kernel-checked alone; (b) discharge each
child chunk MANUALLY via the SubcircuitRw completeness leaves, Merkle-style
(Merkle.lean:1375: `refine Halo2.SubcircuitRw.layouter_completeness_leaf_placed child
cfg idx ⟨place,env⟩ _ hWchunk ⟨envA, A, PA⟩` — and region_completeness_leaf(_placed)
for in-region children), which also provides the child Spec/PS facts needed by later
children's PAs (commit PS → gate PAs; the per-gate witnessed-bit facts via
toFormal_call_witnesses + per-bundle synthesize simp destructure — bundle-completeness
hwit pattern). PA sources: shorts = hw* bitrange bounds (cast_bitrange_val+bitrange_lt);
Y children PA (IsLowBit) = from hwit-projected wlsb equations (brWit gdY 0 1 →
isLowBit_iff_mod_two + bitrange%2); commit PA = PieceBounds (hw pieces + tiling like
donor pieceBounds_of_cellFacts — donor lemma reusable at the read-cells record!),
∃B honest hash (top hPA hB0 + honestChunks_eq_noteCommitChunks_of_cellFacts), window
bounds (top hPA hWin, spelling via rcmExtract); gate PAs = mirror the composite
completeness glue (Composites.lean PA branches) with hwit facts + child PSs.

### Completeness remaining (after 4108df7f: 11/24 leaves done; ALL witness
projections landed — hwb1/hwd0/hwg0/hwh1 (peelGatesW + toFormal_call_witnesses +
bundle simps) and hwb2/hwd1 (yc_lsb_witness two-level projection) are read-language
bit equations; the 15 piece/short equations hwa..hwh are in context)
Order of the remaining work (13 leaves: Y1, Y2, commit, 10 gates):
1. Witness projections FIRST (needed by everything below):
   - per-gate: rw [toFormal_call_witnesses] at a copy of the relevant hWGt chunk
     (destructure hWGt stage-relative like soundness peel — or write peelGatesW mirroring
     peelGates over RegionOperations.ExtendsWitnesses), then per-bundle
     simp only [<Bundle>.bundle, <Bundle>.gate?, circuit_norm, readCell] destructure →
     the witnessed-bit equations (b1/d0/g0/h1 = ↑bitrange reads) + copy witnesses.
   - Y (2-level): make YComposite's gateChild_call_witnesses + gateChild public (edit
     YComposite.lean), then Y-call projection = simp [YCanonicityCheck.synth?…]-analogue:
     EW ((YC.call c inp).ops i) i = the 5 sub-chunks; the gate sub-chunk via the published
     YComposite projection → the lsb equation (wlsb = brWit gdY 0 1 → lsb-read =
     ↑bitrange(gdY,0,1)).
2. Prover-side MessageCellFacts record (21 clauses from the witness equations + the
   witnessed-bit equations; IsLowBit via isLowBit_iff_mod_two + bitrange(_,0,1) = %2).
3. commit leaf: PA = ⟨PieceBounds (donor pieceBounds_of_cellFacts + a
   PieceBounds donor_iff bridge — same induction as pieceChunks_donor_iff),
   ∃B honest (donor honestChunks_eq_noteCommitChunks_of_cellFacts + honestChunks
   donor-iff bridge + top hB0), windows (top hWin — spelling via commit_extract_eq +
   fwExtract at i₀+25)⟩ via layouter_completeness_leaf.
4. Y leaves: PA = IsLowBit y-read lsb-read from the projected lsb equations.
5. Gate leaves: PAs per the composite completeness glue (Composites.lean/CommitIvk
   patterns) using the witness equations + the commit child's PS zs facts (obtain via
   layouter_completeness_derived_placed on the commit chunk — gives Spec∧PS after PA
   discharge, ZsHonest-style honest z-values for the z13/z1 clauses; mirror
   the YComposite guard/tail discharges with high_bit_canonical/base_val_lt_tP_val/
   shifted_high_zero at the honest values).
Then: def circuit compiles (already written), import MainBundle into Clean/Ironwood.lean,
full build, commit. Then VK fixture (orchard dump harness).

### Gate-leaf arc (the LAST 10 leaves; state at ee5d3b3c + MCF/PieceBounds/honest
in-context): the inline layouter_completeness_derived application for the commit Spec
hits a whnf wall (and `seal` breaks the soundness-side extract defeq — reverted).
ROUTE: standalone private lemma
  commit_derived_spec (G R windows Q hQ cfg i₀ place env)
    (hWcm : ExtendsWitnesses ... commit-call chunk) (hPB' hHon' hWin') :
    <the commit_spec_eq/commit_extract_eq-bridged Spec at the (i₀+25) call args>
proved by layouter_completeness_derived + the same PA discharge + bridge rws — kernel
and whnf checked alone (the peel-lemma pattern; the leaf discharge by-blocks compile in
goal position, so pass hPB/hHonest/hWin as HYPOTHESES of the lemma to avoid re-elaboration).
Same standalone treatment for the four rangeCheckAt derived Specs if they also wall
(they are smaller; try inline first). Then the six z-value facts replay EXACTLY the
soundness block (zsFacts_cell + zs_get_* + defeq transports, at env.toEnvironment), and
the ten gate leaves discharge with:
- decompose gates: A trivial×2; PA = ⟨IsBool wit (from hwb1/hwd0/hwg0/hwh1 + bitrange<2),
  IsBool b2/d1-eval (hwb2/hwd1 + %2), the decomposition equation (hMCF clauses 17-21
  modulo eval-spelling)⟩ via toFormal bridges + the leaf.
- canonicity gates: A = the soundness A-discharges verbatim (z-facts + telescopes +
  bounds); PA = ⟨DSpec (MCF slices + guard via honest zLast + high_bit_canonical/
  base_val_lt_tP_val + shifted_high_zero — the Composites.lean completeness guards),
  shift (hWaP/hWbP/hWeP/hWgP witness equations)⟩.
Then `def circuit` (already written) + import MainBundle in Clean/Ironwood.lean + full
build → NoteCommit bundle DONE. Then the VK fixture (orchard dump harness) remains.
