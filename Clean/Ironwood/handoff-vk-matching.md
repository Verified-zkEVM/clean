# Ironwood arc status (was: VK-matching handoff)

Live status log for the in-flight arcs, shared across machines. The original mul
VK-matching handoff is COMPLETE (mul is fully VK-matched, CS + layout — see
`Clean/Halo2/vk-matching-design.md`'s implementation-status banner for the machinery
summary); completed narrative sections were retired 2026-07-18.

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
