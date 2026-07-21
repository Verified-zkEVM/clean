# Framework-Leakage Audit — Clean/Ironwood

**Anchor commit:** `4d922b1a` (branch `halo2-clean-2`). All line numbers are from that
tree — re-grep the symbol name before trusting a line number.

This is a standalone handoff for a cleanup agent with **no other context**. Read the
"Design contract" and "Rules" sections first, then work the "Cleanup order".

**No builds while surveying** was the rule that produced this doc; the cleanup agent
*will* need to build. Every claimed generic lemma below has been read in the framework
sources and exists at the cited location unless flagged "NEW".

---

## Design contract (what "leakage" means here)

`Clean/Halo2/` is the **framework**: the circuit monad, the `FormalCircuit` /
`FormalRegionCircuit` bundles, the `circuit_norm` simp set, `subcircuit_rw`, and the
`circuit_proof_start` proof-prefix tactic. `Clean/Ironwood/` is **userland**: ported
gadgets and their proofs. **The ideal (maintainer ruling, 2026-07-20): a gadget file
reasons about the framework through `circuit_proof_start` and the `circuit_norm` simp set
— and nothing else.** One tactic pass should remove ALL framework material (eval
statements, chunk shapes, accessor spellings), leaving a pure domain-level goal. Even
hand-invoking a *named* framework lemma in a gadget proof is a smell: it marks a
tactic/simp-set gap to be fixed centrally, not a sanctioned usage tier. A fortiori, any
lemma in a gadget file whose *statement* is an instance of a generic framework fact about
`.call` / `.output` / `.operations` / `.regionCount` / `ExtendsWitnesses` / `Constraints`
of a bundle the gadget did not define is a **defect** — "framework-first, never userland
scaffolding". The named-lemma inventory below is therefore the *repair toolkit* for the
cleanup (rewriting workarounds into their honest form), not the end state; the end state
is those lemmas firing inside `circuit_norm`/`circuit_proof_start` where gadgets never
spell them.

The framework already ships the generic replacements for most of what follows
(`Clean/Halo2/Subcircuit.lean`):

- `FormalCircuit.call_regionCount` (L167) + `.call_regionCount'` (L176, concrete-α)
- `FormalCircuit.output_call` (L56) + `.output_call'` (L115, `@[circuit_norm]`)
- `FormalCircuit.nextRegionIndex_call` (L96) + `.nextRegionIndex_call'` (L143)
- `FormalRegionCircuit.toFormal_call_extendsWitnesses` (L127) — the witness-bridge precedent
- `FormalCircuit.foldOps_regionCount / foldOps_constraints / foldOps_extendsWitnesses /
  foldCall_output / foldCall_operations / foldCall_nextRegionIndex` (L219–303) — the
  serial-fold API
- `FormalCircuit.callOps_eq` (`Formal.lean` L318) / `call_operations` (L328)

and the **`derive_contract_bridges name (binders)* := <bundle>`** command
(`Clean/Halo2/Tactics/ContractBridges.lean`, namespace `Halo2.lns`) which auto-generates a
child's `_spec_eq` / `_extract_eq` / `_output` / `_regionCount` / `_nextRegionIndex`
rfl-bridges from the bundle term. `circuit_proof_start` runs this on-the-fly internally.
See `Clean/Halo2/Tests/TestContractBridges.lean` for the pinned output shape.

---

## Executive summary

    Clean/Ironwood carries ~900 framework-plumbing sites across ~25 gadget files,
    roughly 1500–2000 LOC that re-implement framework facts in userland. The three
    biggest families are: (1) ~120 per-child accessor/bridge lemmas — *_call_regionCount
    / *_spec_eq / *_extract_eq / *_output / *_call_output / *_call_witnesses — each
    re-proving a generic FormalCircuit.call_* fact or an rfl-projection that the
    `derive_contract_bridges` command already auto-generates; (2) 314 `with_unfolding_all`
    call sites (164 in Action/Bundle.lean alone) plus ~169 bare `… from rfl` /
    `:= by rfl` defeq bridges that cross the call-spelling↔metadata-spelling boundary the
    framework should reconcile via named lemmas; (3) hand-rolled bundle bookkeeping —
    ~40 `synth*_regionCount` / `_nextRegionIndex` / `_output` lemmas and their `rw`
    chains that manually crack open child chunks that `subcircuit_rw` / the fold API
    should consume. The epicenter is Action/Bundle.lean (28 bridge lemmas, 164 unfoldings,
    four `set_option maxRecDepth 8192` bumps); the Sinsemilla and NoteCommit/CommitIvk
    bundle files are the next tier. None of this is unsound — it is duplication and
    boundary-crossing that a handful of framework additions plus `derive_contract_bridges`
    adoption would delete wholesale.

---

## Category 1 — Per-child accessor / bridge lemmas (the largest family)

Each of these is a `private theorem <child>_call_<field>` (or `_spec_eq` / `_extract_eq` /
`_output`) whose body is a one-line `rw [FormalCircuit.call_regionCount]; rfl`, a
`FormalRegionCircuit.toFormal_call_extendsWitnesses _ …`, or a bare `:= rfl`. They bake a
concrete numeric region-count / output tuple / spec restatement into a named lemma so the
gadget's bundle-completeness proof can `rw` it. **This is exactly the output of
`derive_contract_bridges`.**

### 1a. `*_call_regionCount` spelling-wrappers (≈28 defs)

Body is uniformly `rw [FormalCircuit.call_regionCount]; rfl` (or `.foldOps_regionCount`).

| File | Line | Name | RC |
|---|---|---|---|
| Action/Bundle.lean | 27 | `toFormal_call_regionCount` (generic-over-bundle copy) | =1 |
| Action/Bundle.lean | 35 | `wpoint_call_regionCount` | =1 |
| Action/Bundle.lean | 42 | `wpointNonId_call_regionCount` | =1 |
| Action/Bundle.lean | 49 | `merkle_call_regionCount` | =128 |
| Action/Bundle.lean | 61 | `vc_call_regionCount` | =5 |
| Action/Bundle.lean | 70 | `dn_call_regionCount` | =9 |
| Action/Bundle.lean | 79 | `sa_call_regionCount` | =3 |
| Action/Bundle.lean | 87 | `civk_call_regionCount` | =14 |
| Action/Bundle.lean | 96 | `ai_call_regionCount` | =6 |
| Action/Bundle.lean | 104 | `nc_call_regionCount` | =43 |
| Action/Bundle.lean | 1954 | `base_call_regionCount` | (mainPost) |
| CommitIvk/Main.lean | 153 | `commit_call_regionCount` | |
| CommitIvk/Main.lean | 163 | `composite_call_regionCount` | |
| DeriveNullifier.lean | 107 | `hash_call_regionCount` | |
| DeriveNullifier.lean | 116 | `addChip_call_regionCount` | |
| DeriveNullifier.lean | 124 | `bfe_call_regionCount` | |
| ValueCommit.lean | 58 | `short_call_regionCount` | |
| NoteCommit/Main.lean | 337 | `toFormal_call_regionCount` | |
| NoteCommit/Main.lean | 346 | `yc_call_regionCount` | |
| NoteCommit/Main.lean | 355 | `commit_call_regionCount` | |
| NoteCommit/MainBundle.lean | 74 | `yc_call_regionCount` | |
| NoteCommit/MainBundle.lean | 82 | `commit_call_regionCount` | |
| NoteCommit/MainBundle.lean | 169 | `toFormal_call_regionCount` | |
| CommitDomain.lean | 151 | `blind_call_regionCount` | |
| Ecc/Mul.lean | 1834 | `mul_call_regionCount` | |
| Ecc/Add.lean | 414 | `toFormal_call_regionCount` | |
| Ecc/WitnessPoint.lean | 176 | `pointNonId_toFormal_call_regionCount` | |
| Ecc/MulFixed/FullWidth.lean | 1118 | `circuit_call_regionCount` | |

Note the **cross-file duplication**: `toFormal_call_regionCount` (the generic
`FormalRegionCircuit.toFormal … = 1` wrapper) is copy-pasted verbatim in Action/Bundle
(27), NoteCommit/Main (337), NoteCommit/MainBundle (169). Likewise
`yc_call_regionCount` / `commit_call_regionCount` are duplicated between NoteCommit/Main
and NoteCommit/MainBundle. (See Category 2.)

### 1b. `*_spec_eq` restatements (55 defs) and `*_extract_eq` (26 defs)

Uniformly `:= rfl` (or a 2-line simp). Representative: `Ecc/Mul.lean:1821
mul_spec_eq : mul.Spec = … := rfl`; `YComposite.lean:269 gateChild_extract_eq … := rfl`;
`Action/Bundle.lean:368–516` (a wall of `toFormal_spec_eq`, `wpoint_spec_eq`,
`merkle_spec_eq`, `vc_spec_eq`, `dn_spec_eq`, `sa_spec_eq`, `civk_spec_eq`, `ai_spec_eq`,
`nc_spec_eq`, plus the matching `*_extract_eq`). Full def-site list (grep
`theorem \w+_spec_eq` / `_extract_eq`): Poseidon/Permute (fullRound/partialRound),
Poseidon/Hash (initRegion/addInputRegion/permuteRegion), all five NoteCommit/Composites
`gateChild_spec_eq`, CommitIvk/{MainBundle,Composite}, Sinsemilla/{Chain,Merkle,CommitDomain,
HashToPoint}, MulOverflow, MulFixed/FullWidth. These are **precisely `derive_contract_bridges`
output** — every one should be deleted and replaced by a single
`derive_contract_bridges <child> := <bundle-term>` invocation per bundle.

### 1c. `*_call_output` / `*_output_eq` output-bridges (10 defs)

| File | Line | Name |
|---|---|---|
| Ecc/Mul.lean | 393 | `incomplete_call_output` |
| Ecc/Mul.lean | 404 | `complete_call_output_zs` |
| Ecc/Mul.lean | 411 | `add_call_output` |
| Ecc/Mul.lean | 473/491/504 | plain-`.output` restatements of the above |
| Sinsemilla/HashToPoint.lean | 461 | `hashCircuit_output_eq` |
| Poseidon/Permute.lean | 64/68 | `fullRound_output_eq` / `partialRound_output_eq` |

Mul.lean's `private *_call_output` family is the exemplar the task brief already flagged
as a defect pattern. These bridge the `call`-spelling of `.output` to the metadata
spelling; the generic `FormalCircuit.output_call'` (`@[circuit_norm]`) plus
`derive_contract_bridges`'s `_output` bridge subsumes them.

### 1d. `*_call_witnesses` (1 remaining)

| File | Line | Name |
|---|---|---|
| NoteCommit/YComposite.lean | 259 | `gateChild_call_witnesses` (**already** `:= FormalRegionCircuit.toFormal_call_extendsWitnesses _ …`) |

This one *already* delegates to the generic framework lemma — so it is a thin public
re-export, not a re-proof. Keep it only if a downstream file (MainBundle.lean:739 rewrites
`YCanonicityCheck.gateChild_call_witnesses`) genuinely needs the specialized statement;
otherwise inline the generic lemma at the two use sites. The three `toFormal_call_witnesses`
copies and the `wpoint_call_witnesses` / `wpointNonId_call_witnesses` family the brief
mentions have **already been deleted** in favor of the generic lemma — YComposite is the
last survivor.

**GENERIC FIX for all of Category 1:** adopt `derive_contract_bridges <child> := <bundle>`
(one command per child bundle) to auto-generate the `_spec_eq / _extract_eq / _output /
_regionCount / _nextRegionIndex` bridges; delete the hand-written ones. For the pure
`_call_regionCount` numeric wrappers, either use the generated `_regionCount` bridge or
inline `FormalCircuit.call_regionCount` (concrete-α: `.call_regionCount'`) + `rfl` at the
call site.

**Blocker to note (task #34):** `derive_contract_bridges` currently does NOT handle
**function-typed binders**, which is why the `chainC_*` / `hashC_*` / `shortC_*` bridge
stacks in HashToPoint / CommitDomain / Merkle are still hand-written (their bundle terms
take `ℕ → …` witness-generator arguments). Extending the command to function-typed binders
(task #34) collapses those stacks.

**Migration recipe:** for each `<child>` bundle in a file, (1) add
`derive_contract_bridges <child> := <bundle-term-with-binders>` near the bundle def;
(2) build; (3) `grep` the file for the old hand-written `<child>_spec_eq` etc., delete each
and let the generated name take over (names match by convention — verify against
TestContractBridges.lean); (4) rebuild. Do one child at a time to keep the diff bisectable.

---

## Category 2 — Cross-file duplicate lemmas (α-equivalent, different names)

Same statement proved in ≥2 files:

| Statement | Sites |
|---|---|
| generic `FormalRegionCircuit.toFormal … regionCount = 1` | Action/Bundle:27, NoteCommit/Main:337, NoteCommit/MainBundle:169, (and the true generic is already `FormalCircuit.call_regionCount`) |
| `yc_call_regionCount` | NoteCommit/Main:346, NoteCommit/MainBundle:74 |
| `commit_call_regionCount` | NoteCommit/Main:355, NoteCommit/MainBundle:82, CommitIvk/Main:153 |
| `short_spec_eq` / `short_output` | CommitIvk/MainBundle:26/40, NoteCommit/MainBundle:28, YComposite:104, ValueCommit:41 |
| `rangeCheckAt_spec_eq` | YComposite:34, NoteCommit/Composites:37, CommitIvk/Composite:33, NoteCommit/MainBundle:49 |
| `gateChild_spec_eq` | 4× in NoteCommit/Composites (107/282/439/597), YComposite:229, CommitIvk/Composite:141 |
| `short_extract_eq'` | NoteCommit/MainBundle:558, CommitIvk/MainBundle:466 |

**GENERIC FIX:** the `toFormal_*_regionCount` = 1 copies are all instances of
`FormalCircuit.call_regionCount` + `rfl`; delete and inline. The rest are
`derive_contract_bridges` output (Category 1b) that happens to be duplicated because each
bundle file re-derives its shared children — once the command is adopted, either the
generated bridges live once in the child's own file and are imported, or each file
generates its own (cheap, rfl) copy and the duplication is invisible boilerplate rather
than hand-maintained code. Prefer: generate the bridge **in the child's defining file**
and import.

---

## Category 3 — Defeq hacks crossing the framework boundary

Two shapes. Both mean "the tactic pipeline (`circuit_proof_start`/`circuit_norm`) did not
reconcile these two spellings for me, so I forced kernel defeq." The repair adds the
missing rewrite to the framework simp set / tactic pass — after which the gadget proof
should not need to spell anything at all — not a hand-cited lemma at each site.

### 3a. `with_unfolding_all` (314 sites)

| File | count | | File | count |
|---|---|---|---|---|
| Action/Bundle.lean | 164 | | Ecc/MulComplete.lean | 12 |
| NoteCommit/MainBundle.lean | 28 | | Action/AddressIntegrity.lean | 9 |
| Sinsemilla/Merkle.lean | 26 | | Ecc/Mul.lean | 8 |
| CommitIvk/MainBundle.lean | 17 | | Ecc/MulIncomplete.lean | 8 |
| Sinsemilla/Chain.lean | 12 | | NoteCommit/Main.lean | 7 |
| (others: CommitDomain 6, HashToPoint 3, Basic 3, HashPiece 2, Permute 2, Hash 2, CommitIvk/Main 2, WitnessPoint 1, CommitIvk/Bundle 1, DeriveNullifier 1) | | | | |

Most are `by with_unfolding_all rfl` (a spelling bridge) or
`by with_unfolding_all exact h<...>` (re-typing a hypothesis whose type differs only by an
unfolded `.output` / `eval` / `Point.x` spelling). Action/Bundle is the epicenter — the
`main` soundness/completeness proofs re-type dozens of child-output hypotheses this way.

### 3b. bare `… from rfl` / `:= by rfl` / `show … from rfl` (≈169 sites)

Representative: `Sinsemilla/Merkle.lean:1121 show cfg.1.sinsemilla.xA … from rfl`;
`HashToPoint.lean:191/207 show (… : Value (Output k) Fp) from by with_unfolding_all rfl`.
These assert a `call`-spelling term equals a metadata/`eval`-literal spelling by kernel
defeq inside a larger `rw`/`simp`.

**GENERIC FIX:** these are the symptom the concrete-α restatements
(`output_call'`, `call_regionCount'`, `nextRegionIndex_call'`) and `subcircuit_rw` exist to
kill — a proof that needs `with_unfolding_all rfl` to bridge `(child.call cfg inp).output i`
to the child's `extract` tuple is missing the `@[circuit_norm]` `output_call'` rewrite in
its `simp` set. **Recommended framework work:** audit which spellings still force
`with_unfolding_all` (start with Action/Bundle's `main` proof), and add the missing
concrete-α `@[circuit_norm]` restatement or a `subcircuit_rw` extension so the proof closes
with `simp only [circuit_norm]` / `subcircuit_rw` instead of raw defeq. Each such addition
deletes a cluster of `with_unfolding_all` sites. Treat a `with_unfolding_all` in a gadget
proof as a **framework bug report**, not an acceptable idiom.

**Migration recipe:** per file, for each `with_unfolding_all rfl` / `from rfl`, identify the
two spellings; find (or add) the framework lemma reconciling them; replace with a named
`rw`/`simp only`. Where the spelling is a bundle `.output`/`.extract`, the fix is almost
always the `derive_contract_bridges`-generated `_output`/`_extract_eq` bridge from
Category 1.

---

## Category 4 — Hand-rolled simp sets unfolding framework internals

Gadget proofs that manually `simp only [FormalCircuit.call, FormalCircuit.callOps_eq,
Circuit.operations, …]` to crack open a call chunk the engine should consume:

| File | Line | Args |
|---|---|---|
| NoteCommit/MainBundle.lean | 732 | `simp only [FormalCircuit.call, FormalCircuit.callOps_eq, Circuit.operations]` |
| CommitIvk/MainBundle.lean | 557 | `simp only [FormalCircuit.call, FormalCircuit.callOps_eq, Circuit.operations]` |

Plus ~85 sites across Ironwood where a `simp`/`rw` arg is one of `FormalCircuit.call`,
`callOps_eq`, `Circuit.operations`, `RegionCircuit.operations`, `ExtendsWitnesses`,
`Halo2.Constraints`, `assignRegion` (grep those tokens). The concentrated offenders are the
`*Bundle.lean` completeness proofs and Sinsemilla/{Chain,Merkle,HashToPoint} `.output`
extractions (`ElaboratedRegionCircuit.output_eq` + `RegionCircuit.output_bind/pure` +
`output_assignAdvice` chains, e.g. HashToPoint:287–294, Chain:1177–1184, Merkle:1121–1124).

**GENERIC FIX:** these manual chunk-cracks are what `subcircuit_rw` (soundness/completeness
chunk rewriter) and `FormalCircuit.foldOps_constraints/extendsWitnesses` (for loop bodies)
are for. Where a proof reaches for `callOps_eq` + `Circuit.operations` by hand, it should be
one `subcircuit_rw` call. The `ElaboratedRegionCircuit.output_eq` + `output_bind/pure`
extraction chains in Sinsemilla want a named framework lemma
"`<bundle>.output = <extract tuple>`" — again the `derive_contract_bridges` `_output`
bridge. **Recommended framework work:** confirm `subcircuit_rw` covers the two
`callOps_eq` sites (they may predate it), and add an `output`-extraction lemma/`circuit_norm`
entry for the RegionCircuit `.output` walk so Sinsemilla stops hand-unfolding.

---

## Category 5 — Bundle bookkeeping families (classify: keep vs delete)

Per-bundle `synth*_regionCount` / `_nextRegionIndex` / `_output` lemmas (~40 defs total,
grep `theorem \w+_regionCount` = 60 incl. Category 1a; `_nextRegionIndex` = 6;
`theorem \w+_output` = 41).

**KEEP (private metadata helpers — NOT exports):** the *composite* lemmas that define a
bundle's own `ElaboratedCircuit` metadata fields — consumed by
`regionCount_eq := fun input i => (synth_regionCount …).symm` etc. Maintainer ruling
(2026-07-20): these are tolerated only as `private` helpers with that single consumer;
anything a parent needs must flow through the framework's subcircuit composition, never
through a child-exported lemma. A reference to one of these outside its own `elaborated`
instance is a finding (metadata field bypassed). Examples: `synth_regionCount` in
NoteCommit/Composites (4×), CommitIvk/Composite:132, YComposite:287, Poseidon/Hash:143,
MulOverflow:277, all the `synthesize_regionCount` in MulFixed/{Short,BaseFieldElem,FullWidth};
`main_regionCount`/`mainPost_regionCount`/`synthesize_regionCount`/`synthWitness_regionCount`/
`synthChecks_regionCount`/`synthNotes_regionCount` in Action/Bundle; `synthPieces_*` /
`synthChecks_*` / `synthGates_*` in NoteCommit/Main + CommitIvk/Main. These are correct
altitude.

**DELETE (redundant re-derivations / spelling dups):** the per-*child* `*_call_regionCount`
wrappers folded into Category 1a, and the copy-paste of a composite lemma across bundle
files (Category 2). Also review `currentRegion_nextRegionIndex`
(NoteCommit/Main:198) — likely a generic `RegionIndex` identity that belongs in the
framework.

**GENERIC FIX:** none needed for the keepers. For the deletables, see Categories 1–2. The
composite `synth*_regionCount` proofs themselves contain long
`rw [<child>_call_regionCount, <child>_call_regionCount, …]` chains (e.g.
NoteCommit/Main:389–392 rewrites `toFormal_call_regionCount` nine times; Action/Bundle:119,
128, 138 chains) — once the child bridges are `derive_contract_bridges`-generated, these
chains stay but reference generated names; they cannot be auto-collapsed without a
`regionCount`-computing tactic (optional future work: a `bundle_regionCount` tactic that
sums child `.regionCount` via the fold API).

---

## Category 6 — Tactic-workaround scaffolding



`set_option maxRecDepth` bumps **in gadget proof files** (excluding data-heavy
Fixtures/*.lean and Ecc/MulFixed/Certs/*.lean, whose 100000 bumps are legitimate concrete
layout/cert evaluation):

| File | Lines | Value | Likely cause |
|---|---|---|---|
| Action/Bundle.lean | 749, 1215, 2028, 2102 | 8192 | `main` sound/complete over 15 children; deep call-chunk nesting |
| CommitIvk/MainBundle.lean | 222, 591 | 4096 | bundle completeness |
| CommitIvk/Composite.lean | 173 | 4096 | |
| NoteCommit/YComposite.lean | 297 | 4096 | `synth_regionCount` chunk unfold |

These bumps correlate 1:1 with the files that hand-unfold call chunks (Category 4) and
re-type via `with_unfolding_all` (Category 3): the recursion depth is spent in kernel defeq
that a named `simp only [circuit_norm]` / `subcircuit_rw` path would not incur. Expect the
bumps to become unnecessary (or droppable to the default) once Categories 3–4 are fixed in
that file. **Do not** add new `maxRecDepth` bumps to gadget files (per repo memory: "No
huge maxHeartbeats — prefer a framework fix").

Also in this category: the recorded **tactic gaps** in Sinsemilla/Chain.lean:1083–1093
(`circuit_proof_start`'s step-(b) peel times out at whnf on the slot bundle — the proof
falls back to manual `ElaboratedRegionCircuit.output_eq` unfolding). This is a
`circuit_proof_start` / `subcircuit_rw` capability gap on function-family-indexed bundles;
fixing it removes the manual fallback in Chain and likely the parallel ones in
Merkle/HashToPoint.

**Baseline for contrast:** 135 healthy `circuit_proof_start` invocations across Ironwood —
the tactic works for the vast majority of gadgets. The scaffolding above is concentrated in
the ~6 large *bundle-composition* files where the engine hits its current limits.

---

## Cleanup order (dependency-ordered — framework additions unlock deletions)

1. **Extend `derive_contract_bridges` to function-typed binders (task #34).** Unlocks
   deleting the `chainC_*` / `hashC_*` / `shortC_*` bridge stacks in HashToPoint /
   CommitDomain / Merkle (Category 1b, the function-family bundles). Framework-only change;
   pin new output in TestContractBridges.lean.

2. **Adopt `derive_contract_bridges` for all fixed-binder child bundles.** Delete the
   hand-written `_spec_eq` / `_extract_eq` / `_output` / numeric `_call_regionCount` bridges
   (Categories 1a/1b/1c, 2). Do it file-by-file, child-by-child; each is an independent,
   bisectable diff. Start with the leaf gadgets (Ecc/Add, WitnessPoint, MulFixed/FullWidth,
   DeriveNullifier children) before the composite bundles (Action/Bundle, NoteCommit,
   CommitIvk) so the composites' `rw [<child>_bridge]` chains flip to generated names last.

3. **Add the missing concrete-α `@[circuit_norm]` restatements / `subcircuit_rw` coverage**
   for the spellings currently bridged by `with_unfolding_all` and hand `callOps_eq`
   (Categories 3, 4). Prioritize by count: Action/Bundle (164) → NoteCommit/MainBundle (28)
   → Merkle (26) → CommitIvk/MainBundle (17) → Chain (12) / MulComplete (12). Each framework
   lemma added deletes a cluster; re-grep `with_unfolding_all` after each to measure.

4. **Fix the `circuit_proof_start` / `subcircuit_rw` whnf-timeout on function-family
   bundles** (Chain:1083 gap). Removes the manual `output_eq` fallbacks in Chain / Merkle /
   HashToPoint.

5. **Drop the now-unneeded `set_option maxRecDepth` bumps** in the four bundle files
   (Category 6) and confirm they build at default depth. This is the *verification* that
   steps 3–4 actually removed the kernel-defeq work — if a bump is still needed, a defeq
   bridge was missed.

6. **Sweep the keeper bookkeeping (Category 5)** only to relocate any composite lemma that
   is duplicated across files into its child's defining file + import (Category 2). Do not
   touch the legitimate `regionCount_eq`/`output_eq`/`nextRegionIndex_eq`-feeding lemmas.

---

## Rules for gadget files (give these to every sprint agent)

1. **If your lemma's statement mentions `.call`, `.operations`, `.output`,
   `.nextRegionIndex`, or `.regionCount` of a bundle you did not define in this file, it
   belongs in the framework — not here.** Use the generic `FormalCircuit.call_regionCount` /
   `output_call'` / `nextRegionIndex_call'` / `toFormal_call_extendsWitnesses`, or generate
   the bridge with `derive_contract_bridges`.

2. **Never hand-write a `_spec_eq` / `_extract_eq` / `_output` / `_regionCount` /
   `_nextRegionIndex` bridge for a child bundle.** Write
   `derive_contract_bridges <child> := <bundle-term>` once and use the generated names.

3. **`with_unfolding_all` is a framework bug report, not a tactic.** If you need it to make
   two terms defeq, the framework is missing a named rewrite. File it / add the
   `@[circuit_norm]` lemma; do not commit the `with_unfolding_all`.

4. **Never put `FormalCircuit.call`, `callOps_eq`, `Circuit.operations`,
   `RegionCircuit.operations`, `ExtendsWitnesses`, `Halo2.Constraints`, or `assignRegion` in
   a gadget-proof `simp`/`rw` arg list.** Cracking those open is `subcircuit_rw`'s job (for
   chunks) or the fold API's job (`foldOps_constraints` / `foldOps_extendsWitnesses` for
   loop bodies).

5. **Do not add `set_option maxRecDepth`/`maxHeartbeats` bumps to a gadget proof.** A deep
   recursion means kernel defeq is doing work a named lemma should do. Fix the lemma or
   report the tactic gap.

6. **The ideal gadget proof reasons about the framework through `circuit_proof_start` and
   the `circuit_norm` simp set — and nothing else.** (Maintainer ruling, 2026-07-20: this
   is stricter than "use the named lemma API".) `circuit_proof_start` should eliminate ALL
   framework material — eval statements, chunk shapes, accessor spellings — in a single
   pass, leaving a pure domain-level goal. Every hand-invoked framework lemma, every manual
   peel (`ElaboratedRegionCircuit.output_eq` + `output_bind`/`output_pure`), every
   `subcircuit_rw`-should-have-done-this step in a gadget proof is a pipeline gap: record
   it and fix the tactic/simp set, do not normalize the workaround. If the tactic times out
   (see Chain:1083), that too is a tactic gap to report.

7. **A composite bundle's own metadata lemmas are tolerated ONLY as private helpers with
   exactly one consumer: the `ElaboratedCircuit` instance's `*_eq` fields.** (Maintainer
   ruling, 2026-07-20.) They are NOT an export: parents must learn region counts / outputs
   through the composition machinery (metadata fields consumed by `circuit_norm` /
   `subcircuit_rw`), never by citing a child's `synth*_regionCount`-style lemma. Mark them
   `private`; any reference to one outside its own bundle's `elaborated` instance is itself
   a finding — it means the metadata field was not used where it should have been. (The
   cleanup agent should grep each keeper's name for out-of-instance references and treat
   hits as Category-1 items.)

8. **Before duplicating a child bridge that another bundle file already has, import it.**
   Grep for the child name across `Clean/Ironwood` first (Category 2 exists because nobody
   did).

---

## Reference / related work

- **Task #34** — auto-derive `output_eq` bridges via `derive_contract_bridges`, extended to
  function-typed binders; collapses the `chainC_*` / `hashC_*` / `shortC_*` bridge stacks in
  HashToPoint / CommitDomain / Merkle. Prerequisite for Cleanup step 1.
- **`FormalRegionCircuit.toFormal_call_extendsWitnesses`** (`Clean/Halo2/Subcircuit.lean:127`)
  — the precedent: a per-gadget `toFormal_call_witnesses` copy family was deleted in favor of
  this single generic lemma. YComposite:259 `gateChild_call_witnesses` already delegates to
  it; make every future witness-bridge do the same.
- **`derive_contract_bridges`** command — `Clean/Halo2/Tactics/ContractBridges.lean`
  (namespace `Halo2.lns`); pinned output in `Clean/Halo2/Tests/TestContractBridges.lean`.
- **`circuit_proof_start`** — `Clean/Halo2/Tactics/CircuitProofStart.lean` (runs
  `derive_contract_bridges` on-the-fly + the step-(b) peel).
- **`subcircuit_rw`** — `Clean/Halo2/Tactics/SubcircuitRw.lean` (polarity-aware chunk
  rewriter; the sole mechanism for opening call chunks in sound/complete proofs).
- **Serial-fold API** — `Clean/Halo2/Subcircuit.lean:184–303`
  (`foldState`/`foldCall`/`foldOps` + `_regionCount`/`_constraints`/`_extendsWitnesses`/
  `_output`); the correct tool for loop-body gadgets (Merkle `fold_regionCount:1986` already
  uses `foldOps_regionCount`).

---

## Work reservation (July 21, 2026)

The cleanup is being parallelized. **Reserved by the fixtures/ironwood-move agent
(Claude session c5344d2b, "agent F")** — the userland Category 1/2 sweep, i.e.
`derive_contract_bridges` adoption and deletion of the hand-written
`*_spec_eq` / `*_extract_eq` / `*_output` / `*_call_regionCount` bridges (+ the
Category 2 cross-file dedup and the step-6 relocations), over:

- `Ecc/Add.lean`, `Ecc/WitnessPoint.lean`, `Ecc/MulFixed/FullWidth.lean`, `Ecc/Mul.lean`
- `Action/{DeriveNullifier,ValueCommit,SpendAuthority,AddressIntegrity}.lean`
- `NoteCommit/{Main,MainBundle,Composites,YComposite}.lean`,
  `CommitIvk/{Main,MainBundle,Composite}.lean`
- `Sinsemilla/{Chain,Merkle,CommitDomain,HashToPoint}.lean`, `Poseidon/{Permute,Hash}.lean`,
  `Action/Bundle.lean` (its 28 Category-1 bridges ONLY — the `with_unfolding_all`
  epicenter/Category 3 in that file is NOT claimed)

NOT claimed (free for the other stream): the framework-side steps — #34
(function-typed binders in `derive_contract_bridges`), the Category 3/4 `circuit_norm` /
`subcircuit_rw` gap-filling, the function-family whnf fix (cleanup steps 1, 3, 4), and
all `Clean/Halo2/` files. Function-binder bridge stacks (`chainC_*`/`hashC_*`/`shortC_*`)
stay untouched until #34 lands.

Mark progress here per file as it lands; remove this section when the sweep is done.

**Agent F progress (July 21):**
- **The Category 1/2 sweep is COMPLETE** (commits 6498ca16, ed692bda, 17a73285,
  f9fd0972): every hand-written contract-projection bridge stack in the reserved file
  list is deleted in favor of `derive_contract_bridges` home stacks; the Category-2
  five-site duplicates (short/rangeCheckAt/commit/yc/toFormal-generic) have single
  homes; Action/Bundle's 43 Category-1 bridges are gone (its `with_unfolding_all`
  epicenter and eval/output bridges remain — that is the Category-3 port).
- **NOTE for agent H — #34 may be MOOT**: after the mvar-instantiation fix in
  `buildBridges` (instantiate after the defeq check; commit ed692bda), proof-typed
  binders (`hQ : Q.OnCurve`, `hns : ns ≠ []`, `h13 : 13 ≤ n`) AND function-typed
  binders (`yaIn : Placed Environment Fp → Fp`, `wsib : ℕ → WitgenIR Fp 1`,
  `wswap : ℕ → Placed ProverEnvironment Fp → Bool`) all derive cleanly — the
  slotC/chainC/hashC/hashLayerC/CalculateRoot stacks are all generated now. The
  "chokes on function-typed binders" comments were stale.
- Still hand-written (needs a framework-stream reduction strategy, audit 1c): the
  region-level `*_output` cell-record bridges and applied deep-extract
  `*_extract_cells` — a whnf field projection cannot produce their reduced RHS.
- DONE (commit 6498ca16): leaf gadgets + Action composites. Home derives at
  `Ecc/Add` (toFormal), `Ecc/WitnessPoint` (pointNonId.toFormal, `_output` bridge kept —
  no command support), `Ecc/MulFixed/{FullWidth,Short,BaseFieldElem}`, `Ecc/Mul`,
  `Poseidon/Hash`, `Utilities/AddChip`; hand stacks + the per-consumer private copies in
  `ValueCommit`/`DeriveNullifier` deleted; goal-side regionCount simp lists now use the
  generic `FormalCircuit.call_regionCount` + `rfl`.
- NOTE for agent H (pushed 6498ca16, BEFORE H's Clean/Halo2 reservation was visible):
  `Tactics/ContractBridges.lean` grew `buildRegionCountBridge` — the command now also
  emits `<base>_call_regionCount` for `FormalCircuit`-typed bundles (audit 1a's
  preferred generic fix). Additive, green, no signature changes; fold into #34 work.
- Mul's private `*_call_output`/`*_output_eq` cell-layout family stays for now: a whnf
  projection would leave the field bodies unreduced (the hand RHS is deeper than whnf),
  so a generated `_output` bridge needs a smarter reduction strategy — leaving 1c to the
  framework stream.
- **Action/Bundle full port reassigned to agent F** (user directive, July 21, after H's
  reservation below): F takes the FULL `Action/Bundle.lean` port to the no-leakage
  vision — all framework plumbing via `circuit_proof_start`, superseding the "28
  Category-1 bridges ONLY" limit and H's capstone claim on that file. H: please treat
  Bundle.lean as F-held; everything else in H's reservation stands.
- **Bundle port, slice 1 DONE (commits c38dc0a1, f5ca1566)**: region-count/offset
  plumbing is now fully absorbed by `circuit_proof_start` — the command emits
  `_call_regionCount` in both spellings (abstract + primed concrete-α) and tags them
  `@[circuit_norm]`, so every `circuit_norm` pass folds chunk region counts; Bundle's
  ~90-line try-rw ladders, all stage offset rw blocks, and every other file's
  pre-folded rw's are deleted. All SEVEN gadget-file `maxRecDepth` bumps (Bundle ×4,
  CommitIvk/Composite, CommitIvk/MainBundle ×2→0, YComposite) are GONE — the folded
  towers fit the default depth (Category 6 for gadget files: done).
- **H → F (2026-07-21)**: the generic witness lemma LANDED — `Witgen.MOver.eval_toIRScalar`
  (`@[circuit_norm]`, Clean/Circuit/WitnessIRSugar.lean): `((toIRScalar p).eval env)[0]
  = MOver.eval env p`. Witness facts for `toIRScalar`-assigned cells now land on the
  high-level `MOver.eval` atom in every `circuit_norm` pass — the 155
  `with_unfolding_all` eval-cell bridges in Bundle (and FullWidth's `hWwslM`,
  Bundle's `wpoint_eval_eq_cells` pair) are deletable. The cps auto-unfold/step-(d)/(f)
  work also landed (commit 68c6a6e1). Resume when ready.
- **Bundle port, remaining (blocked on H's framework stream)**: the 155
  `with_unfolding_all` eval-cell defeq bridges (needs the generic "toIRScalar-assigned
  ⇒ eval = cell" `circuit_norm` witness lemma), the ~15 manual
  `SubcircuitRw.layouter_completeness_{leaf,derived}` applications (needs the cps
  auto-unfold / step-(d)/(f) work), the `*Inputs_eval_eq*` and `*_output` record
  bridges (needs the 1c reduction strategy), and the per-call `*_call_nextRegionIndex`
  helpers. F will resume when that machinery lands, or hand the residue to H with this
  note.

**Reserved by the hint-arc agent (Claude session 07d7db7f, "agent H")** — the framework
stream + exemplar ports to the no-leakage ideal (maintainer ruling 2026-07-21: sound/
completeness proofs need ONLY `circuit_proof_start` — no extra `circuit_norm` simp):

- All `Clean/Halo2/` framework work: cps auto-unfold of the bundle's `synthesize` body
  (main-Clean parity) + step-(d)/(f) cooperation on prefix-surfaced children; the
  Category 3/4 concrete-α `@[circuit_norm]` restatements (incl. a generic
  "toIRScalar-assigned ⇒ eval = cell" witness lemma); #34 function-typed binders in
  `derive_contract_bridges`; the Chain:1083 peel-timeout fix.
- Exemplar proof ports (in order): `CommitIvk/Composite.lean` + the four
  `NoteCommit/Composites.lean` canonicity proofs; `Ecc/MulComplete.lean`; then replays
  in `Ecc/MulIncomplete.lean`, `Ecc/Mul.lean`, `Action/AddressIntegrity.lean`;
  `Sinsemilla/Chain.lean` + replays in `Merkle`/`HashToPoint`/`CommitDomain`;
  capstone `Action/Bundle.lean` `main` proofs + dropping its `maxRecDepth` bumps.
- In files agent F also holds: H's proof-rewrites land AFTER F's bridge sweep in that
  file (generated bridges are inputs to the ports, though ported proofs should not
  need to cite them).
