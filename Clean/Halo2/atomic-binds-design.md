# Atomic binds: the proof state mirrors the do-block

**Status:** agreed design (maintainer + agents F/H, July 21, 2026). Not yet implemented.
**Companion work:** H's concrete output reduction in `ElaboratedCircuit` instances (the
canonical reduced-cell spelling per bundle) is the *concrete* half of this design.

## The problem

`circuit_proof_start`'s peel instantiates every bind continuation at the step's output
**term**. The term is textually duplicated into every downstream use, and the pipeline
then spends three separate mechanisms undoing the duplication after the fact:

- `abstract_outputs` — a post-hoc term scavenger for *call* outputs (eight documented
  "guises", a canonicalization fixpoint, traversal-order `x_gen_out_i` naming that is
  unstable under normalization changes);
- row-fact chaining (step f) — post-hoc value replacement for *primitive* cell reads;
- the engine's (retired) deep-input machinery — post-hoc abstraction of inputs that
  embedded composed outputs.

Downstream symptoms: hand-written `*_output` / `*_extract_cells` bridge lemmas, the
`with_unfolding_all` boundary crossings (79 remaining in Action/Bundle.lean), backwards
`h_gen_out : term = x` equations, and proof states nobody can read.

## The idea

**Every `operations_bind` peel of a bind whose value is used mints an opaque atom,
named from the do-binder, and instantiates the continuation at the atom.**

For `let rk ← step` in the synthesize body:

- introduce `rk : <output type>` (the do-binder's name; `x_<k>` fallback for anonymous
  but used binds) and the defining equation **in the useful direction**
  `h_rk : rk = <step's output term>`;
- instantiate the continuation at `rk`, so all downstream occurrences are *born* as the
  atom — no kabstract, no guises, no canonicalization pass, no ordering window;
- attach the step-kind facts alongside:
  - **primitive** (`assignAdvice`, `copyAdvice`, `cellAt`, …): the cell equation
    (what row-fact chaining reconstructs today);
  - **child call**: the child's contract (from `subcircuit_rw`, stated over `rk`) plus
    the concrete-cell boundary fact `eval env rk = ⟨cells…⟩`, instantiated from the
    bundle's `ElaboratedCircuit` canonical output spelling (H's reduction work) via the
    per-bundle registry (`Clean/Halo2/Subcircuit.lean`, `regionCountBridges` pattern);
    the extract value gets the same treatment (`wit_rk` atom + boundary fact).
- **unit-valued or discarded binders** (`gate.enable`, constraints, `let _ ← …` whose
  bvar does not occur) mint nothing — the context stays exactly as large as the
  circuit's dataflow.

Atoms are whole-value (consumers project `rk.x` off the atom; the AbstractOutputs
granularity finding stands). Region counts are NOT atomized — eager literal folding via
the `foldCallRegionCount` simproc stays (the literal is already the minimal term).

Net effect: the proof state is isomorphic to the do-block. Hypotheses read `out_rk`,
`psiOld`, `pair` — the circuit's own names in the circuit's own order. Term growth
during peeling becomes linear. Concrete cell spellings appear exactly once each, on the
supplied-equation side, and `with_unfolding_all`/hand bridges have nothing left to do.

## Raw binds, loops, and the mint gate (H, agreed with maintainer, July 21)

**Detection invariant:** the peel classifies and splits ONLY the top-level `Bind.bind`
spine that do-elaboration produced. It never whnf/unfolds a step term to find binds —
so loop safety is a property of the UNFOLD PIPELINE, not the matcher: nothing may open
a loop combinator before the peel sees it.

**Three-way step classification, by head:**
- **call** — `FormalCircuit.call` (later the region-level call): chunk `h_call_<binder>`,
  contract via the engine, canonical output minted (as shipped).
- **loop** — head carries the `circuit_loop` attribute, an explicit registry on the
  combinator defs (`forRange`/`forRange'`/`forRangeVar'`, the `foldOps`/`foldCall`
  serial-fold API). The attribute does double duty: `autoUnfoldsOfMain` EXCLUDES
  attributed combinators (closing the real hole — the self-recursion detector already
  keeps `loopAux`-style cores folded, but the non-recursive WRAPPERS passed the filter,
  and unfolding one would let the peel eat loop iterations as top-level steps,
  destroying the folded induction interface); `peelOneBind` treats an attributed head
  as an ATOMIC step whose chunk gets the canonical ∀-round split (the tagged
  `forRange*_constraints` lemmas, from `circuit_norm`), never a spine decomposition.
- **primitive** — everything else (`assignRegion`, `currentRegion`, table ops): chunk
  `h_region_<k>`, opened with `circuit_norm`.

**The mint gate: mint iff no consumer rebinds the output by concrete address**
(agreed with maintainer, July 22, replacing the short-lived universal gate). The test:
does any consumer independently re-derive the concrete spelling and match against it,
or does every consumer treat the value opaquely through an interface? Minting where a
re-deriver exists splits one thing into two spellings that no longer meet
syntactically — the exact disease atomization exists to cure.

- **Layouter level: every used cell-valued binder mints.** There are no gates at this
  level; a raw-produced cell is only ever *passed* — into child calls that
  copy-constrain it internally, into contracts stated over its eval. Every consumer is
  opacity-respecting by construction, while the concrete spelling
  (`AssignedCell.of <nextRegionIndex tower> …`) is exactly the offset-arithmetic term
  that metastasizes through every later call's input. Same reason call outputs mint.
- **Region level: raw binds do NOT mint.** Gates address cells by (column, rotation),
  bypassing the binder entirely — the concrete address is *content*, the connection
  medium between gate polys, witness equations, and the cell-spelled extract/Spec
  contract. Cell atoms here forced five of seven region proofs to open with an
  orientation idiom (`simp only [← <atom>_eq, circuit_norm]`) whose only job was to
  reverse the mint — the empirical verdict on the universal gate. Raw region facts
  stay as concrete-spelled `region_<k>` equations; the future for named region reads
  is VALUE-level atoms (CPS3, issue #428), not address-level ones.
- Index-valued binders (`currentRegion`'s `RegionIndex`, ℕ) never mint: they feed
  offset arithmetic that must stay literal for the region-count folding. Unit/discarded
  binders mint nothing.

The layouter/region split is not a carve-out: it is the consumer-rebinding principle
evaluated against a structural fact (where gates live). Loop chunks share the raw
`region_<k>` naming; the registry's spine-atomicity and auto-unfold exclusion are the
substantive loop protections, not the name.

**Loop outputs mint as ONE atom**: a used map-style loop generalizes its whole
`(loop …).output i` to a single binder-named atom; the defining equation is reduced
separately to the closed-form boundary fact (`Vector.ofFn …`, via the loop's tagged
output lemma), and consumers project the atom pointwise through the lazy
`getElem_eval_fields_cells` bridges — atomic binds, loop closed-forms, and the lazy
vector normal form composing instead of fighting.

**Raw-mint mechanics (validated in `Clean/Halo2/Tests/TestRawBind.lean`):** mint from
the still-shared `(x).output i` spelling BEFORE any reduction (all occurrences
converge); reduce ONLY the defining equation to the concrete boundary fact; region
counts of raw steps fold in the LANDING fixpoint (they only materialize there —
`circuit_norm` unfolds the folded `nextRegionIndex` during pass 2, so peel-time folds
find nothing); minted defining equations join the pass-2 rules so contracts land
atom-spelled end-to-end. Known cleanup: a fully-consumed defining equation degrades to
`h_<x> : True` and should be cleared.

**Extract (implemented):** treated identically to output at every call bind — after
the engine opens a contract (`subcircuit_rw`), the child's `extract` spelling is
collected from the contract hypothesis and minted to a `wit_<binder>` atom
(`wit_out` for a call embedded in a terminal raw step, which has no do-binder);
the defining equation stays in context and a goal-only pass at the end of landing
rewrites the goal into the contracts' witness language (validated: SpendAuthority's
goal reads `{output_x, output_y} = wit_alphaCommitment.2 • G + akP` — pure witness
terms). Unit-typed witnesses skip minting. Still open: for the few bundles with
expensive extracts (FullWidth's `fwExtract` 85-vector, Chain's HVec), a reduced-form
`extract` slot + `extract_eq` in `ElaboratedCircuit` (defaulted, like `output`)
would pay the reduction once at the instance instead of per consumer — the same
reduce-once argument as the output field. Would make the hand
`*_extract_eq`/`*_extract_cells` bridge family deletable.

**Engine-time goal normalization (completeness):** the goal is simped ONCE
(`circuit_norm` + count folds + the caller's unfolds) after all peels and before the
goal-mode engine. Every peel is done, so nothing remains for the peel `rw`s to match
and the full pass is safe; it surfaces every call chunk in the canonical spelling the
walker matches — calls embedded in mid-chain or terminal raw regions
(`assignRegion "…" (X.call …)`), and calls under region-level bind spines (BFE's
`witnessCheck13`). This replaced three earlier per-site goal-opens (terminal,
mid-chain, spine) that each fixed one spelling gap.

**Two-pass witness/output matching (`subcircuit_rw !`, cps2 only):** with the bang
flag — which cps2 always passes — the engine's witness locator and the
output-abstraction lookup run a full `.reducible` pass first (identical spellings —
the common case, including 85-round loop families), and a relaxed
default-transparency pass only when nothing matched reducibly. Child/config compares
stay fail-fast at `.reducible` in both passes (a mismatched candidate must not
δ-unfold bundle literals), and the relaxed output pass only compares equations for
the same child bundle (syntactic prefilter). Rationale: the pre-engine goal simp
respels call inputs/indexes on the goal side only, so genuine matches can diverge by
normalization — but an unconditional default-transparency compare storms on loop
families (85 same-child candidates × deep failing defeq — rediscovered the hard way
on Short's inner soundness). Plain `subcircuit_rw` (v1 callers) keeps the strict
single-pass semantics: v1 proofs rely on previously-unmatched chunks staying raw,
and v1 is being retired rather than re-stabilized (the same scoping applies to the
`_proof_N` exemption in the v2 auto-unfold gate).

**Terminal real steps:** a do-chain may end in a real step instead of `pure`
(`do let inn ← …; assignRegion "…" (X.call …)` — FullWidth's shape). The terminal
chunk is that step's chunk and must be kept and registered (`out_spec` for a bare
call, `region_<k>` for a raw step), not cleared — clearing silently dropped the
final step's constraints. The terminal step's output is the bundle output, so its
output spelling is canonicalized in `output_eq` like every peeled bind. In
completeness, the GOAL's terminal raw conjunct is opened (with region counts
folded) before the engine runs: a region-level call embedded in the terminal raw
step (`assignRegion "…" (X.call …)`) is only visible to the goal-mode engine as a
strengthenable chunk once `RegionOperations.Constraints` of the call is exposed and
its region index spells `i₀ + k` literally (the witness locator compares indexes at
reducible transparency). The same embedded-call gap exists for mid-chain raw
regions — unfixed until a circuit needs it.

## The in-peel engine (subcircuit rewriting v2) — agreed with maintainer, July 22

**Principle: contract conversion happens inside `peelOneBind`, not in a post-pass.**
The peel visits every call bind and every loop bind explicitly, in both directions,
holding the ground truth as Exprs: the bundle term, config, offset, input, the
just-split chunk hypothesis, the witness-side chunk (completeness), and — a moment
later — the minted atom with its defining equation. The post-pass engine re-discovers
all of this by syntactic matching, and every engine fragility to date lives in that
re-matching layer: the MulOverflow minted-atom miss, the relaxed transparency pass and
its bundle-compare fail-fast, the `h_spec_k` emission-order names, the missing ∀-bound
goal conversion for loops, the CPS2 witness clear-guard. In-peel, the conversion is
direct term application of the existing leaf lemmas
(`layouter_/region_completeness_leaf/derived[_placed]`,
`Clean/Halo2/Tactics/SubcircuitRw.lean`) at arguments already in hand — no search, no
transparency tiers, no miss modes.

**Per-bind artifact set.** A call bind produces, in one block: its chunk, its atom +
defining equation, its boundary fact, and its contract. Soundness weakens the chunk
hypothesis to the contract in place; completeness strengthens the goal's head conjunct
to the `EnvA ∧ A ∧ PA` premise bundle and introduces the derived
`EnvA → A → PA → Spec ∧ ProverSpec` statement — named `<binder>_spec` in BOTH
directions (retiring `h_spec_k`).

**Loops become symmetric by construction.** At a registry-head bind the peel applies
the canonical ∀-split and converts under the binder in the same step. The completeness
asymmetry — soundness consumes ∀-bound call chunks while fold parents hand-apply
`region_completeness_leaf_placed` per round — disappears; `fold_complete`-style
helpers produce the premise family directly and the per-round leaf boilerplate in
MulComplete's parent and MulIncomplete's loop dies.

**What dies with it** (for CPS2 paths): the engine's matching layer
(canonical-output discovery, the relaxed transparency pass of a5fd815e, the
bundle-compare fail-fast), the CPS2 witness clear-guard (an engine miss becomes
impossible for peeled binds), and the "engine should replace, not leave, consumed
witness chunks" known-gap.

**What stays:** the leaf lemmas as the shared logical core — the in-peel driver is a
new caller over the same semantics, not a fork — and the standalone `subcircuit_rw`
driver for manual and v1-era proofs until that corpus empties (the CPS1/CPS2
coexistence pattern).

**Build assignment:** F (author of the minting loop). The standalone engine's design
doc (`subcircuit-engine-design.md`) carries a superseded-for-CPS2 status note.

## Rollout

1. **CPS v2, wholesale.** A new version of the `circuit_proof_start` pipeline adopting
   this vision end-to-end (peel-with-minting + engine cooperation over atoms), selected
   explicitly per proof (flag or new entry point) — NOT an in-place mutation of the
   current pipeline. Old and new coexist.
2. **Incremental adoption**, exemplar-port style: leaf gadgets first (should be no-ops
   — leaves have no used child binds), then one mid composite (MulComplete or
   YComposite) to shake out the engine cooperation, then the assembly files
   (MainBundles, Action/Bundle) where the payoff is largest.
3. **Retire on empty corpus:** once no proof uses the v1 pipeline, delete
   `abstract_outputs`, row-fact chaining, the `*_output`/`*_extract_cells` hand
   bridges, and the v1 pipeline itself.

Both agents work in the same files where needed; git merges are fine. Coordination
happens through this doc and the audit doc's reservation ledger, not file ownership.
