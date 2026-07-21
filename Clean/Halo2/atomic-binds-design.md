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
