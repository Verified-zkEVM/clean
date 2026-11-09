# Subcircuit rewrite engine (`subcircuit_rw`) — Design

Replaces the absorption-iff mechanism (`Clean/Halo2/Subcircuit.lean`) as the way parent
proofs consume child contracts. The iffs were the deliberate fast unblock; this is the
"proper engine that doesn't leave obligations/premises in place" (maintainer, 2026-07-10).

> **STATUS (superseding the future-tense framing below): migration is complete.** The
> absorption iffs, their concrete-α/`_bare` restatement families, the markers, and the
> `call_constraints_and_specs` copies have all been retired from `Subcircuit.lean` (only a
> historical docstring there records them); `subcircuit_rw` is the sole consumption mechanism.
> Read the "Migration and retirement" and D1 sections below as done, not planned.
>
> **STATUS 2 (July 22): superseded for CPS2 proofs by the in-peel engine — now BUILT.**
> This doc describes the STANDALONE post-pass driver: it scans a finished proof state and
> re-discovers each call's bundle/config/input by syntactic matching — the layer where
> the known fragilities lived (minted-atom spelling misses, the relaxed transparency
> pass, `h_spec_k` naming, no ∀-bound goal conversion). For `circuit_proof_start2`
> proofs contract conversion now happens inside the minting loop itself, where those
> arguments are in hand as Exprs, and raw steps decompose through the `chunk_split`
> constructor set rather than a `circuit_norm`-then-match pass — see
> `atomic-binds-design.md`, "The in-peel engine (subcircuit rewriting v2)". The leaf
> lemmas defined here remain the shared logical core (the in-peel driver is a new caller
> over them, not a fork); the polarity-rewriter driver below remains the mechanism for
> manual and v1-era proofs (Merkle's top bundles, HashLayer) until that corpus empties.

## Why the iffs are not the endgame

Four consumers' worth of evidence (MulComplete, Chain, MulOverflow, Mul):

1. **Residue.** The soundness iff leaves `SubcircuitConstraints … ∧ (…→ Spec)` — the
   marker-wrapped raw chunk survives in every hypothesis forever. The completeness iff
   leaves an `∨` in the goal until the proof picks a side. Both are noise the user must
   read around.
2. **Verbose instantiation.** The simp-firing variants key on `Placed` projections and
   concrete-α spellings; in loop lemmas (bare `place`/`env`) they never fire, so every
   consumer `rw`s the *generic* iff with all five arguments spelled per call — twice per
   round in MulComplete. The `_bare`/primed variant families exist only to fight simp's
   discrimination tree.
3. **Depth fragility.** On four-deep nested chunk inputs (Mul's overflow chunk),
   `call_constraints_and_specs`' metavariable unification exceeds heartbeats while the
   keyed iff `rw` doesn't — robustness currently depends on picking the right one of two
   mechanisms by hand.

## The design: a polarity-aware monotone rewriter

The reason simp can't consume a chunk is that `chunk → X` is not an iff. But proof
states don't need iffs: **hypotheses may be weakened and goals strengthened.** That is
one-directional rewriting under polarity, and it is a small, well-understood engine:

- `subcircuit_rw at h` (soundness side): walk `h`'s proposition structure (`∧ ∨ → ∀ ∃`)
  tracking polarity. Every call-boundary chunk
  `RegionOperations.Constraints place self env ((child.call cfg off inp).operations self)`
  (or the layouter analogue) found in **positive** position is replaced by the child's
  instantiated consequence
  `child.EnvAssumptions cfg ⟨place,env⟩ → child.Assumptions (eval …) → child.Spec … (…output…) (…extract…)`.
  The engine emits a proof of `h_old → h_new` built from a fixed congruence-lemma set
  (`and_mono`, `or_mono`, `imp_mono` with contravariant left, `forall_mono`,
  `exists_mono`) with `child.soundness … : chunk → consequence` at the leaves, then
  `replace h`.
- `subcircuit_rw` (completeness side): processes the **goal and the ExtendsWitnesses
  context simultaneously** (maintainer decision, 2026-07-11 — mirroring main Clean,
  where ExtendsWitnesses is part of each subcircuit's premises and discharged
  generically, never surfacing to the user). For each chunk in the goal's positive
  positions:
  1. locate the matching call-keyed `ExtendsWitnesses` fact in the context (in `hwit`
     or its already-destructured components);
  2. replace the goal chunk by the *parent-facing* preconditions only —
     `EnvAssumptions … ∧ Assumptions … ∧ ProverAssumptions …` — with ExtendsWitnesses
     discharged from the located fact via `child.completeness`. Subcircuit internals
     never appear in the goal.
  3. simultaneously introduce, per chunk, the derived contract statement
     `EnvAssumptions → Assumptions → ProverAssumptions → Spec ∧ ProverSpec`
     (from the located ExtendsWitnesses via `child.completeness` then
     `child.soundness` at the prover env's verifier view) — the main-Clean-style
     "subcircuit statement available from hwit for every subcircuit". This subsumes
     `call_constraints_and_specs` entirely, with read-off-the-term instantiation
     fixing its depth fragility.

  The result is a **single strengthened goal** — the original goal with every positive
  chunk replaced in place by its precondition bundle — plus one premised `h_spec_i` per
  chunk already in context. Since the goal's bundle position and `h_spec_i`'s premises
  need the same facts, house style is to prove each bundle once
  (`have pre₀ := ⟨…⟩`) and feed it to both — the goal position directly, and
  `h_spec_i pre₀.1 pre₀.2.1 pre₀.2.2` for the child's `Spec ∧ ProverSpec`.

### Leaf matching: read the arguments off the term

The matched chunk *contains* every argument the child contract needs — `child`, `cfg`,
`offset`, `input`, `place`, `env`, `self` are all subterms of the matched
`Constraints`/`call` application. The engine unifies against the folded call boundary
(same opacity contract as the iffs: `call` is never unfolded by `circuit_norm`) and
instantiates the child's contract itself. Consequences:

- Zero user-side instantiation. `subcircuit_rw at hc` consumes every chunk in `hc`.
- Discrimination-tree spelling is irrelevant: matching is the tactic's own `isDefEq`
  against the `Constraints`-headed subterm, not simp's keyed lookup. The `Placed` vs
  bare and abstract-α vs concrete-α families all collapse.
- Depth robustness: the engine controls its own unification order (match the
  `Constraints` head first, then read arguments syntactically), avoiding the open-ended
  mvar search that blew up `call_constraints_and_specs`.

### What it deliberately does NOT do

- Chunks in **negative** positions are left untouched (weakening there is unsound).
  In practice chunks only occur positively (constraint hypotheses, constraint goals);
  a chunk under a hypothesis's `→`-left would be skipped silently — acceptable, and the
  tactic reports matched/skipped counts.
- It does not unfold or normalize anything else. Sequencing stays: `circuit_norm` simp
  → `provable_type_simp` → `abstract_outputs` → `subcircuit_rw` → row-fact chaining. The
  starting tactic that composes these now exists — `circuit_proof_start`
  (`Clean/Halo2/Tactics/CircuitProofStart.lean`).
- Knowledge-soundness check: `extract` is a function of the environment, not of the
  constraint proposition, so consuming the chunk entirely loses nothing an extractor
  needs.

## Migration and retirement

1. Engine lands with its own test file mirroring TestSubcircuit/TestLayouterSubcircuit
   (every consumption pattern the four consumers use, both levels, loop context).
2. The C1 gadget-restructure pass migrates consumers to `subcircuit_rw` as it touches
   each file (it touches them all anyway).
3. After migration: the absorption iffs, both markers, the concrete-α/`_bare` variant
   families, and `call_constraints_and_specs` copies retire from `Subcircuit.lean`;
   the file shrinks to `call`/`toFormal`/`CoeFun` + the engine's congruence lemmas.

## Decisions (maintainer, 2026-07-11)

- **D1 — iff lemmas retire fully** after migration; nothing stays in `circuit_norm`
  (they would act against the tactic).
- **D2 — ONE tactic** doing goal + hwit processing simultaneously (hwit is needed both
  to discharge ExtendsWitnesses on goal chunks and to introduce the derived contract
  statements — two tactics can't split that). Exact mechanics are free as long as the
  reduction matches main Clean's (its subcircuit-type props + modified soundness/
  completeness statements).
- **D3 — silent on shapes it doesn't target.** No info messages; a debug flag for
  development is fine. The statement shapes are known and the tactic targets exactly
  those.

## Completeness mode redesign reverted (maintainer, 2026-07-12)

A per-chunk-subgoal completeness redesign was tried and reverted. That variant surfaced each
positive goal chunk as a separate precondition subgoal `pre_i : EnvA ∧ A ∧ PA` (in op order),
collapsed the chunk position in the residual goal to `True`, and threaded a *bare* derived
statement `h_spec_i : Spec ∧ ProverSpec` (preconditions already consumed) into later contexts.
Its aim — writing each precondition bundle exactly once — is met instead by the house-style
dedup `have` described above.

Verdict: the premised single-goal shape described above (D2) **is** the main-Clean-faithful
reduction — subcircuit statements as premises in one goal context, matching how main Clean
states its subcircuit-composition obligations. The per-chunk-subgoal variant was designed
against a simplified model of what real circuit proofs need; real proofs need shared
honest-value bookkeeping across chained/composed subcircuits (e.g. one child's derived
`ProverSpec` feeding the next child's precondition, or both a precondition and a parent-level
gate) in a SINGLE goal context, which splitting into separate subgoals breaks — each subgoal
sees only its own local context, not the sibling facts the bookkeeping needs to flow through.

It is removed. There is exactly one completeness behavior now: bare `subcircuit_rw` always does
the single-goal premised-`h_spec_i` strengthening (no `legacy` token — there is nothing to
distinguish it from anymore).
