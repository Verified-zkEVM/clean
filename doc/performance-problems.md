# Performance Problems in Circuit Proofs

Lessons from debugging proofs that exceed `maxHeartbeats` or die with
`(kernel) deep recursion detected`. The case study behind all of this is
`Clean/Orchard/Ecc/MulFixed/FullWidth.lean` (`completeness`), but the failure
modes are generic.

## The root failure mode: whnf into expensive values

Both the elaborator and the kernel decide definitional equality by `whnf`-reducing terms.
That is usually cheap, but it becomes catastrophic when a term *can* be unfolded into a
large concrete computation:

- `Finset.range n` sums for concrete `n` (e.g. `offsetAcc`),
- `ZMod` arithmetic over a 255-bit concrete modulus (`.val`, `Nat.cast`, `npow`),
- recursive definitions applied at a concrete depth (e.g. `partialSum ks 83`),
- `n • point` (`nsmulRec`) where the scalar is one of the above.

The same term applied at a *symbolic* index is free: `windowScalar w k` gets stuck
immediately on the `w = 84` test when `w` is a variable, while `windowScalar 84 k`
reduces into `offsetAcc` and beyond. So a proof step that is instant for the loop
iteration `j + 1` can blow up for the literal window `84`.

Important asymmetry: **the elaborator passing does not mean the kernel will.** The
kernel re-checks every defeq embedded in the final proof term — type ascriptions,
`show`/`change`, `exact` against a defeq-equal type, structure-eta `rfl`, and the
definitional (dsimp) steps inside `simp` rewrites — and it has neither the elaborator's
caches nor its heuristics. Kernel failures appear as `(kernel) deep recursion detected`
reported at the *theorem header*, after all tactics succeeded.

## Patterns that fix it

The common theme: make the dangerous value **opaque** before any defeq touches it, and
cross between different spellings of the same value by **syntactic rewriting** (`rw`,
`simp only`) rather than by unification.

1. **Extract witness values through a lemma over an opaque variable.** Instantiating
   `h_env`-style hypotheses (`∀ i : Fin n, env.get (ofs + i) = (toElements v)[i]`) at a
   component with a type ascription makes unification reduce `(toElements v)[1]` against
   a field projection, unfolding `v`'s field values. Instead, state a helper lemma over
   an opaque `r`, prove it by destructuring `r` and
   `simp only [explicit_provable_type, circuit_norm, Nat.reduceMod, Nat.add_zero]`,
   and apply it (see `env_get_row` in `FullWidth.lean`). Application only pattern-matches
   `r := rowValue B input 84`; nothing unfolds.

2. **Bridge spellings with `rfl`-lemmas stated at a symbolic index.** A `rfl` like
   `(rowValue B s w).xP = (windowPoint B.point w (windowVal s w)).x` is cheap to check
   for variable `w` (everything stuck), and `rw` with it instantiated at `w := 84` is a
   substitution into an already-proved equation — no defeq at 84 ever happens. Closing
   the same goal at `w := 84` by `rfl`/`show` instead makes the kernel evaluate the
   window-84 scalar.

3. **Same trick for structure eta.** `r = { window := r.window, ... }` by `rfl` is cheap
   when `r` is opaque, deadly when `r` is `rowValue B input 84` (the kernel unfolds the
   concrete fields). Prove a `coordsRow_eq`-style lemma over opaque `r` once and apply it.

4. **Generalize concrete scalars to opaque variables.**
   `obtain ⟨S, hS_def⟩ : ∃ S, partialSum (windowVal input) 83 = S := ⟨_, rfl⟩`
   and use `S` from then on; rewrite with `← hS_def` exactly where a lemma needs the
   literal form. Soundness proofs often get this for free because their values come from
   existential witnesses (`obtain ⟨S, ...⟩`) — that is why a soundness proof can be fine
   while the structurally identical completeness proof explodes: completeness names the
   honest prover values concretely.

   **`set` is not enough for this.** `set x := e with hx` introduces a let-bound local
   that the kernel can still zeta-unfold, so the dangerous value remains reducible. Only
   the `obtain`-an-existential form produces a genuinely opaque variable. (The short
   fixed-base mul soundness proof originally used `set` for the window function and died
   in the kernel; switching to `obtain ⟨ks, hks_def⟩ : ∃ ks', ks' = fun w => ... := ⟨_, rfl⟩`
   fixed it.)

5. **Keep `Option`-level plumbing out of big contexts.** Converting
   `(hashToPoint ...).isSome` to `∃ B, ... = some B` *inside* a circuit proof (via
   `Option.isSome_iff_exists.mp`) triggered a 200k-heartbeat `whnf` on the stuck chain
   value. Stating the assumption in `∃`-form to begin with made the same `obtain` free.
   Generally: pick hypothesis spellings that destructure by constructor, with no lemma
   application at use site.

6. **Don't `subst` a variable that a huge context depends on.** In a leaf case of a
   completeness proof, `obtain rfl : w = 0 := by omega` retypechecks every hypothesis
   with `w := 0`, turning previously-stuck symbolic powers (`2 ^ (K * (w + 1))`) into
   concrete values — instant `isDefEq` timeout. Rewrite only the hypothesis you need
   (`rw [show w = 0 from by omega] at hbound`) and leave the context symbolic.

7. **Prefer `have` over `obtain ⟨..⟩ :=` for big conjunctions.** Destructuring a
   conjunction whose components are large (`rcases`/`obtain` on an aux-lemma
   instantiation) can cost far more than the application itself; binding with `have` and
   using `.1`/`.2` projections at the use sites avoided a budget overrun where the
   `obtain` form died.

8. **A `try`/`first` combinator does not suppress nested `by`-block failures.** In
   `all_goals try (obtain rfl : r = 0 := by omega)`, a failing inner `omega` is *logged*
   as an error even though `try` catches the tactic failure. Same for the anonymous
   hypothesis term `‹r < 1›` (which elaborates to `by assumption`). Branch explicitly
   (`rcases Nat.lt_or_ge r 1 with h | h`) so omega only runs where it succeeds.

9. **Big power literals (`2^130`, `2^254`) reduced by the kernel cause
   `(kernel) deep recursion detected`.** The kernel has accelerated `Nat.add/mul/mod`
   but *not* `Nat.pow`, so a `2^254` that survives into a kernel-checked proof term is
   unfolded ~254 deep, and nested inside a `norm_num`/`omega` certificate it blows the
   recursion limit — reported at the *enclosing declaration's header*, not the offending
   line. Three rules that fixed `base_field_elem`'s canonicity bound (`alpha0_lt_tp`):
   - **Keep powers opaque to `omega`.** Prove the pure-literal facts in *one* isolated
     `have h : 2^130 + tPNat < PALLAS_BASE_CARD ∧ … := by norm_num [PALLAS_BASE_CARD, …]`,
     then feed `omega` only linear hypotheses (`S < 2^130`, `h`, `α0 < 2^132`) where
     `2^130`/`2^132` are atoms it never reduces. `omega` closing `S + t < P` from
     `S < X ∧ X + t < P` treats `X` opaquely.
   - **Avoid `base_card_eq` in the hot path.** Rewriting `PALLAS_BASE_CARD` to
     `2^254 + tPNat` *introduces* a `2^254` the kernel then reduces. Bound against the
     `PALLAS_BASE_CARD` *literal* (it's `@[reducible]` to a hex numeral) instead.
   - **Prefer additive `Nat.ModEq` over `Nat.cast_sub`/`ZMod.val`.** To turn
     `(S:Fp) = ↑α0 + (2:Fp)^130 - ↑tPNat` into a ℕ equation, cross-multiply to
     `↑(S + tPNat) = ↑(α0 + 2^130)` (`push_cast; linear_combination`), then
     `(ZMod.natCast_eq_natCast_iff …).mp` + `Nat.mod_eq_of_lt` on both sides. This dodges
     the `tPNat ≤ α0 + 2^130` subtraction side-goal whose `norm_num [tPNat]` was itself
     the recursion trigger.
   Always factor such arithmetic into a `private theorem` over abstract `ℕ` variables so
   it is kernel-checked once, not inlined into a giant circuit-soundness term.

## Kernel size cliffs in completeness proofs of large compositions

A second, distinct kernel failure mode showed up in the variable-base scalar-mul *entry*
circuit (`Mul/Assign.lean`, a composition of five verified subcircuits): the
completeness proof elaborates fine, every goal closes, and the kernel still reports
`(kernel) deep recursion detected` at the theorem header. Bisection (move a closing
`sorry` through the proof) showed no single poisonous step — instead a *cliff*: past a
certain accumulated proof-term size, any marginal addition (a small lemma application, a
`rw`, even an `exact` with all arguments sorried) tips the kernel over. Facts that made
the bisection legible:

- **`have`-bound terms are never pruned.** `have h := e; rest` elaborates to
  `(fun h => rest) e`, so `e` is in the final term whether or not `h` is used. The only
  things excluded from the kernel's workload are tactics *after* the goal-closer. A
  "minimal" repro with one `have hAcc := h_env.1; sorry` can therefore carry the entire
  normalization cast of `h_env` — and an unused-looking hypothesis is never free.
- **`rcases`/`obtain` on a big conjunction multiplies the goal into every `casesOn`
  motive** (item 7 above, but it bites the kernel too, not just the elaborator budget).
  An 11-way `obtain` on the completeness `h_env` died where `.1`/`.2` projections passed.
- **`circuit_proof_start`'s one-shot `simp ... at h_env` can be the largest single
  cast.** For this circuit the kernel could not re-check it at all. Workaround (see
  `Assign.lean`): `circuit_proof_start_core`, then `dsimp only [main, circuit_norm] at
  h_env` (definitional, castless), project the components with `.1`/`.2`, `clear h_env`,
  and `simp only [circuit_norm, h_input, <child circuits>]` on each small component
  separately. Each per-component cast is kernel-checkable.
- **Move every self-contained argument into a standalone `private theorem` over opaque
  variables.** Each lemma is kernel-checked as its own declaration; the main proof pays
  only an application node. In `Assign.lean` this rescued the honest-witness arguments
  (`chain_cells`, `z0_cell_value`, `mul_spec_honest`, …) which all kernel-fail when
  inlined and all pass standalone.

When all of the above still isn't enough — the parent is simply too big — the fix is
architectural: **split the parent into subcircuits**. Subcircuits in Clean are virtual:
they add no constraints, witnesses, or wiring, so introducing one where the reference
implementation (e.g. halo2) inlines a function preserves circuit/VK fidelity exactly.
But each child's soundness/completeness becomes its own kernel-checked declaration, and
the parent sees one folded `Assumptions → Spec` implication per child instead of the
child's full operation list. This is the same decomposition that keeps Poseidon, Keccak,
BLAKE3 and SHA-2 tractable. Rule of thumb: *when a parent circuit's completeness
kernel-fails at the theorem header and bisection shows a cliff rather than a culprit,
the circuit is asking for a subcircuit boundary.*

## Chained `Circuit.foldl` calls: a composition cliff, fixed by an opaque prefix `def`

`Clean/Orchard/Ecc/MulFixed/BaseFieldElem.lean`'s `RunningSumMul.main` sequences two
`Circuit.foldl` calls (windows `1..42` and `44..83`, with an explicit window 43 in
between). The default `requirementsChannelsLawful` proof on `FormalCircuitBase`
(`dsimp only [main]; simp only [circuit_norm, seval]; ...`) kernel-fails
(`(kernel) deep recursion detected` at the theorem header) on this circuit, while the
sibling `FullWidth.lean` — same rough complexity, a *single* `Circuit.foldlRange 83` —
builds fine with the same default proof.

Bisection (via standalone `lean <scratch-file>.lean` runs against the same `LEAN_PATH`,
not full `lake build`, for fast iteration) pinned this down precisely:

- **One fold, alone, is fine.** `simp only [circuit_norm, seval]` proves
  `((Circuit.foldl (Vector.finRange 42) init body).operations n).shallowChannels = []`
  standalone with no issue, for any `init`/`n` (even symbolic).
- **Two folds side by side, with independent/fresh `init`s, are also fine together** —
  so "two folds" alone is not the problem.
- **Two folds *chained through real data flow*** — fold1's output feeds an intervening
  window's `AddIncomplete.circuit`, whose output feeds fold2's `init` — is what breaks,
  and this reproduces even with a *tiny* second fold (`Vector.finRange 2`), so it is not
  about the second fold's size either. The problem is that fold2's `init`, by the time
  its own channel facts are wanted, is a deeply-layered expression (several extra
  `Circuit.bind` layers from the intervening window) sitting on top of fold1's own
  nontrivial output — reasoning about both inside one `simp` call / kernel check crosses
  the recursion-depth wall. This is a novel case for "kernel size cliffs" above: it's not
  really about the *number* of subcircuit calls in the parent, but about the *nesting
  depth of `.output`/`.localLength` computations* chaining through successive `Circuit.bind`
  layers before the second fold is reached.
- The default proof **does** close the goal via this path (confirmed: removing its closing
  fallback tactics changes nothing) — the failure is purely a *kernel check* on the
  resulting term, not an elaboration-time timeout. This matters: a *conditional-rewrite*
  lemma stating "a fold's `shallowChannels` is `[]` if its body's is, for abstract
  `acc`/`a`/`offset`" does NOT help if `main` is still `dsimp`'d in one shot, because
  `Circuit.foldl.output_eq`/`localLength_eq` (still needed elsewhere, to know where the
  next window starts) re-derive the fold body in an "already normalized" shape (`match` on
  a pair reduced to `.1`/`.2` projections) that no longer syntactically matches a fresh
  restatement of the same body — so a lemma written out fresh doesn't fire via `rw`/`simp`,
  and letting `simp` re-derive everything reproduces the exact same blowup.

**The fix**: extract the chained prefix (window 0 + the *first* fold + the intervening
window) into its own **opaque `def`** — *not* a subcircuit (no separate
soundness/completeness needed), purely to stop `simp`/the kernel from reasoning about the
whole chain in one term:

```lean
private def prefixCircuit (B : ...) (alpha : Var field Fp) :
    Circuit Fp (Var Point Fp × Expression Fp × Expression Fp) := do
  <window 0, the first fold, the intervening window>
  return (acc, zBeforeWindow, zAfterWindow)  -- return everything downstream code needs

def main (B : ...) (alpha : Var field Fp) : Circuit Fp (Var Output Fp) := do
  let (acc, zBeforeWindow, zAfterWindow) ← prefixCircuit B alpha
  <second fold, using zAfterWindow as its init component; zBeforeWindow used later>
```

Critically, **`main`'s own source has to call `prefixCircuit`** — it is not enough to
state an external `main = prefixCircuit >>= rest := rfl` lemma without touching `main`.
That `rfl` works fine for the prefix alone, but blows the *elaborator's* recursion budget
(`maximum recursion depth`, then a heartbeat timeout even after raising `maxRecDepth`) once
the whole tail (through the final output-struct assembly) is included in one equality —
apparently proving a *fresh* copy of the full circuit is definitionally equal to `main`
forces exactly the same expensive comparison the extraction was meant to avoid. Changing
`main`'s source directly sidesteps needing that equality at all: `dsimp only [main]`
naturally exposes `prefixCircuit B alpha` as an opaque call with the second fold's `init`
bound to *fresh pattern-bound variables* — not a deeply layered expression — which is what
actually defuses the blowup.

Since this is a pure repackaging (identical constraints/witnesses/offsets — `prefixCircuit`
is never itself a subcircuit boundary), the *existing* `main`-unfolding proofs
(`soundness`/`completeness`, via `circuit_proof_start [main, ...]`) keep working completely
unchanged, just by adding `prefixCircuit` to their unfold argument list alongside `main`
(since the two unfold together, the resulting term is identical to before the split).

For the standalone `requirementsChannelsLawful`, prove `prefixCircuit`'s own
`shallowChannels`/`subcircuitChannelsWithRequirements` facts standalone (cheap — this is
exactly the "single fold, no chaining" case confirmed fast above), then combine with a
small helper turning `subcircuitChannelsWithRequirements = []` + `shallowChannels = []`
into the full `RequirementsChannelsLawful` fact (a circuit that never emits raw channel
interactions has `shallowChannels = [] ⟹ shallowInteractions = []`, which trivializes the
"under local constraints" conjunct). Once the prefix is opaque, the plain *default*
`Circuit.foldl.shallowChannels`/`subcircuitChannelsWithRequirements` simp lemmas handle the
second fold directly — no custom conditional fold lemma is needed at that point.

As a side effect, this same file's `completeness` proof had an unrelated-looking
`(deterministic) timeout at isDefEq/whnf` failure in a bullet reasoning about the *second*
fold's windows (a `rw [...] at h` chain bridging offset spellings) — bisection there
suggested no single culprit tactic. That failure disappeared with no changes to its own
proof text once `prefixCircuit` shrank the term `dsimp only [main]` produces everywhere in
the file; it was apparently sensitive to the same cumulative-size pressure.

## RESOLVED: a kernel/elaborator size cliff from unifying against an unfolded `∀`-spec

`Clean/Orchard/Ecc/MulFixed/BaseFieldElem.lean`'s outer `soundness` proof had a `have hVltp
: V < PALLAS_BASE_CARD := by rw [base_card_eq]; rcases hAlpha2 with ha2 | ha2 · ... · ...`
whose second (`α2 = 1`) branch was ~70 lines, ending by wiring 13 individual
`hChain ⟨k, _⟩` facts (from a 13-window `CopyCheck` lookup) into a `telescope13_eq` helper.
This branch timed out (`(deterministic) timeout at whnf`, both at a step deep in the branch
and, separately, at the *theorem header*).

Bisection (moving a `sorry` through the proof) showed this was a genuine cliff, not a
single culprit tactic: a **bare `sorry` placed immediately after** `rcases hAlpha2 with ha2
| ha2` (i.e. before any of the `α2 = 1` branch's own reasoning ran) still timed out at the
exact same location, and neither the `obtain ⟨S, hSdef⟩ := ⟨_, rfl⟩` line nor its explicit-
witness variant was the culprit (both failed identically, and removing the `obtain`
entirely still failed at the same spot) — the cumulative proof term up to that point was
already at the cliff.

**The fix**: replace the 13 individual `hChain ⟨k, _⟩` destructures + `telescope13_eq` with
a single application of `Utilities.LookupRangeCheck.CopyCheck.spec_telescope` — a generic
lemma already proven in `Utilities.lean`, stated over an abstract `let f : ℕ → Fp := fun i
=> if hi : i < numWords + 1 then zs[i]'hi else 0` indirection specifically so the ∀-quantified
running-sum chain is proven once, over an opaque function, rather than combined ad hoc from
13 concrete getElem instances every time a consumer needs it.

The subtlety (this is the part that wasn't obvious going in): **naively applying
`spec_telescope` to the existing `hCopy` still timed out**, just relocated to the `obtain`
line itself. Root cause: `hCopy` came from a `circuit_proof_start [..., CopyCheck.circuit,
CopyCheck.Spec]` call with `CopyCheck.Spec` in the unfold list, so `hCopy`'s type was the
*fully-unfolded raw conjunction* (`zs[0]'_ = element ∧ ∀ i : Fin 13, ∃ word, ... zs[i.val]'_
= ...`), with the messy concrete `Vector.cast`/`Vector.append`/`Vector.mapRange` getElem
chain sitting *inside* the `∀`'s body. Applying `spec_telescope` (whose hypothesis argument
has an implicit `zs`) then forces Lean to unify `Spec ?numWords ?element ?zs ?data` against
that already-unfolded conjunction, which requires descending under the `∀` binder and
unifying `?zs[i.val]'_` — for a *symbolic* bound `i` — against the concrete vector's getElem
expression. Since `?zs` isn't applied directly to `i` (it's wrapped in a `GetElem.getElem`
projection), this isn't a Miller/higher-order pattern, so Lean can't assign `?zs` cheaply;
it falls into general unification that tries to `whnf` the concrete vector expression at a
symbolic index, gets stuck (case-splits on `Decidable` instances that can't reduce for a
non-literal index), and loops until the heartbeat budget is exhausted.

**The actual fix**: remove `Utilities.LookupRangeCheck.CopyCheck.Spec` from the
`circuit_proof_start` unfold list (keep `.circuit`). This leaves `hCopy : CopyCheck.Spec 13
alpha0Prime zsBigTerm data` *folded* — an opaque application to already-resolved concrete
arguments. Unifying `spec_telescope`'s implicit args against `hCopy`'s type is then a
**direct argument-by-argument match on the outer `Spec` application**, never unfolding
`Spec`'s body (the `∀`) at all, since both sides share the head symbol `Spec`. This is the
"keep the dangerous value opaque before any defeq touches it" principle from the "Patterns
that fix it" section above, applied to an entire hypothesis's *type* (by controlling
`circuit_proof_start`'s unfold list) rather than to a witnessed value.

Two smaller follow-on fixes, both cheap once the timeout was gone:
- After `rw [hCopy.1] at htel` (cheap — `htel`'s `zs[0]` subterm is literally `hCopy`'s own
  `zs[0]` term post-unification, a syntactic match), `htel`'s remaining `zs[13]` subterm was
  spelled `(Vector.map (Expression.eval env) (Vector.cast ⋯ V))[13]`, while the `hz13`
  hypothesis it needed to combine with (from a *different* destructuring path via
  `Gate.CanonicalHighBit`) was already simplified to `Expression.eval env (V[13])` by an
  earlier, unrelated simp pass. Fixed with `simp only [Vector.getElem_map,
  Vector.getElem_cast] at htel` (both `@[simp]` in Lean core) — cheap here because `htel` at
  this point is a single concrete equation, the `∀` having already been consumed inside
  `spec_telescope`/`chain_telescope`. Must run *after* `rw [hCopy.1]`, not before, else it
  also normalizes the `zs[0]` subterm and breaks that rewrite's syntactic match.
- `have hK13 : K * 13 = 130 := by norm_num [Orchard.Specs.K]` silently elaborated the bare
  `K` as an unrelated local type variable (this file uses `K` as a type-variable name in
  several other defs), producing a nonsensical goal. Fixed by using the fully-qualified
  `Orchard.Specs.K` in the statement itself, not just inside `norm_num`'s lemma list.

`telescope13_eq` became fully dead code after this change (verified via a whole-repo
`grep`) and was deleted; `alpha0_lt_tp` is still used. Confirmed via a fresh `lake build`
(stale `.olean` removed first): green, zero `sorry`s, zero lint warnings.

## Measuring honestly

- **`#count_heartbeats in` lies for this purpose.** It runs the command with an
  *unlimited* heartbeat budget and can under-report work done in async proof-body
  elaboration. A declaration that "uses 1366 heartbeats" under the wrapper can time out
  at 200000 without it. Use it only for rough profiling of commands that already pass.
- To verify a declaration is genuinely cheap, put `set_option maxHeartbeats <low> in` on
  it and see if it still compiles. Lowering the budget also makes the debug loop fail
  fast instead of grinding for minutes. (Never raise `maxHeartbeats` in committed code.)
- Fast iteration: `lake env lean <file>` re-elaborates just that file against prebuilt
  imports (seconds, vs a full `lake build`). Bisect a failing proof by truncating it with
  `sorry` plus a block comment and moving the cut point; this works for kernel errors
  too, since the kernel checks whatever partial term elaboration produced.
- `set_option diagnostics true in` on the failing declaration prints unfold counters —
  `Eq.rec`, `List.rec`, `dite`, `Vector.append`, `Nat.rec` in the tens of thousands is
  the signature of a runaway whnf.
