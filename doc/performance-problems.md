# Performance Problems in Circuit Proofs

Lessons from debugging proofs that exceed `maxHeartbeats` or die with
`(kernel) deep recursion detected`. The case study behind all of this is
`Clean/Orchard/Ecc/ScalarMul/MulFixed/FullWidth.lean` (`completeness`), but the failure
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
