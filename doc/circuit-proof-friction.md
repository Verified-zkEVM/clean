# Friction Points in Circuit Proofs

Feedback for the tactic/simp layer, collected while proving the variable-base
scalar-mul milestone (`copy_check`, `overflow_check`, `complete.rs::assign_region`,
`incomplete.rs::double_and_add`). Complements `performance-problems.md`, which covers
whnf/kernel blowups; this file covers cases where the *shape* of elaborated circuit
terms defeats the standard tactics.

## 1. Fold-carried loop state produces unmatchable lambdas (unresolved)

A `Circuit.foldlRange` whose body returns a state struct depending on the accumulator
(e.g. `return { prev := w, xA := s.prev.xANext }`) elaborates into
`Fin.foldl n (fun acc i => ...) init` inside every extracted hypothesis. That lambda
could not be matched by `rw` or `simp only` under any formulation we tried:

- a top-level `rfl`-equation whose LHS was refined until its `pp.explicit` output was
  **byte-identical** to the target (verified by mechanical string diff over the full
  ~6300-character explicit form) still failed kabstract with "did not find an
  occurrence of the pattern";
- realigning every visible instance difference (`IterCells.mk` at
  `field (Expression Fp)` vs `Expression Fp`, `List.sum`'s
  `MulZeroClass.toZero Nat Nat.instMulZeroClass` zero instance, `[1,1,1].sum` vs
  literal `3`) did not help;
- `simp only` with the same equation timed out instead.

Whatever kabstract compares differs in something not surfaced by `pp.explicit`
(binder types? structure-eta forms? metadata?). The eventual fix was architectural:
restructure the circuit so no iteration's *output* mentions the loop state.

**Post-mortem (added later):** the framework already encodes the right contract —
`Circuit.foldl` demands `ConstantOutput`, which is precisely what makes its proofs
collapse (`SHA256Compress.fin_foldl_eq_stateVar`, `Keccak/Permutation`); and even
state-dependent outputs are provable via the explicit `stateVar` +
`foldlAcc_eq_stateVar` recipe in `SHA256Compress.lean`. The failed body used
`foldlRange`, whose only hypothesis is `ConstantLength`, so the trap surfaced deep
inside the soundness proof instead of at definition time. The double-and-add was
eventually rebuilt with `Circuit.mapFinRange` over per-row witness blocks (row-major,
matching the halo2 assignment order), which has closed-form `output_eq`/`forAll`
lemmas and needed no collapse lemma at all. Tracked as
https://github.com/Verified-zkEVM/clean/issues/407 (document the loop combinators'
differing contracts; consider demanding `ConstantOutput` or warning in `foldlRange`).

## 2. Selective unfolding is load-bearing and trial-and-error

Putting expression-level helper defs (`Sinsemilla.DoubleAndAdd.yA`/`xR`) into the
`circuit_proof_start` unfold list blew `h_holds` into a whnf timeout: they occur in
every loop iteration's gate input, so unfolding multiplies term size by the iteration
count. The fix — unfold them only inside per-row extracted hypotheses — was found by
bisection. Similarly, `obtain` on `h_holds` whnf-times-out when an earlier unfold left
a stuck non-`∧` head, with the error reported at the theorem header.

Recommendation: document which kinds of defs are safe in the `circuit_proof_start`
list (Spec-level: yes; expression-formula helpers referenced inside loop bodies: no).

## 3. Expression-level `Sub`/`Neg` vs value-level subtraction

`Expression`'s `Sub` instance desugars to `add e₁ (mul (const (-1)) e₂)`, so once
`circuit_norm` pushes `Expression.eval` through a gate polynomial, the value-level
form is `a + -(1 * b)`-shaped. This is neither defeq nor `ring`-atom-equal to a spec
stated with field subtraction; `(-P).y` and `-(P.y)` are likewise distinct ring atoms
needing explicit `rfl`-bridges. Every equation crossing this boundary needs
`linear_combination` (with manually computed coefficients) instead of `exact`.

Recommendation: a simp set (or extension of `circuit_norm`) that canonicalizes both
worlds into a single subtraction form would remove a whole class of friction.

## 4. getElem bounds do not elaborate inline in statement types

`(#v[x] ++ Vector.mapRange n f)[i]'(by omega)` inside a `have`/`∃` statement type runs
the bound tactic against an unresolved metavariable (goal displayed as
`?m.626 v 13`) — `omega`, `norm_num`, and `get_elem_tactic` all fail, and
`get_elem_tactic` additionally hit `maxRecDepth` on append literals. The reliable
workaround is a helper lemma over an abstract `v : Vector _ k` (plus
`hv : v = <concrete>` when the cell values matter), instantiated with `_ rfl`.

## 5. Parser quirks in nested term/type positions

- `[1, 1, 1].sum` (dot notation) inside a structure literal in a theorem statement
  fails to parse ("unexpected identifier; expected '}'"); `List.sum [1, 1, 1]` — the
  identical term — parses fine.
- `({ ... } : T)`-ascribed structure literals in argument position inside larger
  statements fail with misleading "expected '}'" errors pointing at line ends.
  Dropping the ascription (letting unification determine the type) parses.

## 6. OfNat-indexed numerals

Gates parameterized over `[OfNat K (2 ^ 130)]` produce `OfNat.ofNat (2 ^ 130)` terms.
Unifying these against `(2 : Fp) ^ 130` recurses past `maxRecDepth`; the workaround is
an explicit `have : (OfNat.ofNat (2 ^ 130) : Fp) = 2 ^ 130 := by norm_num` bridge
before any `refine`/`exact` that would cross the gap.

## 7. Pass-ordering sensitivity (normalize vs rewrite)

Each proof needed a different interleaving of index-normalization (`norm_num`),
lemma-set simp passes, and targeted `rw`s, discovered by iteration:

- rewriting `zsAll`-style cell equations **before** `norm_num` works when the lemma
  instance spelling (`v[0+1]`) matches the raw hypothesis, and breaks after
  normalization folds the index to `v[1]` — and vice versa;
- the per-row extraction for the vector-shaped `double_and_add` only became tractable
  as one **fused** pass: `simp only [Vector.get, Vector.getElem_ofFn, Fin.val_mk]`,
  then a case split on the row index, then
  `norm_num [Vector.getElem_append, Vector.getElem_mapRange]` — which collapses every
  vector atom to a plain cell without the explosive motive checks that the
  `rw`-by-cell-equation route triggered.

Recommendation: a dedicated `circuit_row_norm`-style tactic that collapses
vector/index/ite atoms of an extracted per-row hypothesis in one canonical pass would
have roughly halved the iteration count of this milestone.

## 8. Tooling: probing giant contexts

The LSP cannot print these proof contexts within its 30s budget. The productive loop
is `lake env lean <file>` plus deliberate type-mismatch probes:

```lean
have hX1 : True := h_loop   -- the error prints h_loop's type, bounded by pp depth
exact (trivial : True)      -- the error prints the goal
```

combined with `set_option pp.explicit true in` when instance-level diffs are
suspected. Worth documenting in `proving-guide.md`; every theorem in this milestone
was built this way.
