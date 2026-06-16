# NoteCommit helper purge notes

This file records proof ideas removed from `Clean/Orchard/NoteCommitGadget.lean` during
the helper purge. The deleted Lean declarations were mostly shaped as manual
`ConstraintsHold.Soundness` unpackers. Do not restore them in that form.

## Top-level proof shape

Start `soundness` from:

```lean
circuit_proof_start [main, Assumptions, Spec]
```

The tactic already exposes:

- `h_input`: evaluated input fields equal the named input values.
- `h_assumptions`: semantic assumptions.
- `h_holds`: the source-shaped split of `main` into `assignMessageCells` and
  `commitAndConstrain`.

Do not rebuild `main_soundness_constraints_iff`, `commitAndConstrain_*_iff`, or similar
trace lemmas. If a subcircuit spec is needed, get it from the `h_holds` structure exposed
by `circuit_proof_start`, or include the child circuit/spec in the tactic's simp list.

## Semantic bridge still needed

The final soundness proof reduces to:

1. Apply the `Sinsemilla.CommitDomain.WithZs` spec for the committed pieces.
2. Prove those committed pieces produce exactly
   `Orchard.Specs.Sinsemilla.noteCommitChunks gdX gdYbit pkdX pkdYbit v rho psi`.
3. Apply `spec_of_commitWithZs_spec`.

The hard part is not unpacking `ConstraintsHold`; it is the semantic chunk equality.

## Pure lemmas worth preserving

The following are mathematical and were intentionally kept:

- `lsb_eq_y_low_bit_of_parts`
- `j_lt_tP_of_prime_bounds`
- `y_lsb_eq_low_bit_of_row_facts`
- `noteCommitChunks_*` tiling/segment lemmas
- `pieceChunks_eq_noteCommitChunks_of_indexed_piece_values`
- arithmetic facts relating subpiece sums to field values, when they do not mention
  `ConstraintsHold`.

These can be applied from the top-level proof once the corresponding gate specs are
available through `circuit_proof_start`.

## Deleted proof ideas

The deleted helpers extracted useful facts, but in the wrong API shape. Recreate only the
following ideas directly inside the top-level soundness proof or as pure lemmas:

- `CopyCheck` running sums with a zero tail imply value bounds. The pure version should
  state this over a running-sum chain relation or `Chain.ZsFacts`, not over
  `ConstraintsHold.Soundness`.
- `canonBitshift130`, `pkdXCanonicity`, `rhoCanonicity`, and `psiCanonicity` prime bounds
  should be derived from formal assertion specs after `circuit_proof_start`, not by
  manually projecting the subcircuit trace.
- `yCanonicity` should yield the pure row facts needed by
  `y_lsb_eq_low_bit_of_row_facts`. The clean proof should obtain the
  `NoteCommit.YCanonicity.Spec` row from the top-level proof context, then apply pure
  range/low-bit lemmas.
- Piece equalities for `a` through `h` should be proven in the soundness proof from
  `assignMessageCells` and `constrainCommitment` facts exposed by the tactic, not as
  separate `main_*_of_soundness` lemmas with full circuit hypotheses.

## Source facts to preserve

From `orchard/src/circuit/note_commit.rs` and `halo2_gadgets/src/sinsemilla.rs`:

- `MessagePiece::from_subpieces` packs subpieces little-endian by accumulating
  `acc + 2^bits * subpiece`.
- Piece `b` is `b0 + 16*b1 + 32*b2 + 64*b3`.
- Piece `d` is `d0 + 2*d1 + 4*d2 + 1024*d3`.
- Piece `e` is `e0 + 64*e1`.
- Piece `g` is `g0 + 2*g1 + 1024*g2`.
- Piece `h` is `h0 + 32*h1`; the remaining four bits are zero.
- `d1` is the `y_canonicity(input.pkd.y, subpieces.d1)` result and must become
  `pkdY.val % 2`.
