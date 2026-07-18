import Clean.Ironwood.Ecc.Basic
import Clean.Ironwood.Ecc.WitnessPoint
import Clean.Ironwood.Ecc.AddIncomplete
import Clean.Ironwood.Ecc.Add
import Clean.Ironwood.Ecc.MulIncomplete
import Clean.Ironwood.Ecc.MulComplete
import Clean.Ironwood.Ecc.MulOverflow
import Clean.Ironwood.Ecc.Mul
import Clean.Ironwood.Ecc.MulFixed
import Clean.Ironwood.Ecc.MulFixed.BaseFieldElem
import Clean.Ironwood.Ecc.MulFixed.FullWidth
import Clean.Ironwood.Ecc.MulFixed.Short
import Clean.Ironwood.Utilities.LookupRangeCheck
import Clean.Ironwood.CommitIvk.Gate
import Clean.Ironwood.CommitIvk.Bundle
import Clean.Ironwood.CommitIvk.Composite
import Clean.Ironwood.NoteCommit.Gates
import Clean.Ironwood.NoteCommit.Decompose
import Clean.Ironwood.NoteCommit.Canonicity
import Clean.Ironwood.NoteCommit.Composites
import Clean.Ironwood.NoteCommit.YComposite
import Clean.Ironwood.NoteCommit.Main
import Clean.Ironwood.Utilities.AddChip
import Clean.Ironwood.Poseidon.Pow5
import Clean.Ironwood.Poseidon.Rounds
import Clean.Ironwood.Poseidon.Permute
import Clean.Ironwood.Poseidon.Hash
import Clean.Ironwood.Sinsemilla.Basic
import Clean.Ironwood.Sinsemilla.HashPiece
import Clean.Ironwood.Sinsemilla.Chain
import Clean.Ironwood.Action.DeriveNullifier

/-!
# Ironwood circuits

Aggregator for the Ironwood (halo2-native) circuit modules, so they're built and
warning-checked (`--wfail`) as part of the main `Clean` library in CI.

`Clean.Ironwood.Sinsemilla.CommitDomain` and `Clean.Ironwood.Sinsemilla.Merkle` are
intentionally excluded: they carry stated `sorry`s pending the `MulFixed`/`CondSwap`
boundaries landing, and `--wfail` treats `sorry` as a build-failing warning. They will
rejoin this aggregator once those boundaries are in place.
-/
