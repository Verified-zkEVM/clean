module

public import Clean.Ironwood.Specs.Types
public import Clean.Ironwood.Specs.Bitrange
public import Clean.Ironwood.Specs.Pallas
public import Clean.Ironwood.Specs.PallasCert
public import Clean.Ironwood.Specs.Sinsemilla
public import Clean.Ironwood.Specs.SinsemillaBreak
public import Clean.Ironwood.Specs.SinsemillaGenerators
public import Clean.Ironwood.Utilities.RunningSum
public import Clean.Ironwood.Ecc.Defs
public import Clean.Ironwood.Ecc.DoubleAndAdd
public import Clean.Ironwood.Ecc.AddTheorems
public import Clean.Ironwood.Ecc.AddIncompleteTheorems
public import Clean.Ironwood.Ecc.MulTheorems
public import Clean.Ironwood.Ecc.MulIncompleteTheorems
public import Clean.Ironwood.Ecc.MulCompleteTheorems
public import Clean.Ironwood.Ecc.MulOverflowTheorems
public import Clean.Ironwood.Ecc.MulAssignTheorems
public import Clean.Ironwood.Ecc.MulFixed.Theorems
public import Clean.Ironwood.Ecc.MulFixed.BaseFieldElemTheorems
public import Clean.Ironwood.Ecc.MulFixed.ShortTheorems
public import Clean.Ironwood.Ecc.MulFixed.CertCheck
public import Clean.Ironwood.Ecc.MulFixed.Certs.NullifierK
public import Clean.Ironwood.Ecc.MulFixed.Certs.ValueCommitR
public import Clean.Ironwood.Ecc.MulFixed.Certs.SpendAuthG
public import Clean.Ironwood.Ecc.MulFixed.Certs.CommitIvkR
public import Clean.Ironwood.Ecc.MulFixed.Certs.NoteCommitR
public import Clean.Ironwood.Ecc.MulFixed.Certs.ValueCommitV
public import Clean.Ironwood.Sinsemilla.HVec
public import Clean.Ironwood.Sinsemilla.ChipTheorems
public import Clean.Ironwood.Sinsemilla.ChainTheorems
public import Clean.Ironwood.Sinsemilla.CommitDomainTheorems
public import Clean.Ironwood.Poseidon.Constants
public import Clean.Ironwood.Poseidon.Pow5Theorems
public import Clean.Ironwood.Poseidon.SpongeTheorems
public import Clean.Ironwood.Poseidon.HashTheorems
public import Clean.Ironwood.NoteCommit.CanonicityTheorems
public import Clean.Ironwood.NoteCommit.DecomposeTheorems
public import Clean.Ironwood.NoteCommit.MainTheorems
public import Clean.Ironwood.CommitIvk.GateTheorems
public import Clean.Ironwood.CommitIvk.ChunkTheorems
public import Clean.Ironwood.CommitIvk.MainTheorems
public import Clean.Ironwood.Ecc.Basic
public import Clean.Ironwood.Ecc.WitnessPoint
public import Clean.Ironwood.Ecc.AddIncomplete
public import Clean.Ironwood.Ecc.Add
public import Clean.Ironwood.Ecc.MulIncomplete
public import Clean.Ironwood.Ecc.MulComplete
public import Clean.Ironwood.Ecc.MulOverflow
public import Clean.Ironwood.Ecc.Mul
public import Clean.Ironwood.Ecc.MulFixed
public import Clean.Ironwood.Ecc.MulFixed.BaseFieldElem
public import Clean.Ironwood.Ecc.MulFixed.FullWidth
public import Clean.Ironwood.Ecc.MulFixed.Short
public import Clean.Ironwood.Utilities.LookupRangeCheck
public import Clean.Ironwood.CommitIvk.Gate
public import Clean.Ironwood.CommitIvk.Bundle
public import Clean.Ironwood.CommitIvk.Composite
public import Clean.Ironwood.NoteCommit.Gates
public import Clean.Ironwood.NoteCommit.Decompose
public import Clean.Ironwood.NoteCommit.Canonicity
public import Clean.Ironwood.NoteCommit.Composites
public import Clean.Ironwood.NoteCommit.YComposite
public import Clean.Ironwood.NoteCommit.Main
public import Clean.Ironwood.NoteCommit.MainBundle
public import Clean.Ironwood.CommitIvk.Main
public import Clean.Ironwood.CommitIvk.MainBundle
public import Clean.Ironwood.Utilities.AddChip
public import Clean.Ironwood.Poseidon.Pow5
public import Clean.Ironwood.Poseidon.Rounds
public import Clean.Ironwood.Poseidon.Permute
public import Clean.Ironwood.Poseidon.Hash
public import Clean.Ironwood.Sinsemilla.Basic
public import Clean.Ironwood.Sinsemilla.HashPiece
public import Clean.Ironwood.Sinsemilla.Chain
public import Clean.Ironwood.Action.DeriveNullifier
public import Clean.Ironwood.Action.ValueCommit
public import Clean.Ironwood.Action.SpendAuthority
public import Clean.Ironwood.Action.AddressIntegrity
public import Clean.Ironwood.Ecc.Chip
public import Clean.Ironwood.Action.Circuit
public import Clean.Ironwood.Action.Bundle
public import Clean.Ironwood.Action.RealBases
public import Clean.Ironwood.Action.Spec
public import Clean.Ironwood.Action.Separation
public import Clean.Ironwood.Action.Shape

@[expose] public section

/-!
# Ironwood circuits

Aggregator for the Ironwood (halo2-native) circuit modules. Ironwood is kept separate
from the main `Clean` library export and can be built with `lake build Zcash`.
-/
