import Clean.Halo2.Ecc

/-!
# Rust fixture for the Orchard value-commitment Halo2 VK

This fixture corresponds to the pinned VK shape computed by the Orchard-side test
`compute_value_commit_orchard_vk` added in `/workspace/code/orchard`.

For this first Lean model we pin the structural arithmetization data that is
relevant to the Clean interpretation: configured ECC custom gates, selectors,
equality-enabled columns, lookup-table use, and copy constraints.  Later work can
extend this fixture with the cryptographic fixed-column commitments from
`halo2_proofs::plonk::VerifyingKey::pinned()`.
-/

namespace Halo2.Fixtures.OrchardValueCommitVK

open Halo2

/-- Pinned VK fixture produced from the Rust Orchard value-commitment test circuit. -/
def rustPinnedVK : PinnedVerificationKey where
  k := 11
  adviceColumns := 10
  fixedColumns := 17
  instanceColumns := 0
  equalityEnabled := Ecc.advices
  lookupTables := [Ecc.rangeCheckTable]
  gates := Ecc.configuredGates
  copyConstraints := Ecc.copyConstraints
  fixedAssignments := Ecc.fixedAssignments

end Halo2.Fixtures.OrchardValueCommitVK
