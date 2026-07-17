import Clean.Halo2.Fixtures.MerklePre
import Clean.Halo2.Fixtures.MerklePost
import Clean.Halo2.Fixtures.MerkleSelMap
import Clean.Halo2.Tests.TestVkMatchSinsemilla
import Clean.Ironwood.Sinsemilla.Merkle

/-!
# VK-match test: the Merkle chip (`MerkleConfig`) — the full Sinsemilla+Merkle chain

Continues the Sinsemilla configure-chain (`TestVkMatchSinsemilla.sinsemillaProgram` — the
Rust `register_prereqs` sequence ending in the real `SinsemillaChip::configure`) with the
real `MerkleChip::configure` (`merkle/chip.rs:109-212`), which itself runs
`CondSwapChip::configure` (q_swap + the 3-constraint swap gate) and then `q_decompose` +
the 4-constraint `Decomposition check` gate. Projects the resulting `ConstraintSystem` and
checks it **equal** to the dumped fixtures, BOTH phases:

* `merklePre` — pre-selector-compression: the 4 Sinsemilla-chain gates + 3 swap
  constraints (selector 5) + 4 decomposition constraints (selector 6); the query layouts
  are IDENTICAL to `sinsemillaPre` (both new gates reuse already-registered rot-0/1
  queries on the five hash advices).
* `merklePost` — post-`compress_selectors` with the REAL packing gathered from a real
  `CondSwapChip::swap` + `MerkleChip::hash_layer` synthesize (`Value::unknown()`, k=11),
  applied mechanically via `projectCSPostMap` (`merkleSelMap`).

The comparison is `#guard` on `DecidableEq CsFixture`.
-/

namespace Halo2.Fixtures.Test

open Ironwood (Fp)

/-- The Merkle configure chain: the full Sinsemilla prerequisite chain, continued by the
real `MerkleChip::configure` on the resulting config. -/
def merkleProgram : Configure Fp Ironwood.Sinsemilla.Merkle.Config := do
  let scfg ← sinsemillaProgram
  Ironwood.Sinsemilla.Merkle.configure scfg

def merkleCS : ConstraintSystem Fp := (merkleProgram {}).2

/-- The whole-chain registration-order query seed (see `TestVkMatchMul.mulSeed`). -/
def merkleSeed : List Query :=
  merklePre.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ merklePre.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)

/-- The post-compression seed: the dumped post layouts. -/
def merkleSeedPost : List Query :=
  merklePost.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ merklePost.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)

-- Pre-compression: projected CS equals the dumped fixture.
#guard projectCS merkleSeed merkleCS == merklePre

-- Post-compression: the Rust-dumped selector-compression map, applied mechanically,
-- yields exactly the dumped post-compression CS.
#guard projectCSPostMap merkleSeedPost merkleSelMap merkleCS == merklePost

end Halo2.Fixtures.Test
