import Lake
open Lake DSL

package Clean where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Clean where

lean_lib Zcash where
  roots := #[`Clean.Ironwood]

lean_lib Orchard where
  roots := #[`Clean.Orchard]

lean_lib CleanTests where
  roots := #[`Clean.Test, `Clean.Specs.BLAKE3.ChunkProcessingTests]

-- The proof roots, plus every module under Midnight.
lean_lib Midnight where
  roots := #[`Midnight.SHA256.Semantics.Formal, `Midnight.SHA256.WitnessComplete, `Midnight.SHA256.Admission.Certificate]
  globs := #[.submodules `Midnight, .one `Midnight]

-- Lean half of the VK export tool (scripts/vk-export); not a default target.
lean_lib MidnightExport where
  globs := #[.submodules `MidnightExport]

-- Lowering replay fixtures (scripts/lowering-replay), one directory each; not a default target.
lean_lib LoweringFixtures where
  srcDir := "scripts/lowering-replay"
  globs := #[.submodules `LoweringFixtures]

-- ethereum/EthLib at 3bd2b3c, BLAKE2b compression only, vendored with per-file hashes
-- (scripts/ethlib-vendor/vendor.py --check); Midnight's key hash runs on its compression function.
lean_lib EthLib where
  srcDir := "vendor/ethlib"
  roots := #[`EthLib.Cryptography.Hash.Blake2b]

-- Public Lean 4.35 compatibility port of daira/CompElliptic.
require CompElliptic from git
  "https://github.com/zksecurity/compelliptic-lean4-35.git" @ "f26a235f2f647b10fe63bc4ec4c7ee394b3c8f43"

-- mathlib LAST so its pinned toolchain-matched versions of the common transitive
-- dependencies (batteries, aesop, Qq, proofwidgets, ...) take precedence.
require CompPoly from git "https://github.com/Verified-zkEVM/CompPoly.git" @ "v4.35.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"
