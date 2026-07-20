import Lake
open Lake DSL

package Clean where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Clean where

lean_lib CleanTests where
  roots := #[`Clean.Test, `Clean.Specs.BLAKE3.ChunkProcessingTests]

-- The shared elliptic-curve/finite-field theory used by Clean/Ironwood and by
-- zcash/ironwood (which pins the same revision) — replacing the formerly vendored
-- Clean/Ironwood/Specs/CompElliptic+CompPoly copies. Brings CompPoly transitively.
require CompElliptic from git
  "https://github.com/daira/CompElliptic" @ "f5f420f4b090b9f65be398d82ad29cfd96710aa3"

-- mathlib LAST so its pinned toolchain-matched versions of the common transitive
-- dependencies (batteries, aesop, Qq, proofwidgets, ...) take precedence.
require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.30.0"
