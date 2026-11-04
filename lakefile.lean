import Lake
open Lake DSL

package Clean where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    -- Preserve the source-level mutable-loop representation used by Halo2 proofs.
    ⟨`backward.do.legacy, true⟩,
    -- Match the implicit-argument unification used to elaborate the preserved branch.
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib Clean where

lean_lib Zcash where
  roots := #[`Clean.Ironwood]

lean_lib Orchard where
  roots := #[`Clean.Orchard]

lean_lib CleanTests where
  roots := #[`Clean.Test, `Clean.Specs.BLAKE3.ChunkProcessingTests]

-- Public Lean 4.35 compatibility port of daira/CompElliptic.
require CompElliptic from git
  "https://github.com/zksecurity/compelliptic-lean4-35.git" @ "f26a235f2f647b10fe63bc4ec4c7ee394b3c8f43"

-- mathlib LAST so its pinned toolchain-matched versions of the common transitive
-- dependencies (batteries, aesop, Qq, proofwidgets, ...) take precedence.
require CompPoly from git "https://github.com/Verified-zkEVM/CompPoly.git" @ "v4.35.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"
