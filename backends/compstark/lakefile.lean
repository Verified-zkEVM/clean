import Lake
open Lake DSL

/-! The CompStark backend of Clean: a separate package, so that Clean does not depend on
CompStark. Its dependencies' revisions agree with Clean's manifest. -/

package CleanCompStark where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

require Clean from "../.."

-- CompStark's `main`.
require CompStark from git "https://github.com/zksecurity/CompStark" @
  "29aaf95b5cf111f46e8784dbb4f981a56b964aeb"

@[default_target]
lean_lib CleanCompStark

lean_lib CleanCompStarkTests where
  globs := #[.submodules `CleanCompStarkTests]

/-- The keccak-air showcase's evidence against Plonky3 and its benchmark. -/
lean_lib KeccakShowcase where
  moreLeancArgs := #["-march=native"]

lean_exe keccak_showcase where
  root := `KeccakShowcase.Main
  moreLeancArgs := #["-march=native"]
