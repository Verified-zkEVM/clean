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
  "8c47e952621cb8ffb5c7430ccf7fae054accc7e1"

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
