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
  "c774b83f82f81d002981c70c6207ac8de4c3fde7"

@[default_target]
lean_lib CleanCompStark

lean_lib CleanCompStarkTests where
  globs := #[.submodules `CleanCompStarkTests]
