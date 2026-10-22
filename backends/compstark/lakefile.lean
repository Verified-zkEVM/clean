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
  "50708f587c543e98903b191fc565deeac5a6cabc"

@[default_target]
lean_lib CleanCompStark

lean_lib CleanCompStarkTests where
  globs := #[.submodules `CleanCompStarkTests]
