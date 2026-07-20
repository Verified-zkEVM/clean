import Clean.Ironwood.Fixtures.Project
import Clean.Ironwood.Fixtures.ActionSelMap
import Clean.Ironwood.Fixtures.Json
import Clean.Ironwood.Specs.SinsemillaGenerators
import Clean.Ironwood.Action.Circuit

/-!
# VK-match test: the full Orchard Action circuit `configure`

Projects the `ConstraintSystem` produced by the ported `Action.Circuit.configure` to the
ironwood `CsFixture` shape and checks it EQUAL to the fixtures dumped from the actual
Rust circuit — both pre-compression (`actionPre.json`) and, via the Rust-dumped selector
map applied mechanically, post-`compress_selectors` (`actionPost.json`). `configure` is
version-independent (post-NU 6.2 and 6.3 share the CS), so this single test covers both
top-level circuits.

The fixtures are JSON data files loaded at `#eval` time (see `Fixtures/Json.lean` for
the codec, the pinned-content-hash scheme, and why the data is not a Lean term); a
mismatch or failed load is a build failure, exactly like the former `#guard`s.
-/

namespace Halo2.Ironwood.Fixtures.Test.MatchAction

open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Fixtures.Json

def actionCS : ConstraintSystem Fp :=
  (Halo2.Ironwood.Action.Circuit.configure Halo2.Ironwood.Specs.Sinsemilla.orchardGenerators {}).2

/-- Registration-order query seed from a dumped fixture's query layouts. -/
def seedOf (f : CsFixture) : List Query :=
  f.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ f.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)
    ++ f.instanceQueryLayout.map (fun (c, r) => Query.instance ⟨c⟩ r)

#eval show IO Unit from do
  let actionPre ← loadCsFixture "Clean/Ironwood/Fixtures/actionPre.json" 0x31656840fdb3156d
  let actionPost ← loadCsFixture "Clean/Ironwood/Fixtures/actionPost.json" 0xdb884f3c3174a41b
  runChecks [
    -- Pre-compression: projected CS equals the dumped fixture.
    ("actionPre: projected CS = dump", projectCS (seedOf actionPre) actionCS == actionPre),
    -- Post-compression: the Rust-dumped selector map, applied mechanically, yields
    -- exactly the dumped post-compression CS.
    ("actionPost: projected CS = dump",
      projectCSPostMap (seedOf actionPost) actionSelMap actionCS == actionPost)]

end Halo2.Ironwood.Fixtures.Test.MatchAction
