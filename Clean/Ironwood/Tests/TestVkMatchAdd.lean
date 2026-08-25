import Clean.Ironwood.Fixtures.Project
import Clean.Ironwood.Fixtures.AddPre
import Clean.Ironwood.Fixtures.AddPost
import Clean.Ironwood.Ecc.Add

/-!
# VK-match test: the complete-addition (`add::Config`) gadget

The first end-to-end VK match for Halo2-Clean. Runs the ported `Add.add.configure` on the same
columns the Rust harness used (`advices[0..8]` in the roles
`x_p, y_p, x_qr, y_qr, lambda, alpha, beta, gamma, delta`), projects the resulting
`ConstraintSystem` to the ironwood `CsFixture` shape, and checks it **equal** to the fixture
dumped from the actual Rust circuit (`AddPre.lean` / `AddPost.lean`).

* `addPre`  — pre-selector-compression (gates still carry `.selector 0`).
* `addPost` — post-`compress_selectors` (the single `q_add` selector packed into one new
  fixed column; every `.selector 0` replaced by `.fixed 0`).

The comparison is `#guard` on `DecidableEq CsFixture`, so CI fails on any drift between the
Lean Add port and the Rust constraint system.

This file is part of the small, readable **documentation** suite of the VK-matching
approach — two leaf gadgets, each with both sides: Add (this file + `TestVkLayoutAdd`;
the minimal example) and Mul (`TestVkMatchMul` + `TestVkLayoutMul`; the LOOKUP and
selector-compression example). The check that the real circuit is correct is the
top-level suite: `TestVkMatchAction` (configure, both versions) + `TestVkLayoutAction`
(ironwood synthesize) + `TestVkLayoutActionBase` (pre-ironwood synthesize) — the other
per-gadget tests were subsumed by those and retired (see git history).
-/

namespace Zcash.Circuits.Fixtures.Test

open Halo2
open Ecc.Add (Config add)

/-- Allocate the 9 advice columns (mirroring the Rust harness's `EccConfig`-minimal column
allocation: `advices[0..9]` via `meta.advice_column()`), then run `Add.add.configure` on them.
Allocating in the monad — rather than passing bare `⟨0⟩..⟨8⟩` — is what advances the CS's
`numAdviceColumns` counter to 9, matching the harness. -/
def addProgram : Configure Fp Config := do
  let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
  let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
  let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
  add.configure (a0, a1, a2, a3, a4, a5, a6, a7, a8)

def addCS : ConstraintSystem Fp := (addProgram {}).2

-- Pre-compression: projected CS (query layouts from the configure-recorded queries)
-- equals the dumped fixture.
#guard projectCS addCS == addPre

-- Post-compression: projected CS equals the dumped fixture.
#guard projectCSPost addCS == addPost

end Zcash.Circuits.Fixtures.Test
