import Clean.Halo2.Fixtures.Project
import Clean.Halo2.Fixtures.AddPre
import Clean.Halo2.Fixtures.AddPost
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
-/

namespace Halo2.Fixtures.Test

open Ironwood (Fp)
open Ironwood.Ecc

/-- Allocate the 9 advice columns (mirroring the Rust harness's `EccConfig`-minimal column
allocation: `advices[0..9]` via `meta.advice_column()`), then run `Add.add.configure` on them.
Allocating in the monad — rather than passing bare `⟨0⟩..⟨8⟩` — is what advances the CS's
`numAdviceColumns` counter to 9, matching the harness. -/
def addProgram : Configure Fp Add.Config := do
  let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
  let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
  let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
  Ironwood.Ecc.Add.add.configure (a0, a1, a2, a3, a4, a5, a6, a7, a8)

def addCS : ConstraintSystem Fp := (addProgram {}).2

/-- The Add gate's queried cells in halo2 declaration order (the closure's `let` sequence,
`add.rs`): `x_p, y_p, x_q, y_q, x_r, y_r, λ, α, β, γ, δ` on advice columns `0..8`, with
`x_r, y_r` at `Rotation::next()` on columns `2, 3`. This is halo2's `Gate::queried_cells`;
it seeds the query-index walk so the projected layout and gate indices match Rust. -/
def addSeed : List Query :=
  [ .advice ⟨0⟩ 0, .advice ⟨1⟩ 0, .advice ⟨2⟩ 0, .advice ⟨3⟩ 0,
    .advice ⟨2⟩ 1, .advice ⟨3⟩ 1,
    .advice ⟨4⟩ 0, .advice ⟨5⟩ 0, .advice ⟨6⟩ 0, .advice ⟨7⟩ 0, .advice ⟨8⟩ 0 ]

-- Pre-compression: projected CS equals the dumped fixture.
#guard projectCS addSeed addCS == addPre

-- Post-compression: projected CS equals the dumped fixture.
#guard projectCSPost addSeed addCS == addPost

end Halo2.Fixtures.Test
