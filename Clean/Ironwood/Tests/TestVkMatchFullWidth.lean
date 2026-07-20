import Clean.Ironwood.Fixtures.Project
import Clean.Ironwood.Fixtures.FullWidthPre
import Clean.Ironwood.Fixtures.FullWidthPost
import Clean.Ironwood.Fixtures.FullWidthSelMap
import Clean.Ironwood.Ecc.MulFixed.FullWidth

/-!
# VK-match test (CS): full-width fixed-base scalar mul

The `TestVkMatchMul` counterpart for the `mul_fixed` wrapper: runs the same configure
chain as the Rust dump circuit (and as `TestVkLayoutFullWidth`), projects the resulting
`ConstraintSystem` to `CsFixture`, and checks it equal to the fixtures dumped from the
actual Rust circuit — both pre-compression (gates carry `.selector`) and
post-`compress_selectors` (the dumped selector map applied mechanically via
`projectCSPostMap`).

`#guard` equality is fine (D1).
-/

namespace Halo2.Ironwood.Fixtures.Test.MatchFullWidth

open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Ecc.MulFixed.FullWidth (Config configure)

/-- The configure chain, exactly as in the layout test / Rust dump circuit. -/
def program : Configure Fp Config := do
    let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
    let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
    let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
    let _a9 ← adviceColumn
    let l0 ← fixedColumn; let l1 ← fixedColumn; let l2 ← fixedColumn
    let l3 ← fixedColumn; let l4 ← fixedColumn; let l5 ← fixedColumn
    let l6 ← fixedColumn; let l7 ← fixedColumn
    let constants ← fixedColumn
    enableConstant constants
    let addIncompleteConfig ← Ironwood.Ecc.AddIncomplete.add.configure (a0, a1, a2, a3)
    let addConfig ← Ironwood.Ecc.Add.add.configure (a0, a1, a2, a3, a4, a5, a6, a7, a8)
    let mulFixedConfig ← Ironwood.Ecc.MulFixed.configure
      ![l0, l1, l2, l3, l4, l5, l6, l7] a4 a5 addConfig addIncompleteConfig
    configure mulFixedConfig

def fullWidthCS : ConstraintSystem Fp := (program {}).2

/-- Registration-order query seed from the dumped pre layouts. -/
def seed : List Query :=
  fullWidthPre.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ fullWidthPre.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)

/-- The post-compression seed from the dumped post layouts. -/
def seedPost : List Query :=
  fullWidthPost.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ fullWidthPost.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)

-- Pre-compression: projected CS equals the dumped fixture.
#guard projectCS seed fullWidthCS == fullWidthPre

-- Post-compression: the Rust-dumped selector map, applied mechanically, yields exactly
-- the dumped post-compression CS.
#guard projectCSPostMap seedPost fullWidthSelMap fullWidthCS == fullWidthPost

end Halo2.Ironwood.Fixtures.Test.MatchFullWidth
