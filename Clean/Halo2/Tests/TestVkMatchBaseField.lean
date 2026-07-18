import Clean.Halo2.Fixtures.Project
import Clean.Halo2.Fixtures.BaseFieldPre
import Clean.Halo2.Fixtures.BaseFieldPost
import Clean.Halo2.Fixtures.BaseFieldSelMap
import Clean.Ironwood.Ecc.MulFixed.BaseFieldElem

/-!
# VK-match test (CS): fixed-base mul by a base-field element

The `TestVkMatchMul` counterpart for the `mul_fixed` wrapper: runs the same configure
chain as the Rust dump circuit (and as `TestVkLayoutBaseField`), projects the resulting
`ConstraintSystem` to `CsFixture`, and checks it equal to the fixtures dumped from the
actual Rust circuit — both pre-compression (gates carry `.selector`) and
post-`compress_selectors` (the dumped selector map applied mechanically via
`projectCSPostMap`).

`#guard` equality is fine (D1).
-/

namespace Halo2.Fixtures.Test.MatchBaseField

open Halo2.Ironwood (Fp)
open Halo2.Ironwood.Ecc.MulFixed.BaseFieldElem (Config configure)

/-- The configure chain, exactly as in the layout test / Rust dump circuit. -/
def program : Configure Fp Config := do
    let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
    let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
    let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
    let a9 ← adviceColumn
    let tableIdx ← lookupTableColumn
    let l0 ← fixedColumn; let l1 ← fixedColumn; let l2 ← fixedColumn
    let l3 ← fixedColumn; let l4 ← fixedColumn; let l5 ← fixedColumn
    let l6 ← fixedColumn; let l7 ← fixedColumn
    let constants ← fixedColumn
    enableConstant constants
    let _advices : Fin 10 → Column .advice := ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
    let lookupConfig ← Ironwood.LookupRangeCheck.configure 10 a9 tableIdx
    let addIncompleteConfig ← Ironwood.Ecc.AddIncomplete.add.configure (a0, a1, a2, a3)
    let addConfig ← Ironwood.Ecc.Add.add.configure (a0, a1, a2, a3, a4, a5, a6, a7, a8)
    let mulFixedConfig ← Ironwood.Ecc.MulFixed.configure
      ![l0, l1, l2, l3, l4, l5, l6, l7] a4 a5 addConfig addIncompleteConfig
    configure ![a6, a7, a8] lookupConfig mulFixedConfig

def baseFieldCS : ConstraintSystem Fp := (program {}).2

/-- Registration-order query seed from the dumped pre layouts. -/
def seed : List Query :=
  baseFieldPre.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ baseFieldPre.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)

/-- The post-compression seed from the dumped post layouts. -/
def seedPost : List Query :=
  baseFieldPost.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ baseFieldPost.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)

-- Pre-compression: projected CS equals the dumped fixture.
#guard projectCS seed baseFieldCS == baseFieldPre

-- Post-compression: the Rust-dumped selector map, applied mechanically, yields exactly
-- the dumped post-compression CS.
#guard projectCSPostMap seedPost baseFieldSelMap baseFieldCS == baseFieldPost

end Halo2.Fixtures.Test.MatchBaseField
