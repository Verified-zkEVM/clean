import Clean.Ironwood.Fixtures.FixtureTypes
import Clean.Halo2.Keygen

/-!
# `projectCS` — Halo2-Clean `ConstraintSystem` → `CsFixture`

Thin wrappers over the Clean-core keygen projection (`Clean.Halo2.Keygen.Projection`),
building the `CsFixture` shape the VK-match tests compare for **equality** against the
Rust dumps (`AddPre.lean` / `AddPost.lean` / `actionPre.json` / …):

* `projectCS` — the **pre-compression** view: run the query walk over the flat gates from
  the configure-recorded query layouts, leaving each simple selector erased as `.selector`.
* `projectCSPost` — the **post-compression, single-selector** view: substitute the one
  selector by its packed fixed column (bare query), then run the walk.
* `projectCSPostMap` — the **post-compression, map-driven** view: exactly the core
  `Halo2.projectCS` (selector substitution by the root-finding replacements, then the seeded
  walk). The map's derivation stays Rust-side (trust boundary); Lean applies it mechanically
  and the resulting CS is checked EQUAL to the dumped post-compression fixture.
-/

namespace Zcash.Circuits.Fixtures

open Halo2

/-- Project a Halo2-Clean `ConstraintSystem` (pre-compression) into the `CsFixture`:
flatten gates, run the query walk + erasure starting from the configure-recorded query
layouts, erase the lookups, read the counts. Simple selectors survive as `.selector`. -/
def projectCS (cs : ConstraintSystem Fp) : CsFixture :=
  let queries := recordedQueries cs
  { numAdviceColumns := cs.numAdviceColumns
    numFixedColumns := cs.numFixedColumns
    numInstanceColumns := cs.numInstanceColumns
    numSelectors := cs.numSelectors
    adviceQueryLayout := queries.advice.toList
    fixedQueryLayout := queries.fixed.toList
    instanceQueryLayout := queries.inst.toList
    gates := eraseGates (flatGates cs) queries
    lookups := eraseLookups cs.lookups queries }

/-! ## Post-compression projection (single-selector gadget)

For a gadget with `numSelectors = 1` simple selector active in its gate, `compress_selectors`
packs it into one new fixed column with `combination_len = 1`, `assigned_root = 1`, so the
replacement expression is the *bare* fixed query on the new column. The new fixed column index
is `numFixedColumns`, and its query is registered at column-allocation time inside
`compress_selectors` (`circuit.rs:1267-1274`) — appended after the configure-recorded fixed
queries, before the substituted gates are walked. -/

/-- Substitute a single simple selector by a fixed query on the packed column `packedCol`,
rotation 0 (the `combination_len = 1` replacement). Leaves everything else untouched. -/
def substSelector (packedCol : ℕ) : Expression Fp Query → Expression Fp Query
  | .var (.selector _) => .var (.fixed ⟨packedCol⟩ 0)
  | .var q => .var q
  | .const c => .const c
  | .add a b => .add (substSelector packedCol a) (substSelector packedCol b)
  | .mul a b => .mul (substSelector packedCol a) (substSelector packedCol b)

/-- Project the post-compression CS for a **single-selector** gadget: substitute the
selector by the packed fixed column (index = old `numFixedColumns`), grow `numFixedColumns`
by 1, then run the same walk seeded with the packed column's fixed query. -/
def projectCSPost (cs : ConstraintSystem Fp) : CsFixture :=
  let packedCol := cs.numFixedColumns
  let polys := (flatGates cs).map (substSelector packedCol)
  let queries := (recordedQueries cs).registerFixed packedCol
  { numAdviceColumns := cs.numAdviceColumns
    numFixedColumns := cs.numFixedColumns + 1
    numInstanceColumns := cs.numInstanceColumns
    numSelectors := cs.numSelectors
    adviceQueryLayout := queries.advice.toList
    fixedQueryLayout := queries.fixed.toList
    instanceQueryLayout := queries.inst.toList
    gates := eraseGates polys queries }

/-- Project the post-compression CS with a Rust-dumped selector-compression map — exactly
the Clean-core `Halo2.projectCS`: substitute every selector (in gates and lookups) by its
root-finding replacement, grow `numFixedColumns` by the new packed columns, and run the
seeded query walk. -/
def projectCSPostMap (map : SelCompressMap) (cs : ConstraintSystem Fp) : CsFixture :=
  Halo2.projectCS map cs

end Zcash.Circuits.Fixtures
