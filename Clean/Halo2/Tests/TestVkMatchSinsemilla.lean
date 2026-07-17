import Clean.Halo2.Fixtures.Project
import Clean.Halo2.Fixtures.SinsemillaPre
import Clean.Halo2.Fixtures.SinsemillaPost
import Clean.Halo2.Fixtures.SinsemillaSelMap
import Clean.Ironwood.Sinsemilla.HashPieceRound
import Clean.Ironwood.Utilities.LookupRangeCheck

/-!
# VK-match test: the Sinsemilla chip (`SinsemillaConfig`) — first lookup-table target

Runs the ported Sinsemilla configure-chain on the same columns the Rust harness uses
(`halo2_gadgets/src/sinsemilla/dump.rs::register_prereqs` — the orchard `merkle_config_1`
prerequisite sequence), projects the resulting `ConstraintSystem` to the ironwood
`CsFixture`, and checks it **equal** to the fixtures dumped from the actual Rust circuit —
BOTH phases:

* `sinsemillaPre` — pre-selector-compression: 4 gates (range-check bitshift, `Initial y_Q`,
  the Sinsemilla secant + y-check), 13 advice queries, 6 fixed queries, and TWO lookups
  (the running-sum range check and the 3-tuple generator-table lookup — the first
  multi-column lookup in the Halo2-Clean pipeline).
* `sinsemillaPost` — post-`compress_selectors` with the REAL packing gathered from one
  actual `hash_to_point` synthesize (`Value::unknown()`, k=11): all 5 selectors get their
  own packed column (`sinsemillaSelMap`), applied mechanically via `projectCSPostMap`.

The chain (fixture header, in registration order):

1. 10 advice columns; the `constants` fixed column with `enable_constant` (fixed 0);
   `fixed_y_q` (fixed 1); the three generator-table `lookup_table_column`s (fixed 2/3/4);
2. `LookupRangeCheck.configure 10 (advices 9) tableIdx` — the range-check lookup + the
   bitshift gate + selectors 0-2;
3. `SinsemillaChip::configure (advices 0..5) (advices 6) fixed_y_q lookup range_check
   false` — equality on the five hash advices, `q_s1` (selector 3, complex), `q_s2`
   (fixed 5, allocated inside), `q_s4` (selector 4), the generator lookup, then the
   `Initial y_Q` and `Sinsemilla` gates.

The generator-chain constant baked into the lookup input ASTs is `S(0)`
(`SINSEMILLA_S[0]`); the test `Generators` pins exactly that point (the rest of the table
is Layout-fixture territory: fixed-column contents).

The comparison is `#guard` on `DecidableEq CsFixture`.
-/

namespace Halo2.Fixtures.Test

open Ironwood (Fp)
open Orchard.Specs.Sinsemilla (Generators)
open Ironwood.Sinsemilla (GeneratorTableConfig)
open Ironwood.Sinsemilla.HashPiece (Config configure)

/-- The dumped `S(0)` (Rust `SINSEMILLA_S[0]`), pinned from the fixture's lookup constants. -/
def sinsemillaS0 : Orchard.Point Fp :=
  { x := mkFp 6526256343580731999 2999498162208400053 1455178258206882939 987732578029543183,
    y := mkFp 1712018179792725123 10685357584973937153 11290355119345096144 3391000250449829916 }

theorem sinsemillaS0_onCurve : sinsemillaS0.OnCurve := by
  show sinsemillaS0.y ^ 2 = sinsemillaS0.x ^ 3 + Orchard.pallasB
  decide

/-- A `Generators` whose `S 0` is the dumped point — configure only bakes `S 0` into the
lookup input ASTs, so this pins exactly the VK-relevant content. -/
def sinsemillaTestG : Generators where
  S _ := sinsemillaS0
  S_onCurve _ := sinsemillaS0_onCurve

/-- The Sinsemilla configure chain on fresh columns, mirroring the Rust
`register_prereqs` + `SinsemillaChip::configure` harness. Allocating in the monad advances
the CS counters exactly as the harness does; `advices[5]`, `advices[7]`, `advices[8]` are
allocated but unused (orchard reserves them for other chips). -/
def sinsemillaProgram : Configure Fp Config := do
  let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
  let a3 ← adviceColumn; let a4 ← adviceColumn; let _a5 ← adviceColumn
  let a6 ← adviceColumn; let _a7 ← adviceColumn; let _a8 ← adviceColumn
  let a9 ← adviceColumn
  -- shared constants column (fixed 0) with enable_constant
  let constants ← fixedColumn
  enableConstant constants
  -- fixed_y_q (fixed 1)
  let fixedYQ ← fixedColumn
  -- the generator table columns (fixed 2/3/4)
  let t0 ← lookupTableColumn
  let t1 ← lookupTableColumn
  let t2 ← lookupTableColumn
  -- range_check on advices[9] against table_idx
  let _lookupConfig ← Ironwood.LookupRangeCheck.configure 10 a9 t0
  -- the real SinsemillaChip::configure: advices[0..5], witness_pieces = advices[6]
  configure sinsemillaTestG a0 a1 a2 a3 a4 a6 fixedYQ
    { tableIdx := t0, tableX := t1, tableY := t2 }

def sinsemillaCS : ConstraintSystem Fp := (sinsemillaProgram {}).2

/-- The whole-chain registration-order query seed (see `TestVkMatchMul.mulSeed`): the
dumped layouts ARE the deduplicated first-encounter order per query kind. -/
def sinsemillaSeed : List Query :=
  sinsemillaPre.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ sinsemillaPre.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)

/-- The post-compression seed: the dumped post layouts. -/
def sinsemillaSeedPost : List Query :=
  sinsemillaPost.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ sinsemillaPost.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)

-- Pre-compression: projected CS equals the dumped fixture.
#guard projectCS sinsemillaSeed sinsemillaCS == sinsemillaPre

-- Post-compression: the Rust-dumped selector-compression map, applied mechanically,
-- yields exactly the dumped post-compression CS.
#guard projectCSPostMap sinsemillaSeedPost sinsemillaSelMap sinsemillaCS == sinsemillaPost

end Halo2.Fixtures.Test
