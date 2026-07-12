import Clean.Halo2.Fixtures.Project
import Clean.Halo2.Fixtures.MulPre
import Clean.Ironwood.Ecc.Mul

/-!
# VK-match test: variable-base scalar multiplication (`mul::Config`) — the flagship

Runs the ported mul configure-chain on the same columns the Rust harness uses
(`configure_mul` in `halo2_gadgets/src/ecc/chip/dump.rs`), projects the resulting
`ConstraintSystem` to the ironwood `CsFixture`, and checks it **equal** to the fixture
dumped from the actual Rust circuit (`MulPre.lean` / `MulPost.lean`).

The mul-relevant configure chain (mirroring the subsequence of `EccChip::configure` that
mul consumes) is, in registration order:

1. 10 advice columns + the lookup table column (fixed col 0);
2. `LookupRangeCheck.configure 10 (advices 9) tableIdx` — the range-check lookup argument
   (the first lookup in the pipeline) + the "Short lookup bitshift" gate + 3 selectors
   (q_lookup, q_running complex; q_bitshift simple);
3. `Add.configure (advices 0..8)` — the complete-addition gate + `q_add`;
4. `Mul.configure add lookup advices` — hi/lo incomplete gates, complete-decompose gate,
   overflow gate, LSB gate + their selectors.

`mulPre` is pre-selector-compression (gates carry `.selector`). This is the flagship
pre-compression VK match: 45 gates (range-check bitshift, complete addition, hi/lo
incomplete rounds, complete-decompose, overflow, LSB), 24 advice queries, 1 fixed query, and
the range-check LOOKUP (the first lookup in the Halo2-Clean pipeline) — all matched **equal**
to the Rust dump.

**Post-compression** is scaffolded but NOT asserted here: a faithful `compress_selectors`
result for the multi-selector mul chain needs the real per-selector activation table from a
`synthesize` run (see `Project.lean`'s post-compression scaffolding — `SelCompress`,
`selReplacement`, `substSelectorMap`, and the trust-boundary note). The dumped `MulPost.lean`
uses a single-row placeholder activation under which no selectors pack, so it is a shape
placeholder, not the authoritative VK; it is intentionally not `#guard`ed.

The comparison is `#guard` on `DecidableEq CsFixture` (D1: `#eval`-equality is fine).
-/

namespace Halo2.Fixtures.Test

open _root_.Halo2
open _root_.Halo2.Ironwood (Fp)
open _root_.Halo2.Ironwood.Ecc
open _root_.Halo2.Ironwood
open Halo2.Fixtures

/-- The mul configure chain on fresh columns, mirroring the Rust `configure_mul` harness:
allocate 10 advice columns and the lookup table column, then configure range-check, add and
mul in that order (the mul-relevant subsequence of `EccChip::configure`). Allocating in the
monad advances the CS counters exactly as the harness does. -/
def mulProgram : Configure Fp Mul.Config := do
  let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
  let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
  let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
  let a9 ← adviceColumn
  let tableIdx ← lookupTableColumn
  let advices : Fin 10 → Column .advice :=
    ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  -- range_check first (ecc.rs:836), on advices[9]
  let lookupConfig ← LookupRangeCheck.configure 10 a9 tableIdx
  -- add before mul (EccChip::configure order), on advices[0..8]
  let addConfig ← Add.configure a0 a1 a2 a3 a4 a5 a6 a7 a8
  -- the mul chain
  Mul.configure addConfig lookupConfig advices

def mulCS : _root_.Halo2.ConstraintSystem Fp := (mulProgram {}).2

/-- The whole-chain registration-order query seed (halo2 `queried_cells` across every gate
and lookup closure, in configure-call order). Built from the dumped layouts: the Rust dump's
`{advice,fixed}QueryLayout` ARE the deduplicated first-encounter order per query kind, so
seeding with them reproduces the exact layouts and isolates any gate/lookup AST mismatch.
(Advice and fixed live in independent index spaces, so seeding each kind in its own order
is faithful.) -/
def mulSeed : List Query :=
  mulPre.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ mulPre.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)

-- Diagnostic: show the projection so a mismatch localises the first differing gate.
-- #eval projectCS mulSeed mulCS

-- Pre-compression: projected CS equals the dumped fixture.
#guard projectCS mulSeed mulCS == mulPre

end Halo2.Fixtures.Test
