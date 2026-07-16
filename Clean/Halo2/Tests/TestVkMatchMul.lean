import Clean.Halo2.Fixtures.Project
import Clean.Halo2.Fixtures.MulPre
import Clean.Halo2.Fixtures.MulPost
import Clean.Halo2.Fixtures.MulSelMap
import Clean.Ironwood.Ecc.Mul

/-!
# VK-match test: variable-base scalar multiplication (`mul::Config`) — the flagship

Runs the ported mul configure-chain on the same columns the Rust harness uses
(`configure_mul` in `halo2_gadgets/src/ecc/chip/dump.rs`), projects the resulting
`ConstraintSystem` to the ironwood `CsFixture`, and checks it **equal** to the fixtures
dumped from the actual Rust circuit — BOTH phases:

* `mulPre` — pre-selector-compression (gates carry `.selector`): 45 gates (range-check
  bitshift, complete addition, hi/lo incomplete rounds, complete-decompose, overflow, LSB),
  24 advice queries, 2 fixed queries (constants + table), and the range-check LOOKUP (the
  first lookup in the Halo2-Clean pipeline).
* `mulPost` — post-`compress_selectors`, with the REAL packing: the Rust harness circuit
  (`MulDumpCircuit`) runs one actual mul synthesize (witnessed base point × witnessed
  scalar, `Value::unknown()` — keygen's view) through the floor planner at `k = 11` to
  gather the true per-selector activation table; `compress_selectors` on that table packs
  the 13 selectors into **7 new fixed columns** (q_lookup, q_running: own columns, degree-0;
  q_add and q_mul_overflow: own columns, degree budget; the remaining 8 simple selectors:
  three 3-member combinations). Lean applies the dumped map (`mulSelMap`) mechanically via
  `projectCSPostMap` — the map's derivation stays Rust-side (trust boundary, see
  `Project.lean` / `FixtureTypes.lean`), and this equality check validates the applied
  result byte-for-byte.

The mul-relevant configure chain (mirroring the subsequence of `EccChip::configure` that
mul consumes) is, in registration order:

1. 10 advice columns; the lookup table column (fixed 0); the `constants` column (fixed 1)
   with `enable_constant` (`ecc.rs:833-834` — needed by mul's `z_init = 0`
   `assign_advice_from_constant`, and its `enable_equality` registers fixed query 0);
2. `LookupRangeCheck.configure 10 (advices 9) tableIdx` — the range-check lookup argument
   + the "Short lookup bitshift" gate + 3 selectors (q_lookup, q_running complex;
   q_bitshift simple);
3. `Add.add.configure (advices 0..8)` — the complete-addition gate + `q_add`;
4. `Mul.configure add lookup advices` — hi/lo incomplete gates, complete-decompose gate,
   overflow gate, LSB gate + their selectors.

The comparison is `#guard` on `DecidableEq CsFixture` (D1: `#eval`-equality is fine).
-/

namespace Halo2.Fixtures.Test

open Ironwood (Fp)
open Ironwood.Ecc.Add (add)
open Ironwood.Ecc.Mul (Config configure)

/-- The mul configure chain on fresh columns, mirroring the Rust `configure_mul` harness:
allocate 10 advice columns, the lookup table column and the constants column
(`enableConstant`), then configure range-check, add and mul in that order (the mul-relevant
subsequence of `EccChip::configure`). Allocating in the monad advances the CS counters
exactly as the harness does. -/
def mulProgram : Configure Fp Config := do
  let a0 ← adviceColumn; let a1 ← adviceColumn; let a2 ← adviceColumn
  let a3 ← adviceColumn; let a4 ← adviceColumn; let a5 ← adviceColumn
  let a6 ← adviceColumn; let a7 ← adviceColumn; let a8 ← adviceColumn
  let a9 ← adviceColumn
  let tableIdx ← lookupTableColumn
  -- shared constants column (ecc.rs:833-834; mul's z_init needs it)
  let constants ← fixedColumn
  enableConstant constants
  let advices : Fin 10 → Column .advice :=
    ![a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  -- range_check first (ecc.rs:836), on advices[9]
  let lookupConfig ← Ironwood.LookupRangeCheck.configure 10 a9 tableIdx
  -- add before mul (EccChip::configure order), on advices[0..8]
  let addConfig ← add.configure (a0, a1, a2, a3, a4, a5, a6, a7, a8)
  -- the mul chain
  configure addConfig lookupConfig advices

def mulCS : ConstraintSystem Fp := (mulProgram {}).2

/-- The whole-chain registration-order query seed (halo2 `queried_cells` across every gate
and lookup closure — and `enable_equality`/`enable_constant`, which also register rot-0
queries via `query_any_index` — in configure-call order). Built from the dumped layouts:
the Rust dump's `{advice,fixed}QueryLayout` ARE the deduplicated first-encounter order per
query kind, so seeding with them reproduces the exact layouts and isolates any gate/lookup
AST mismatch. (Advice and fixed live in independent index spaces, so seeding each kind in
its own order is faithful.) -/
def mulSeed : List Query :=
  mulPre.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ mulPre.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)

/-- The post-compression seed: the dumped post layouts (= pre layouts ++ the packed columns'
rot-0 fixed queries, registered at column-allocation time inside `compress_selectors`). -/
def mulSeedPost : List Query :=
  mulPost.adviceQueryLayout.map (fun (c, r) => Query.advice ⟨c⟩ r)
    ++ mulPost.fixedQueryLayout.map (fun (c, r) => Query.fixed ⟨c⟩ r)

-- Pre-compression: projected CS equals the dumped fixture.
#guard projectCS mulSeed mulCS == mulPre

-- Post-compression: the Rust-dumped selector-compression map, applied mechanically,
-- yields exactly the dumped post-compression CS.
#guard projectCSPostMap mulSeedPost mulSelMap mulCS == mulPost

end Halo2.Fixtures.Test
