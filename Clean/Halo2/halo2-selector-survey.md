# Selector usage survey (halo2_gadgets 0.5.0 + orchard feat/ironwood)

Exhaustive survey of every `create_gate` and `meta.lookup` in halo2_gadgets 0.5.0 and
orchard `feat/ironwood` (commit `840cd68`), to validate the gate model in
`Configure.lean`/`Operations.lean`. Bottom line: **all 13 orchard gates and all but one
halo2_gadgets gate use `Constraints::with_selector` with a single simple `Selector` as
the outer guard**; genuine `Selector`s never appear inside another gate's polynomial.
The exceptions and near-exceptions, with model impact:

## Gates

1. **Inner witness guards** (7+ gates: `note_commit.rs` g_d/pk_d/rho/psi/y-canon,
   `commit_ivk.rs`, `mul_fixed/base_field_elem.rs`): shape
   `q * (b * poly)` where `b` is an *advice bit* boolean-constrained by the same gate
   ("MSB = 1 ⇒ canonicity" pattern). No model impact: the inner guard is part of the
   constraint polynomial; the conditional meaning belongs to the gate's `Spec`.

2. **Fixed-column pseudo-selector** (`sinsemilla/chip.rs:97,243`,
   `generator_table.rs:46`): `q_sinsemilla2 : Column<Fixed>` is a documented
   "non-binary selector"; `q_s3 = q_s2·(q_s2−1)` appears *inside* the "Sinsemilla gate"
   polynomial (guarded by simple-… actually complex selector `q_s1`). No model impact
   for gates: fixed queries evaluate through the environment; the per-row `q_s2` values
   are pinned by `assignFixed` operations.

3. **Manual gate construction** (`ecc/chip/witness_point.rs:58`): builds
   `(q_point * x) * curve_eqn` by hand instead of `with_selector`'s
   `q_point * (x * curve_eqn)` — deliberately, for pinned-VK AST compatibility (see the
   Rust code comment). **Model impact**: `Gate` must store the compiled constraints
   *verbatim* (not a guard × unguarded-poly split); the semantics of enabling is
   "compiled polys vanish under `own selector ↦ 1`", which handles both shapes.

4. **Gate reuse via witness neutralization** (`orchard/src/circuit.rs:317,888`): the
   single `q_orchard` gate (4 constraints) is enabled on 1 + 4 rows per action with two
   unrelated meanings — the cross-address rows neutralize 2 of the 4 constraints by
   witnessing constants (`enable_spend = 1` etc.) and reuse `v_old·(root−anchor)` as
   `disableCrossAddress·(old_coord−new_coord)`. No model impact (enabling means exactly
   "these 4 polys vanish here"; call sites prove different specs from the same
   equations) — but **spec-relevant**: `disableCrossAddress` is *not*
   boolean-constrained in-circuit; the algebra works for any nonzero value, and the
   boolean encoding is a public-input convention.

5. **API facts** (halo2_proofs 0.3): `query_selector` takes no rotation; `query_fixed`
   takes **no rotation either** (always current row). Selector rotations are
   impossible; all fixed queries in the pinned CS have rotation 0.

## Lookups — where the real selector arithmetic lives

All non-trivial selector arithmetic is in `meta.lookup` input expressions, over
**complex** selectors:

- `utilities/lookup_range_check.rs:334`:
  `q_lookup · (q_running · running_sum_word + (1 − q_running) · short_word)`.
- `utilities/lookup_range_check.rs:554` (4/5-bit variant, used via
  `configure_with_tag`): De-Morgan OR `q_range_check = 1 − (1−q_rc4)(1−q_rc5)`, an
  if/else-if chain for `num_bits`, all multiplied by `q_lookup`, feeding **two** lookup
  tuples (value table + tag table).
- `sinsemilla/chip/generator_table.rs:46`: inputs mux against the default table row:
  `q_s1 · x_p + (1 − q_s1) · init_x`, with `q_run = q_s2 − q_s3` (fixed-column
  arithmetic) selecting the running-sum form.

Lookup arguments hold at **every row** (rows with all guards 0 hit the default/zero
table row). Model direction (lookup port, TODO): lookup satisfaction is global over the
activation table; the per-region meaning of enabling the lookup selectors ("my tuple at
this row is in the table") needs a decidable non-interference condition from the
computed layout (no other region enables lookup-relevant selectors on my rows).

## Non-orchard oddities (not needed for ironwood)

- `sha256/table16/spread_table.rs:194`: a lookup with **no selector at all**
  (unconditional on every row).
- sha256 gates build constraints through helper structs rather than textually inside
  `create_gate` (indirection only).
