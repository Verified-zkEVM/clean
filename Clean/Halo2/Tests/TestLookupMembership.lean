import Clean.Ironwood.Utilities.LookupRangeCheck

/-!
Regression pin for `LookupRangeCheck.mem_usableRows_val_lt` (C2a #5): the membership-consumption
helper turns a lookup-membership existential + the `TableLoaded` usable-rows bound into a value
bound in one step. Acceptance-consumed in `LookupRangeCheck.short_range_check` soundness.
-/

namespace Zcash.Circuits.LookupRangeCheck.Test

open Halo2

-- the "two obtains + apply" pattern collapses to one `exact` on the helper.
example {K : ℕ} {cfg : Config K} {env : Environment Fp} {v : Fp}
    (hTableLt : ∀ r : ℕ, r < env.usableRows → (env.fixed cfg.tableIdx.inner (r : ℤ)).val < 2 ^ K)
    (hMem : ∃ tableRow : ℕ, tableRow < env.usableRows
      ∧ v = env.fixed cfg.tableIdx.inner (tableRow : ℤ)) :
    v.val < 2 ^ K :=
  mem_usableRows_val_lt hTableLt hMem

end Zcash.Circuits.LookupRangeCheck.Test
