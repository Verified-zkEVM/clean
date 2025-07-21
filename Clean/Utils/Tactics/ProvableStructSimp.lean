import Clean.Utils.Tactics.SplitProvableStructEq
import Clean.Utils.Tactics.DecomposeProvableStruct
import Clean.Utils.Tactics.SimplifyProvableStructEval

/--
  Simplify all provable struct expressions by repeatedly applying:
  1. `split_provable_struct_eq` - splits struct equalities into field-wise equalities
  2. `decompose_provable_struct` - destructures struct variables that appear in projections
  3. `simplify_provable_struct_eval` - simplifies eval expressions in equalities with struct literals

  The tactic continues until no transformation makes any more progress.

  This is useful for normalizing goal states involving structures with ProvableStruct instances,
  as it automatically:
  - Splits equalities like `s1 = s2` into `s1.f1 = s2.f1 ∧ s1.f2 = s2.f2 ∧ ...` if some components of `s1` or `s2` are explicitly mentioned
  - Destructures variables like `input` that appear in projections like `input.x` to expose components
  - Simplifies `eval env var = struct_literal` to expose components
  - Handles these transformations even inside conjunctions

  Example:
  ```lean
  theorem example (a b : MyStruct F) (h : a = b ∧ a.x = 5) : b.x = 5 := by
    provable_struct_simp
    -- Now a and b are destructured, and h.1 is split into field equalities
    -- The proof becomes straightforward
    sorry
  ```
-/
macro "provable_struct_simp" : tactic =>
  `(tactic|
    repeat (
      fail_if_no_progress (
      try split_provable_struct_eq;
      try decompose_provable_struct;
      try simplify_provable_struct_eval;
      try simp only [] at *
      )
    )
  )
