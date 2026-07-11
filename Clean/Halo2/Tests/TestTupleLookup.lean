import Clean.Halo2
import Clean.Ironwood.Ecc.Basic

/-!
Regression test for the **3-tuple lookup membership reduction** — the new shape introduced
by the Sinsemilla generator lookup (`Clean/Ironwood/Sinsemilla/HashPiece.lean`), the first
real 3-tuple lookup consumer in Halo2-Clean.

The framework's `enableLookup` constraint semantics (`Clean/Halo2/Operations.lean:164-179`)
compares the *input list* to the *table list* pointwise via `List.map`. For a 3-tuple
`inputs = [i₀, i₁, i₂]`, `tables = [t₀, t₁, t₂]` the membership existential

  `∃ row < usableRows, inputs.map (eval@here) = tables.map (eval@row)`

reduces — by `List.map_cons`/`List.map_nil`/`List.cons.injEq` — to a single shared
`row` witnessing three per-column equalities `i_k@here = t_k@row`. These tests pin that
reduction so the Sinsemilla soundness proof (which peels each generator lookup into a
`(m, S(m).x, S(m).y)` fact) rests on a checked shape.
-/

namespace Halo2.TupleLookup.Test

open Halo2 Halo2.Ironwood

/-- The list-map equality of two 3-element lists splits into three componentwise
equalities — the algebraic core of the 3-tuple membership reduction. -/
example (i0 i1 i2 t0 t1 t2 : Fp) :
    ([i0, i1, i2].map id = [t0, t1, t2].map id) ↔ (i0 = t0 ∧ i1 = t1 ∧ i2 = t2) := by
  simp only [List.map_cons, List.map_nil, List.cons.injEq, id_eq, and_true]

/-- A concrete `enableLookup` constraint for a 3-input / 3-table `LookupArgument` reduces,
under `circuit_norm` + the list-map splitting, to a shared-row existential over three
per-column equalities — the exact shape the Sinsemilla generator lookup is consumed at. -/
example (place : RegionIndex → ℕ) (self : RegionIndex) (env : Environment Fp) (row : ℕ)
    (s : Selector) (i0 i1 i2 : Expression Fp Query) (c0 c1 c2 : Column .fixed) :
    (RegionOperation.enableLookup
        { inputs := [i0, i1, i2],
          tables := [queryFixed c0, queryFixed c1, queryFixed c2] }
        [s] row).Constraints place self env
      ↔ ∃ tableRow : ℕ, tableRow < env.usableRows ∧
          i0.eval (Query.eval env (fun j => if j ∈ [s].map Selector.index then 1 else 0)
              (place self + row : ℕ)) = env.fixed c0 (tableRow : ℤ) ∧
          i1.eval (Query.eval env (fun j => if j ∈ [s].map Selector.index then 1 else 0)
              (place self + row : ℕ)) = env.fixed c1 (tableRow : ℤ) ∧
          i2.eval (Query.eval env (fun j => if j ∈ [s].map Selector.index then 1 else 0)
              (place self + row : ℕ)) = env.fixed c2 (tableRow : ℤ) := by
  simp only [RegionOperation.constraints_enableLookup, List.map_cons, List.map_nil,
    List.cons.injEq, and_true, queryFixed, Expression.eval, Query.eval, add_zero]

end Halo2.TupleLookup.Test
