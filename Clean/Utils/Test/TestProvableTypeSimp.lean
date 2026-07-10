import Clean.Halo2.Tactics.ProvableTypeSimp
import Clean.Ironwood.Ecc.Basic

/-!
Regression tests for `provable_type_simp` (halo2). Each asserts a shape or a consumption
pattern the confluence claims depend on. Companion to main Clean's `TestProvableStructSimp`.
-/

namespace Halo2.ProvableTypeSimp.Test
open Halo2 Halo2.Ironwood

/-- Two-level struct: a `ProvableStruct` whose components are themselves higher-level
(`Point`) — the Add32 `{x:U32,y:U32}` analogue. -/
structure TwoPoints (F : Type) where
  p : Point F
  q : Point F
deriving ProvableStruct

-- 1. Plain `ProvableType` (`Point`) literal decomposition, consumed by a row fact:
-- the whole-struct eval equation splits field-wise and discharges the projected goal.
example (env : Placed Environment Fp) (a b : AssignedCell Fp) (out : Point Fp)
    (h : eval env (⟨a, b⟩ : Point (AssignedCell Fp)) = out) :
    eval env a = out.x := by
  provable_type_simp
  exact h.1

-- 2. Two-level struct decomposes along component boundaries and keeps `Point` WHOLE: the
-- literal decomposes to `⟨eval env p, eval env q⟩` with the `Point` components *un*-flattened.
-- The equality closes only because both sides carry the identical Point-level `eval env p`
-- (had the LHS flattened to field reads it would not match the RHS).
example (env : Placed Environment Fp) (p q : Point (AssignedCell Fp)) :
    eval env (⟨p, q⟩ : TwoPoints (AssignedCell Fp)) = ⟨eval env p, eval env q⟩ := by
  provable_type_simp

-- 3. Plain `ProvableType` drilled into: a projection under `eval` lifts to the row level and
-- the row fact discharges it.
example (env : Placed Environment Fp) (v : Point (AssignedCell Fp)) (out : Point Fp)
    (h : eval env v = out) :
    eval env v.x = out.x := by
  provable_type_simp
  exact h.1

-- 4. Opaque `eval = eval` between two structs is a row-level fact: left folded, as `eval`
-- (NOT flattened to `ProvableType.eval`). `provable_type_simp` is intentionally a no-op here
-- — that no-op is the assertion that the opaque value keeps the `eval` normal form.
set_option linter.unusedTactic false in
example (env : Placed Environment Fp) (u v : Point (AssignedCell Fp))
    (h : eval env u = eval env v) :
    eval env u = eval env v := by
  provable_type_simp
  exact h

-- 5. Constructor-equality of values splits field-wise (verifier side).
example (a b c d : AssignedCell Fp) (env : Placed Environment Fp)
    (h : eval env (⟨a, b⟩ : Point (AssignedCell Fp)) = eval env (⟨c, d⟩ : Point (AssignedCell Fp))) :
    eval env a = eval env c := by
  provable_type_simp
  exact h.1

end Halo2.ProvableTypeSimp.Test
