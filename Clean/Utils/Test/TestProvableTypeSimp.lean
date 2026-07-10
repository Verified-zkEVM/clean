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

/-! ### Named-cell / typed-read normal form ("pretty cells")

The `circuit_norm` normal form for circuit-created cells and environment reads: assign/copy
outputs are the *named* `AssignedCell.of` (never an anonymous record literal), and every
typed read — gate query, assigned-cell eval, witness read — lands on the
`Environment.advice`-family accessors with the `↑(place self + row)` row form. The
`guard_hyp … :ₛ` assertions are syntactic: they fail if record literals
(`{ kind := … }`, `{ regionIndex := … }`) ever leak back into the normal form. -/

-- 6. The assign/copy output is the named cell, kept folded.
example (col : Column .advice) (self : RegionIndex) (row : ℕ) (compute : WitgenIR Fp 1) :
    (assignAdvice (F := Fp) col row compute).output self = .of self row col := by
  simp only [circuit_norm]

-- 7. An `assignAdvice` output under `eval` normalizes to a typed `env.advice` read —
-- syntactically (`guard_hyp :ₛ`): no cell/column record literals, row spelled
-- `↑(place self + row)`. (`provable_type_simp` doing nothing on top asserts the terminal
-- form is stable under it.)
set_option linter.unusedTactic false in
example (env : Placed Environment Fp) (col : Column .advice) (self : RegionIndex)
    (row : ℕ) (compute : WitgenIR Fp 1) (out : Fp)
    (h : eval env ((assignAdvice col row compute).output self) = out) :
    env.env.advice col ((env.place self + row : ℕ) : ℤ) = out := by
  simp only [circuit_norm] at h
  provable_type_simp
  guard_hyp h :ₛ env.env.advice col ((env.place self + row : ℕ) : ℤ) = out
  exact h

-- 8. The gate-query path meets the assigned-cell path on the same `env.advice` spelling:
-- after `circuit_norm` (rotation 0 cleared by `add_zero`) both sides are the SAME atom,
-- so simp closes the equality by rfl.
example (env : Environment Fp) (col : Column .advice) (sel : ℕ → Fp)
    (place : RegionIndex → ℕ) (self : RegionIndex) (row : ℕ) :
    Query.eval env sel ((place self + row : ℕ) : ℤ) (.advice col 0)
      = AssignedCell.eval place env (.of self row col) := by
  simp only [circuit_norm]

-- 9. The witness-read path (witgen `readVar`) also lands on `env.advice` for named cells.
set_option linter.unusedVariables false in
example (pe : Placed ProverEnvironment Fp) (col : Column .advice) (self : RegionIndex)
    (row : ℕ) (out : Fp)
    (h : Witgen.WitgenEnv.readVar pe (AssignedCell.of self row col : AssignedCell Fp) = out) :
    True := by
  simp only [circuit_norm] at h
  guard_hyp h :ₛ pe.env.toEnvironment.advice col ((pe.place self + row : ℕ) : ℤ) = out
  trivial

end Halo2.ProvableTypeSimp.Test
