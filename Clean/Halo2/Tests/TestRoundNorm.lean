import Clean.Halo2.Tactics.RoundNorm
import Clean.Ironwood.Ecc.Basic

/-!
Regression pins for `round_norm`'s rotation-row normalization (C2a #1). These assert the
mechanized replacement for the hand-written `hzp`/`hz1` cast bridges: a `Rotation::prev`/`next`
loop-row cast normalizes to the assignment's `↑(place self + …)` spelling, so a gate polynomial
lines up with its assigned cell without a per-gadget `have … := by push_cast; ring`.

The tactic's gate-`simp` half is exercised end-to-end by the acceptance demonstration in
`Clean/Ironwood/Ecc/MulIncomplete.lean` (`loop_gate_facts`, interior `q_mul_2` branch); these
pins isolate the rotation-row half on the exact cast shapes the gadgets produce.
-/

namespace Halo2.RoundNorm.Test
open Halo2 Halo2.Ironwood

-- 1. `Rotation::prev` (`- 1`) at a loop row: `↑(place self + (offset + 1 + r)) - 1` normalizes to
-- the assignment spelling `↑(place self + (offset + r))` — the mechanized `MulIncomplete.hzp`.
example (env : Environment Fp) (col : Column .advice) (place : RegionIndex → ℕ)
    (self : RegionIndex) (offset r : ℕ)
    (h : env.advice col (↑(place self + (offset + 1 + r)) - 1) = 0) :
    env.advice col ↑(place self + (offset + r)) = 0 := by
  round_norm [] at h
  guard_hyp h :ₛ env.advice col ↑(place self + (offset + r)) = 0
  exact h

-- 2. `Rotation::next` (`+ 1`) at a loop row: `↑(place self + (offset + r)) + 1` normalizes to the
-- assignment's next-row spelling `↑(place self + (offset + r + 1))` (here via `circuit_norm`'s
-- `cast_row_succ`; `round_norm`'s own `roundRowNext` covers the `offset + (r + 1)` source spelling
-- some gadgets use — both are defeq). This is the mechanized `HashPiece.hz1`.
example (env : Environment Fp) (col : Column .advice) (place : RegionIndex → ℕ)
    (self : RegionIndex) (offset r : ℕ)
    (h : env.advice col (↑(place self + (offset + r)) + 1) = 0) :
    env.advice col ↑(place self + (offset + r + 1)) = 0 := by
  round_norm [] at h
  guard_hyp h :ₛ env.advice col ↑(place self + (offset + r + 1)) = 0
  exact h

-- 3. Idempotence / no-op: an already-normalized cast is left unchanged (the confluence pin —
-- `round_norm` never re-associates a canonical row index).
set_option linter.unusedTactic false in
example (env : Environment Fp) (col : Column .advice) (place : RegionIndex → ℕ)
    (self : RegionIndex) (offset r : ℕ)
    (h : env.advice col ↑(place self + (offset + r)) = 0) :
    env.advice col ↑(place self + (offset + r)) = 0 := by
  round_norm [] at h
  exact h

end Halo2.RoundNorm.Test
