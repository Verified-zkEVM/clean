import Lean.Elab.Tactic
import Clean.Halo2.Lemmas
import Clean.Halo2.Formal

/-!
# `round_norm`

The single tactic that normalizes a per-round constraint hypothesis (a fresh loop round,
peeled from `loop_operations_succ`) down to its value-level gate equations. It replaces the
~15-lemma `simp only [circuit_norm, <gate defs>, …]` + manual rotation-row cast bridges
(`have hzp : ↑(place self + (offset + 1 + r)) - 1 = ↑(place self + (offset + r)) := by
push_cast; ring`) that appear 6+ times across `MulIncomplete`/`HashPiece`/`MulComplete`/`Chain`.

## What it bundles

`round_norm [gate₁, gate₂, …] at h`

1. runs `simp only [gate₁, …, circuit_norm, Constraints.withSelector] at h`, where the
   user-supplied args are the round def (`round`), the gate defs (`qMul3Gate`, `sinsemillaGate`,
   …), their helper polys (`yAExpr`, `xRExpr`, `forLoopPolys`, `qS3Expr`, …), and any
   `if_pos`/`if_neg` selector-condition resolutions for the specific round position;
2. normalizes the residual **rotation-row casts** with the `roundRow*` lemma set below: after
   `circuit_norm`'s `cast_row_succ`/`cast_row_pred`/`row_succ_succ`/`add_zero` fire, a
   `Rotation::prev` cell read still surfaces as `↑(place self + (off + 1 + r)) - 1`, whose inner
   `ℕ` index must be re-associated to meet the assignment's `↑(place self + (off + r))` spelling
   — the mechanical replacement for the hand-written `hzp`/`hz1` casts.

The lemmas are the associativity companions of `cast_row_pred`/`cast_row_succ` for the
`off + 1 + r` (`Rotation::prev`) and `off + r` (`Rotation::next`) loop-row spellings the
gadgets produce; they are stated as plain rewrites (not `@[circuit_norm]`, to keep the ambient
normal form unchanged) and applied only inside `round_norm`.
-/

open Lean Elab Tactic

namespace Halo2.RoundNorm

/-! ## Rotation-row associativity lemmas

These bridge the loop-row cast spellings that `circuit_norm`'s `cast_row_pred`/`cast_row_succ`
leave behind: the gate reads a rotated cell at `off + 1 + r` (`Rotation::prev`, `- 1`) or
`off + r` (`Rotation::next`, `+ 1`), while the *assignment* producing that cell spells it
`off + r` / `off + (r + 1)`. Proven once by `omega`; applied by `round_norm`. -/

/-- `Rotation::prev` at a loop row: `↑(a + (b + 1 + r)) - 1 = ↑(a + (b + r))`. The `z`-prev
read in `MulIncomplete.round` (the hand `hzp`). -/
theorem roundRowPrev (a b r : ℕ) :
    ((a + (b + 1 + r) : ℕ) : ℤ) - 1 = ((a + (b + r) : ℕ) : ℤ) := by
  push_cast; ring

/-- `Rotation::prev` variant with the `+1` innermost: `↑(a + (b + r + 1)) - 1 = ↑(a + (b + r))`. -/
theorem roundRowPrev' (a b r : ℕ) :
    ((a + (b + r + 1) : ℕ) : ℤ) - 1 = ((a + (b + r) : ℕ) : ℤ) := by
  push_cast; ring

/-- `Rotation::next` at a loop row: `↑(a + (b + r)) + 1 = ↑(a + (b + (r + 1)))`. The next-row
read in `HashPiece.round`/`Chain` (the hand `hz1`), landing on the `assignAdvice … (offset + (r+1))`
source spelling. -/
theorem roundRowNext (a b r : ℕ) :
    ((a + (b + r) : ℕ) : ℤ) + 1 = ((a + (b + (r + 1)) : ℕ) : ℤ) := by
  push_cast; ring

/-- The fixed rotation-row normalization simp set applied by `round_norm` after the gate simp. -/
def rotationRowLemmas : Array Name := #[
  ``roundRowPrev, ``roundRowPrev', ``roundRowNext]

/-- `round_norm [l₁, l₂, …] at h` : normalize a per-round constraint hypothesis to its
value-level gate equations. See the module docstring. -/
syntax (name := roundNorm) "round_norm"
  (" [" withoutPosition(Lean.Parser.Tactic.simpLemma,*) "]")? " at " ident : tactic

@[tactic roundNorm]
def evalRoundNorm : Tactic := fun stx => do
  match stx with
  | `(tactic| round_norm $[[ $args,* ]]? at $h:ident) =>
    let userArgs : Array (TSyntax `Lean.Parser.Tactic.simpLemma) :=
      match args with
      | some a => a.getElems
      | none => #[]
    let fixed : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[
      ← `(Lean.Parser.Tactic.simpLemma| circuit_norm),
      ← `(Lean.Parser.Tactic.simpLemma| Halo2.Constraints.withSelector)]
    let allArgs := userArgs ++ fixed
    -- the gate `circuit_norm` reduction with the user gate/def args
    (do evalTactic (← `(tactic| simp only [$[$allArgs],*] at $h:ident))) <|> pure ()
    -- the rotation-row cast normalization (the mechanized `hzp`/`hz1` bridges)
    let rowArgs ← rotationRowLemmas.mapM fun n =>
      `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
    (do evalTactic (← `(tactic| simp only [$[$rowArgs],*] at $h:ident))) <|> pure ()
  | _ => throwUnsupportedSyntax

end Halo2.RoundNorm
