import Clean.Circuit.WitnessIRSugar

/-!
Regression tests for the `u64Wrap` simproc: the `% 2^64` / `% 64` truncations left behind
by the u64 witness sort are erased exactly when the local hypotheses bound the operand.
-/

/-- The wrap is erased when `omega` can bound the operand from the local context. -/
example (a b : ℕ) (h : a < 256 ∧ b < 256) :
    (a % 18446744073709551616 ^^^ b % 2^64) = a ^^^ b := by
  simp only [circuit_norm]

/-- Shift-amount masks (`% 64`) are erased the same way. -/
example (i : ℕ) (h : i < 32) : (7 >>> (i % 64)) = 7 >>> i := by
  simp only [circuit_norm]

/-- Without a bound the wrap stays: `circuit_norm` must not "simplify" it away. -/
example (a : ℕ) : a % 18446744073709551616 = a % 2 ^ 64 := by
  norm_num

/-- Other moduli are left alone, so specification arithmetic is untouched. -/
example (a : ℕ) (h : a < 8) : a % 256 = a := by
  fail_if_success simp only [circuit_norm]
  omega

/-!
`<?` overloads on the operand sort: field-sorted operands compare `ZMod.val`s exactly,
u64-sorted operands compare `u64`s (and so agree only below `2^64`).
-/
section LtCond
open Witgen
variable {F : Type} [FiniteField F]

/-- Field operands produce the exact `ZMod.val` comparison, with no truncation. -/
example (ctx : Ctx F) (x y : FExpr F) :
    (x <? y).eval ctx = decide (FiniteField.val (x.eval ctx) < FiniteField.val (y.eval ctx)) :=
  rfl

/-- u64 operands still produce the `u64` comparison. -/
example (ctx : Ctx F) (x y : U64Expr F) :
    (x <? y).eval ctx = decide (x.eval ctx < y.eval ctx) :=
  rfl

/-- `x.val <? y.val` goes through the u64 sort, so it compares truncated values —
the field-sorted form above is the one to use when operands may exceed `2^64`. -/
example (ctx : Ctx F) (x y : FExpr F) :
    (x.val <? y.val).eval ctx
      = decide (FiniteField.val (x.eval ctx) % 2^64 < FiniteField.val (y.eval ctx) % 2^64) := by
  simp [circuit_norm, UInt64.lt_iff_toNat_lt]
end LtCond

section BitOf
open Witgen
variable {F : Type} [FiniteField F]

/-- `BExpr.bit` is a condition; casting it into the field gives the `0`/`1` element, in
the same normal form `VExpr.bitsOf` produces for the loop-indexed case. -/
example (ctx : Ctx F) (x : FExpr F) (i : ℕ) :
    FExpr.eval ctx (x.bit i) = FiniteField.fromNat (FiniteField.val (x.eval ctx) >>> i % 2) := by
  simp only [circuit_norm]

/-- The bit index is a static `ℕ`, so it is exact past 64 on large fields. -/
example (ctx : Ctx F) (x : FExpr F) :
    (BExpr.bit x 200).eval ctx = (FiniteField.val (x.eval ctx)).testBit 200 :=
  rfl
end BitOf
