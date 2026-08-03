import Clean.Circuit.WitnessIR

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
