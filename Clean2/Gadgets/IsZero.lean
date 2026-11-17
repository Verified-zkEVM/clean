/-
`isZero`: the classic circuit that needs a witness.

  inv ← witness x⁻¹          (any value works when x = 0)
  out ← 1 - x * inv
  assert x * out = 0

The output is a boolean, at `bit`: `out = 1` exactly when `x = 0`.

Soundness: if x = 0 then out = 1 - 0 = 1; if x ≠ 0 then x * out = 0 forces out = 0.
Completeness: the honest inv = x⁻¹ makes out = 1 - x*x⁻¹, which is 1 or 0, and x * out = 0.
-/
module

public import Clean2.Gadgets.Bool

@[expose] public section

namespace Clean2
variable {Native : Type} [Field Native]

namespace IsZero

/-- Whether a native element is zero, as a boolean laid out as `bool`. -/
@[reducible]
def interface [DecidableEq Native] (bool : CType Native Bool) : Interface Native where
  input := Native
  inputCType := .native
  output := Bool
  outputCType := bool
  Spec := fun x out => out = decide (x = 0)

/-- Generic over the arithmetic; the output is a `bit`. The witness is a functionality like any
other: nothing is known about `inv` for soundness, and its value is known for completeness. -/
def impl {B : Backend} [Field B.Native] [DecidableEq B.Native] (arith : ∀ n, Impl B (Arith.interface n)) :
    Impl B (interface (bit B.Native)) where
  main x := do
    let inv ← arith (.witness native fun v => v⁻¹) x
    let t ← arith .mul (x, inv)
    let one ← arith (.const 1) ()
    let out ← arith .sub (one, t)
    let zero ← arith (.const 0) ()
    arith .mulEq (x, out, zero)
    return out
  soundness := by
    intro s env x _ h
    simp only [circuit_norm, IsBool] at h ⊢
    -- the five facts: t = x*inv, one = 1, out = one - t, zero = 0, x*out = zero (the witness gives none)
    obtain ⟨ht, hone, hout, hzero, hmul⟩ := h
    simp only [hout, hone, ht, hzero] at hmul ⊢
    by_cases hx : B.eval env x = 0
    · simp [hx]
    · rcases mul_eq_zero.mp hmul with h | h
      · exact absurd h hx
      · simp [h, hx]
  completeness := by
    intro s env x h _
    simp only [circuit_norm, IsBool] at h ⊢
    -- the honest prover knows inv = x⁻¹ (the witness's `ProverSpec`) and, by soundness of the
    -- children, all the intermediate values; the obligations are the assertion x*out = 0 and that
    -- out is a bit
    by_cases hx : B.eval env x = 0 <;> simp_all

end IsZero

end Clean2
