/-
`isZero`: the classic circuit that needs a witness.

  inv ← witness x⁻¹          (any value works when x = 0)
  out ← 1 - x * inv
  assert x * out = 0

Soundness: if x = 0 then out = 1 - 0 = 1; if x ≠ 0 then x * out = 0 forces out = 0.
Completeness: the honest inv = x⁻¹ makes out = 1 - x*x⁻¹, which is 1 or 0, and x * out = 0.
-/
module

public import Clean2.Gadgets.Bool

@[expose] public section

namespace Clean2
variable {Native : Type} [Field Native]

namespace IsZero

@[reducible]
def interface : Interface Native where
  input := Native
  inputCType := .native
  output := Native
  outputCType := .native
  Spec := fun x out => (x = 0 → out = 1) ∧ (x ≠ 0 → out = 0)

/-- Generic over the arithmetic. The witness is a functionality like any other: nothing is
known about `inv` for soundness, and its value is known for completeness. -/
def impl {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) : Impl B interface where
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
    simp only [circuit_norm] at h ⊢
    -- the five facts: t = x*inv, one = 1, out = one - t, zero = 0, x*out = zero (the witness gives none)
    obtain ⟨ht, hone, hout, hzero, hmul⟩ := h
    simp only [hout, hone, ht, hzero] at hmul ⊢
    constructor
    · intro hx
      simp [hx]
    · intro hx
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd h hx
      · exact h
  completeness := by
    intro s env x h _
    simp only [circuit_norm] at h ⊢
    -- the honest prover knows inv = x⁻¹ (the witness's `ProverSpec`) and, by soundness of the
    -- children, all the intermediate values; the only obligation is the assertion x*out = 0
    by_cases hx : B.eval env x = 0 <;> simp_all

end IsZero

def isZeroExpr : Impl (ExprBackend Native) IsZero.interface := IsZero.impl ExprBackend.arith
def isZeroR1CS : Impl (R1CS Native) IsZero.interface := IsZero.impl R1CS.arith

/-! ### Allocation in action

The same gadget, resolved on each backend. Cells are numbered from the state `s` at which the
gadget is instantiated; the witness computations refer to the input variable `x`. -/

/-- Expression backend: one cell (the witness), one constraint; the arithmetic is folded
into expressions. -/
example (x : Expr Native) (s : ℕ) : (isZeroExpr (Native := Native)).advance x s = s + 1 := rfl
example (x : Expr Native) (s : ℕ) :
    ((isZeroExpr (Native := Native)).main x |>.operations s).toFlat =
      [ .witness 1 #v[x] (fun v => v[0]⁻¹),
        .assertZero (.add (.mul x (.add (.const 1) (.mul (.const (-1)) (.mul x (.var s)))))
                          (.mul (.const (-1)) (.const 0))) ] := rfl

/-- R1CS: two cells (the witness `inv` at `s`, the product `x * inv` at `s + 1`) and two
constraints; the linear part (`1 - t`) is folded into the linear combination. -/
example (x : LinComb Native) (s : ℕ) : (isZeroR1CS (Native := Native)).advance x s = s + 2 := rfl
example (x : LinComb Native) (s : ℕ) :
    ((isZeroR1CS (Native := Native)).main x |>.operations s).toFlat =
      [ .witness 1 #v[x] (fun v => v[0]⁻¹),
        .witness 2 #v[x, .cell s] (fun v => v[0] * v[1]),
        .constraint x (.cell s) (.cell (s + 1)),
        .constraint x (.ofConst 1 - .cell (s + 1)) (.ofConst 0) ] := rfl

/-- The spatial contract, instantiated: whatever the caller's heap, the gadget's inputs only
need to exist in it, and then an honest environment for the gadget exists on top of it. -/
example (x : LinComb Native) (s : ℕ) (env₀ : ℕ → Native) (h : x.footprint ⊆ Linear.Alloc s) :
    ∃ env, (∀ c < s, env c = env₀ c) ∧ ((isZeroR1CS (Native := Native)).main x |>.operations s).Honest env s :=
  (isZeroR1CS (Native := Native)).honest_env_exists x s env₀ (by simpa [circuit_norm] using h)

end Clean2
