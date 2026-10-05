/-
Field inversion, and what it buys: a non-zero assertion and division.

`Inverse` is the archetype of a gadget whose *soundness* is stronger than what the circuit
literally says: `x * inv = 1` proves, after the fact, that `x` was non-zero. `AssertNonZero`
and `Div` then reuse that, at the interface level only.
-/
module

public import Clean2.Gadgets.Bool

@[expose] public section

namespace Clean2
variable {Native : Type} [Field Native]

/-! ## `inverse`: witness `x⁻¹` and pin it down with `x * inv = 1` -/

namespace Inverse

@[reducible]
def interface : Interface Native where
  input := Native
  inputCType := .native
  output := Native
  outputCType := .native
  Spec := fun x out => x ≠ 0 ∧ out = x⁻¹
  ProverAssumptions := fun x => x ≠ 0
  ProverSpec := fun x out => out = x⁻¹

def impl {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) : Impl B interface where
  main x := do
    let inv ← arith (.witness native fun v => v⁻¹) x
    let one ← arith (.const 1) ()
    arith .mulEq (x, inv, one)
    return inv
  soundness := by
    intro s env x h_assumptions h
    simp only [circuit_norm] at h ⊢
    obtain ⟨h_one, h_mul⟩ := h
    rw [h_one] at h_mul
    refine ⟨fun hx => ?_, eq_inv_of_mul_eq_one_right h_mul⟩
    rw [hx, zero_mul] at h_mul
    exact zero_ne_one h_mul
  completeness := by
    intro s env x h h_prover
    simp only [circuit_norm] at h h_prover ⊢
    -- the honest witness is `x⁻¹`, so `x * inv = 1 = one`
    obtain ⟨h_inv, h_one⟩ := h
    rw [h_inv, h_one]
    exact ⟨mul_inv_cancel₀ h_prover, rfl⟩

end Inverse

/-! ## `assertNonZero`: the same circuit, with the output thrown away -/

namespace AssertNonZero

@[reducible]
def interface : Interface Native where
  input := Native
  inputCType := .native
  output := Unit
  outputCType := .unit
  Spec := fun x _ => x ≠ 0
  ProverAssumptions := fun x => x ≠ 0

def impl {B : Backend} [Field B.Native] (inverse : Impl B Inverse.interface) : Impl B interface where
  main x := do
    let _ ← inverse x
    return ()
  soundness := by
    intro s env x _ h
    simp only [circuit_norm] at h ⊢
    -- `Inverse.interface.Spec` already says `x ≠ 0`
    exact h.1
  completeness := by
    intro s env x _ h_prover
    simp only [circuit_norm] at h_prover ⊢
    -- the only obligation is `Inverse.interface.ProverAssumptions`, which is this one's
    exact h_prover

end AssertNonZero

/-! ## `div`: `a / b`, which is only defined when `b ≠ 0` -/

namespace Div

@[reducible]
def interface : Interface Native where
  input := Native × Native
  inputCType := .nativePair
  output := Native
  outputCType := .native
  Spec := fun (a, b) out => b ≠ 0 ∧ out = a / b
  ProverAssumptions := fun (_, b) => b ≠ 0
  ProverSpec := fun (a, b) out => out = a / b

def impl {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) (inverse : Impl B Inverse.interface) :
    Impl B interface where
  main | (a, b) => do
    let binv ← inverse b
    arith .mul (a, binv)
  soundness := by
    intro s env (a, b) h_assumptions h
    simp only [circuit_norm] at h ⊢
    -- `b ≠ 0` and `binv = b⁻¹` from `Inverse`, `out = a * binv` from `Mul`
    obtain ⟨⟨hb, h_inv⟩, h_mul⟩ := h
    exact ⟨hb, by rw [h_mul, h_inv, div_eq_mul_inv]⟩
  completeness := by
    intro s env (a, b) h h_prover
    simp only [circuit_norm] at h h_prover ⊢
    -- discharging `Inverse`'s prover assumption `b ≠ 0` also yields `binv = b⁻¹`
    obtain ⟨h_inv, h_mul⟩ := h
    refine ⟨h_prover, ?_⟩
    rw [h_mul, (h_inv h_prover).2, div_eq_mul_inv]

end Div

/-! ## On both backends -/

def inverseExpr : Impl (ExprBackend Native) Inverse.interface := Inverse.impl ExprBackend.arith
def inverseR1CS : Impl (R1CS Native) Inverse.interface := Inverse.impl R1CS.arith

def assertNonZeroExpr : Impl (ExprBackend Native) AssertNonZero.interface := AssertNonZero.impl inverseExpr
def assertNonZeroR1CS : Impl (R1CS Native) AssertNonZero.interface := AssertNonZero.impl inverseR1CS

def divExpr : Impl (ExprBackend Native) Div.interface := Div.impl ExprBackend.arith inverseExpr
def divR1CS : Impl (R1CS Native) Div.interface := Div.impl R1CS.arith inverseR1CS

/-- One witness cell on either backend; the multiplication is free only on the expression one. -/
example (x : Expr Native) (s : ℕ) : (inverseExpr (Native := Native)).advance x s = s + 1 := rfl
example (x : LinComb Native) (s : ℕ) : (inverseR1CS (Native := Native)).advance x s = s + 1 := rfl
example (a b : Expr Native) (s : ℕ) : (divExpr (Native := Native)).advance (a, b) s = s + 1 := rfl
example (a b : LinComb Native) (s : ℕ) : (divR1CS (Native := Native)).advance (a, b) s = s + 2 := rfl

/-- On R1CS, `inverse` is a single constraint on the witnessed cell. -/
example (x : LinComb Native) (s : ℕ) :
    ((inverseR1CS (Native := Native)).main x |>.operations s).toFlat =
      [.witness 1 #v[x] (fun v => v[0]⁻¹), .constraint x (.cell s) (.ofConst 1)] := rfl

/-- Witness generation, at the interface level: for a non-zero input, an honest environment
satisfying every constraint exists on top of whatever the caller has already assigned. -/
example (x : LinComb Native) (s : ℕ) (env₀ : ℕ → Native) (h : x.footprint ⊆ Linear.Alloc s)
    (hx : x.eval env₀ ≠ 0) :
    ∃ env, (∀ c < s, env c = env₀ c) ∧
      ((inverseR1CS (Native := Native)).main x |>.operations s).ConstraintsHold env s ∧
      env s = (x.eval env)⁻¹ := by
  have h_out : (inverseR1CS (Native := Native)).output x s = .cell s := rfl
  have := (inverseR1CS (Native := Native)).exists_honest_env x s env₀ (by simpa [circuit_norm] using h) ⟨trivial, hx⟩
  simp only [circuit_norm, h_out] at this
  exact this

end Clean2
