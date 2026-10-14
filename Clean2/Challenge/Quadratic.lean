/-
The simplest challenge check: `a = b = c = 0`, by checking `a + b * α + c * α ^ 2 = 0` at one
challenge `α`.

- Pointwise: the circuit evaluates the quadratic at `α` and asserts that it is zero.
- Symbolically: `C a + C b * X + C c * X ^ 2 = 0` in `F[X]` means that every coefficient is zero.
- The polynomial has degree at most `2`: a non-zero triple is accepted at no more than `2`
  challenges.
- Completeness holds at every challenge: the zero triple satisfies the check everywhere.
-/
module

public import Clean2.Challenge.Basic
public import Clean2.Functionalities.Arith
public import Clean2.Backends.R1CS
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

namespace Clean2
open Polynomial

namespace Quadratic
variable {Native : Type} [Field Native]

/-- `a + b * X + c * X ^ 2`. -/
noncomputable def poly (a b c : Native) : Native[X] := C a + C b * X + C c * X ^ 2

theorem eval_poly (a b c α : Native) : (poly a b c).eval α = a + b * α + c * α ^ 2 := by
  simp [poly]

/-- The symbolic argument: a polynomial is zero exactly when its coefficients are. -/
theorem eq_zero_of_poly_eq_zero {a b c : Native} (h : poly a b c = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have h0 := congrArg (fun p => p.coeff 0) h
  have h1 := congrArg (fun p => p.coeff 1) h
  have h2 := congrArg (fun p => p.coeff 2) h
  simp [poly, coeff_X, coeff_C] at h0 h1 h2
  exact ⟨h0, h1, h2⟩

theorem natDegree_poly_le (a b c : Native) : (poly a b c).natDegree ≤ 2 := by
  unfold poly
  compute_degree

/-- The check: the triple is zero. -/
@[reducible]
noncomputable def check : ChallengeCheck Native where
  Phase1 := Native × Native × Native
  phase1CType := .nativeTriple
  Statement := fun (a, b, c) => a = 0 ∧ b = 0 ∧ c = 0
  poly := fun (a, b, c) => poly a b c
  symbolic := fun (_, _, _) _ h => eq_zero_of_poly_eq_zero h
  ProverAssumptions := fun (a, b, c) _ => a = 0 ∧ b = 0 ∧ c = 0

variable {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n))

/-- Horner's rule, `(c * α + b) * α + a`, and an assertion that it is zero. -/
noncomputable def impl : Impl B (check (Native := B.Native)).interface where
  main | ((a, b, c), α) => do
    let cα ← arith .mul (c, α)
    let s ← arith .add (cα, b)
    let sα ← arith .mul (s, α)
    let v ← arith .add (sα, a)
    arith .assertZero v
  spatial := by
    challenge_spatial
  soundness := by
    intro s env ((a, b, c), α) _ h
    simp only [circuit_norm] at h ⊢
    rw [eval_poly]
    obtain ⟨h_cα, h_s, h_sα, h_v, h_zero⟩ := h
    linear_combination h_zero - h_v - h_sα - B.eval env α * h_s - B.eval env α * h_cα
  completeness := by
    intro s env ((a, b, c), α) h h_prover
    simp only [circuit_norm] at h h_prover ⊢
    obtain ⟨h_cα, h_s, h_sα, h_v⟩ := h
    obtain ⟨ha, hb, hc⟩ := h_prover
    rw [h_v, h_sα, h_s, h_cα, ha, hb, hc]
    ring

/-- **Soundness error.** A non-zero triple is accepted at no more than two challenges, on any
backend: a soundness error of `2 / |F|`. -/
theorem soundness_error (a b c : B.Native) (h : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    {α | ChallengeCheck.Accepts (impl arith) (a, b, c) α}.ncard ≤ 2 :=
  (ChallengeCheck.soundness_error (impl arith) (a, b, c) trivial h).trans (natDegree_poly_le a b c)

end Quadratic

/-- On R1CS. -/
noncomputable def quadraticR1CS {F : Type} [Field F] : Impl (R1CS F) (Quadratic.check (Native := F)).interface :=
  Quadratic.impl R1CS.arith

end Clean2
