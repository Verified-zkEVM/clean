import Clean.Circuit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import Clean.Orchard.Specs.Pallas

/-!
# Double-and-add row (incomplete addition)

The `(x_A, x_P, λ₁, λ₂)` cells of one incomplete-addition double-and-add step and the
derived `x_R`/`Y_A` formulas. This is shared ECC machinery used by both scalar
multiplication and the Sinsemilla hash, so it lives under `Orchard.Ecc` rather than
inside Sinsemilla.

Reference:
`halo2@halo2_gadgets-0.5.0/halo2_gadgets/src/ecc/chip/mul/incomplete.rs`
- `DoubleAndAdd::x_r`
- `DoubleAndAdd::Y_A`
-/

namespace Orchard.Ecc

structure DoubleAndAddRow (F : Type) where
  xA : F
  xP : F
  lambda1 : F
  lambda2 : F
deriving ProvableStruct

namespace DoubleAndAdd

def xR {K : Type} [Sub K] [Mul K] (row : DoubleAndAddRow K) : K :=
  row.lambda1 * row.lambda1 - row.xA - row.xP

def yA {K : Type} [Add K] [Sub K] [Mul K] (row : DoubleAndAddRow K) : K :=
  (row.lambda1 + row.lambda2) * (row.xA - xR row)

/--
If the incomplete double-and-add operation `(A ⸭ S) ⸭ A` returns `B`, then the
standard non-degenerate affine row equations determine the output coordinates.
-/
theorem coordinates_of_constraints {A S B : Point Fp}
    (hstep : Point.doubleAndAdd A S = some B)
    {xp lambda1 lambda2 xB YB : Fp}
    (hYP : 2 * A.y - 2 * lambda1 * (A.x - xp) = 2 * S.y)
    (hXP : xp = S.x)
    (hYA : 2 * A.y = (lambda1 + lambda2) * (A.x - (lambda1 * lambda1 - A.x - xp)))
    (hSecant : lambda2 * lambda2 = xB + (lambda1 * lambda1 - A.x - xp) + A.x)
    (hYCheck : 4 * lambda2 * (A.x - xB) = 4 * A.y + 2 * YB) :
    xB = B.x ∧ YB = 2 * B.y := by
  have hYP' : A.y - lambda1 * (A.x - xp) = S.y :=
    mul_left_cancel₀ (by decide : (2 : Fp) ≠ 0) (by linear_combination hYP)
  unfold Point.doubleAndAdd at hstep
  by_cases hc₁ : A = 0 ∨ S = 0 ∨ A.x = S.x
  · rw [Point.incompleteAdd_def, if_pos hc₁] at hstep
    simp at hstep
  rw [Point.incompleteAdd_def, if_neg hc₁] at hstep
  push Not at hc₁
  obtain ⟨hA0, hS0, hAxS⟩ := hc₁
  set R : Point Fp := A + S with hR_def
  change Point.incompleteAdd R A = some B at hstep
  by_cases hc₂ : R = 0 ∨ A = 0 ∨ R.x = A.x
  · rw [Point.incompleteAdd_def, if_pos hc₂] at hstep
    simp at hstep
  rw [Point.incompleteAdd_def, if_neg hc₂] at hstep
  push Not at hc₂
  obtain ⟨hR0, -, hRxA⟩ := hc₂
  have hB : B = R + A := by
    have := Option.some.inj hstep
    rw [← this]
  subst hXP
  have hRadd := Point.nondegenerateAdd_eq_add (p := A) (q := S) hA0 hS0 hAxS
  rw [← hR_def] at hRadd
  have hRx := congrArg Point.x hRadd
  have hRy := congrArg Point.y hRadd
  simp only [Point.nondegenerateAdd] at hRx hRy
  set slope₁ : Fp := (S.y - A.y) * (S.x - A.x)⁻¹ with hslope₁
  have hAxS' : A.x - S.x ≠ 0 := sub_ne_zero.mpr hAxS
  have hl1 : lambda1 = slope₁ := by
    apply mul_right_cancel₀ hAxS'
    rw [hslope₁, mul_assoc,
      show (S.x - A.x)⁻¹ * (A.x - S.x) = -1 from by
        rw [show A.x - S.x = -(S.x - A.x) by ring, mul_neg,
          inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hAxS))]]
    linear_combination -hYP'
  have hxR : lambda1 * lambda1 - A.x - S.x = R.x := by
    rw [hl1]
    exact hRx
  have hyR : lambda1 * (A.x - R.x) - A.y = R.y := by
    rw [hl1, ← hRx]
    exact hRy
  have hRxA' : A.x - R.x ≠ 0 := sub_ne_zero.mpr fun h => hRxA h.symm
  have hBadd := Point.nondegenerateAdd_eq_add (p := R) (q := A) hR0 hA0 hRxA
  rw [← hB] at hBadd
  have hBx := congrArg Point.x hBadd
  have hBy := congrArg Point.y hBadd
  simp only [Point.nondegenerateAdd] at hBx hBy
  set slope₂ : Fp := (R.y - A.y) * (R.x - A.x)⁻¹ with hslope₂
  have hslope₂_alt : (A.y - R.y) * (A.x - R.x)⁻¹ = slope₂ := by
    rw [hslope₂, show A.y - R.y = -(R.y - A.y) by ring,
      show A.x - R.x = -(R.x - A.x) by ring, inv_neg]
    ring
  rw [hslope₂_alt] at hBx hBy
  have hl2 : lambda2 = slope₂ := by
    apply mul_right_cancel₀ hRxA'
    have hslope₂_mul : slope₂ * (A.x - R.x) = A.y - R.y := by
      rw [hslope₂, mul_assoc,
        show (R.x - A.x)⁻¹ * (A.x - R.x) = -1 from by
          rw [show A.x - R.x = -(R.x - A.x) by ring, mul_neg,
            inv_mul_cancel₀ (sub_ne_zero.mpr hRxA)]]
      ring
    rw [hslope₂_mul]
    have hYA' : 2 * A.y = (lambda1 + lambda2) * (A.x - R.x) := by
      rw [← hxR]
      exact hYA
    linear_combination -hYA' - hyR
  have hline₂ : lambda2 * (A.x - R.x) = A.y - R.y := by
    rw [hl2]
    rw [hslope₂, mul_assoc,
      show (R.x - A.x)⁻¹ * (A.x - R.x) = -1 from by
        rw [show A.x - R.x = -(R.x - A.x) by ring, mul_neg,
          inv_mul_cancel₀ (sub_ne_zero.mpr hRxA)]]
    ring
  constructor
  · rw [← hBx, ← hl2]
    rw [hxR] at hSecant
    rw [hSecant]
    ring
  · rw [← hBy]
    rw [← hl2]
    have hxB : lambda2 * lambda2 - R.x - A.x = xB := by
      rw [hxR] at hSecant
      rw [hSecant]
      ring
    rw [hxB]
    have hYB2 : 2 * YB = 4 * lambda2 * (R.x - xB) - 4 * R.y := by
      calc
        2 * YB = 4 * lambda2 * (A.x - xB) - 4 * A.y := by
          linear_combination -hYCheck
        _ = 4 * lambda2 * (R.x - xB) - 4 * R.y := by
          linear_combination 4 * hline₂
    apply mul_left_cancel₀ (by decide : (2 : Fp) ≠ 0)
    linear_combination hYB2

end DoubleAndAdd

end Orchard.Ecc
