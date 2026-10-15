/-
A linear combination with constant coefficients, `x ↦ ∑ i, m i * x[i]`: a loop of scalings and
additions, so free on the backends whose variables are linear combinations (R1CS).
-/
module

public import Clean2.Functionalities.Arith
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace Clean2
variable {F : Type} [Field F]

namespace Mix

/-- The coefficients of a linear combination, over `t` inputs. -/
structure Params (F : Type) where
  t : ℕ
  m : Fin t → F

/-- `x ↦ ∑ i, m i * x[i]`. -/
@[reducible]
def interface (p : Params F) : Interface F where
  input := Vector F p.t
  inputCType := .natives p.t
  output := F
  outputCType := .native
  Spec := fun x y => y = ∑ i, p.m i * x[i]

/-- The tail sums `∑_{j ≥ i}`, one step: the loop invariant of `impl`. -/
theorem sum_tail_succ {t : ℕ} (f : Fin t → F) (i : Fin t) :
    (∑ j : Fin t, if (i : ℕ) ≤ j then f j else 0) =
      f i + ∑ j : Fin t, if (i : ℕ) + 1 ≤ j then f j else 0 := by
  have : ∀ j : Fin t, (if (i : ℕ) ≤ j then f j else 0) =
      (if j = i then f j else 0) + (if (i : ℕ) + 1 ≤ j then f j else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp
    · have : (j : ℕ) ≠ i := fun h => hj (Fin.ext h)
      by_cases hle : (i : ℕ) ≤ j
      · rw [if_pos hle, if_neg hj, if_pos (by omega), zero_add]
      · rw [if_neg hle, if_neg hj, if_neg (by omega), zero_add]
  rw [Finset.sum_congr rfl fun j _ => this j, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ i,
    if_pos (Finset.mem_univ _)]

/-- A loop of scalings and additions: linear, so free on R1CS. -/
def impl {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n)) (p : Params B.Native) : Impl B (interface p) where
  main x := do
    let zero ← arith (.const 0) ()
    Circuit.foldr p.t (fun i acc => do
      let y ← arith (.scale (p.m i)) x[i]
      arith .add (acc, y)) zero
  consistent := by
    intro x s
    simp only [circuit_norm]
    exact Circuit.foldr_consistent _ _ _ fun i acc s => by simp only [circuit_norm]
  spatial := by
    intro x s h_in
    simp only [circuit_norm] at h_in ⊢
    refine ⟨Set.empty_subset _, fun h_zero h_mono => ?_⟩
    refine Circuit.foldr_local _ _ _ _ (fun i acc s => by simp only [circuit_norm])
      (fun i acc s h_mono' h_acc => ?_) (by rw [Backend.footprintT_native]; exact h_zero)
      fun h => by rw [Backend.footprintT_native] at h; exact h
    simp only [circuit_norm, Set.union_subset_iff] at h_acc ⊢
    exact ⟨(Backend.footprint_getElem_subset h_in i i.isLt).trans (h_mono.trans h_mono'),
      fun h_y h_mono'' => ⟨⟨h_acc.trans h_mono'', h_y⟩, fun h_out _ => h_out⟩⟩
  soundness := by
    intro s env x _ h
    simp only [circuit_norm] at h ⊢
    obtain ⟨h_zero, h_loop⟩ := h
    have := Circuit.foldr_sound _ _ _ env
      (fun i acc => B.eval env acc = ∑ j : Fin p.t, if i ≤ (j : ℕ) then p.m j * B.eval env x[j] else 0)
      ?_ ?_ h_loop
    · simp only [zero_le, if_true, Vector.getElem_map, Fin.getElem_fin] at this ⊢
      exact this
    · rw [h_zero]
      exact (Finset.sum_eq_zero fun j _ => if_neg (by have := j.isLt; omega)).symm
    · intro i acc s h_inv h_step
      simp only [circuit_norm] at h_step ⊢
      obtain ⟨h_y, h_add⟩ := h_step
      rw [h_add, h_y, h_inv, sum_tail_succ, Fin.getElem_fin]
      ring
  completeness := by
    intro s env x h _
    simp only [circuit_norm] at h ⊢
    exact Circuit.foldr_complete _ _ _ env (fun i acc s h => by simp only [circuit_norm] at h ⊢) h.2

end Mix

end Clean2
