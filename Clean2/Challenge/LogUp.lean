/-
A logUp lookup argument, as a user writes it.

A table `t` with multiplicities `m`, and lookups `f`. The identity
  `∑ m i / (X - t i) - ∑ 1 / (X - f j) = 0`
says that every value `y` is looked up as often as the table's multiplicities for `y` add up to,
in the field: `#{j | f j = y} = ∑_{t i = y} m i` (`logUp_iff`). Completeness needs the challenge
to avoid the table and the lookups, since the honest prover divides by `α - t i` and `α - f j`.

The symbolic argument is a uniqueness of partial fractions (`eq_zero_of_sum_div_eq_zero`): if
`∑_{y ∈ S} d y / (X - y) = 0` for distinct `y`, then every `d y` is zero.
-/
module

public import Clean2.Challenge.Identity
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

namespace Clean2
open Polynomial

namespace LogUp
variable {F : Type} [Field F] [DecidableEq F]

/-- Uniqueness of partial fractions with simple poles. -/
theorem eq_zero_of_sum_div_eq_zero (S : Finset F) (d : F → F)
    (h : ∑ y ∈ S, RatFunc.C (d y) / (RatFunc.X - RatFunc.C y) = 0) : ∀ y ∈ S, d y = 0 := by
  -- clear denominators: `P = ∑ d y ∏_{z ≠ y} (X - z)` is zero
  set P : F[X] := ∑ y ∈ S, Polynomial.C (d y) * ∏ z ∈ S.erase y, (Polynomial.X - Polynomial.C z)
  have hP : algebraMap F[X] (RatFunc F) P =
      (∏ z ∈ S, (RatFunc.X - RatFunc.C z)) * ∑ y ∈ S, RatFunc.C (d y) / (RatFunc.X - RatFunc.C y) := by
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [← Finset.mul_prod_erase S _ hy]
    simp only [map_mul, map_prod, map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
    field_simp [RatFunc.X_sub_C_ne_zero y]
  have hP0 : P = 0 := by
    apply RatFunc.algebraMap_injective F
    rw [hP, h, mul_zero, map_zero]
  -- and at `y`, only the `y`-th term survives
  intro y hy
  have h_eval := congrArg (Polynomial.eval y) hP0
  rw [eval_zero, eval_finsetSum, Finset.sum_eq_single y] at h_eval
  · simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X] at h_eval
    refine (mul_eq_zero.mp h_eval).resolve_right ?_
    exact Finset.prod_ne_zero_iff.mpr fun z hz => sub_ne_zero.mpr (Finset.ne_of_mem_erase hz).symm
  · intro z hz hzy
    simp only [eval_mul, eval_prod, eval_sub, eval_X, eval_C]
    rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hzy, hy⟩) (sub_self y), mul_zero]
  · intro h; exact absurd hy h

/-- Group a sum of simple fractions by pole. -/
theorem sum_div_eq_sum_poles {n : ℕ} (S : Finset F) (g : Fin n → F) (w : Fin n → F) (hg : ∀ i, g i ∈ S) :
    ∑ i, RatFunc.C (w i) / (RatFunc.X - RatFunc.C (g i)) =
      ∑ y ∈ S, RatFunc.C (∑ i ∈ Finset.univ.filter (fun i => g i = y), w i) / (RatFunc.X - RatFunc.C y) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := g) (fun i _ => hg i)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

/-- The logUp statement, as an identity of rational functions. -/
theorem logUp_iff {n l : ℕ} (t m : Fin n → F) (f : Fin l → F) :
    ∑ i, RatFunc.C (m i) / (RatFunc.X - RatFunc.C (t i)) = ∑ j, (RatFunc.X - RatFunc.C (f j))⁻¹ ↔
      ∀ y, ((Finset.univ.filter fun j => f j = y).card : F) =
        ∑ i ∈ Finset.univ.filter (fun i => t i = y), m i := by
  set S := Finset.univ.image t ∪ Finset.univ.image f
  have ht : ∀ i, t i ∈ S := fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem t (Finset.mem_univ i))
  have hf : ∀ j, f j ∈ S := fun j => Finset.mem_union_right _ (Finset.mem_image_of_mem f (Finset.mem_univ j))
  have h_one : ∑ j, (RatFunc.X - RatFunc.C (f j))⁻¹ =
      ∑ j, RatFunc.C (1 : F) / (RatFunc.X - RatFunc.C (f j)) := by simp
  rw [h_one, sum_div_eq_sum_poles S t m ht, sum_div_eq_sum_poles S f (fun _ => 1) hf, ← sub_eq_zero,
    ← Finset.sum_sub_distrib]
  simp only [← sub_div, ← map_sub, Finset.sum_const, nsmul_eq_mul, mul_one]
  constructor
  · intro h y
    by_cases hy : y ∈ S
    · exact (sub_eq_zero.mp (eq_zero_of_sum_div_eq_zero S _ h y hy)).symm
    · have h_t : Finset.univ.filter (fun i => t i = y) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun i _ hi => hy (hi ▸ ht i)
      have h_f : Finset.univ.filter (fun j => f j = y) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun j _ hj => hy (hj ▸ hf j)
      simp [h_t, h_f]
  · intro h
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [h y, sub_self, map_zero, zero_div]

/-- Every value is looked up as often as the table's multiplicities for it add up to. -/
@[reducible]
def interface (n l : ℕ) : Interface F where
  input := ((Vector F n × Vector F n) × Vector F l) × F
  inputCType := ((.natives n ×ᵗ .natives n) ×ᵗ .natives l) ×ᵗ .native
  output := Unit
  outputCType := .unit
  Spec := fun (((t, m), f), _) _ => ∀ y,
    ((Finset.univ.filter fun j : Fin l => f[j] = y).card : F) = ∑ i ∈ Finset.univ.filter (fun i : Fin n => t[i] = y), m[i]
  ProverAssumptions := fun (((t, m), f), α) => (∀ y,
    ((Finset.univ.filter fun j : Fin l => f[j] = y).card : F) = ∑ i ∈ Finset.univ.filter (fun i : Fin n => t[i] = y), m[i]) ∧
    (∀ i : Fin n, α ≠ t[i]) ∧ ∀ j : Fin l, α ≠ f[j]

/-- `∑ m i / (X - t i) - ∑ 1 / (X - f j)`, in the committed values `t ++ (m ++ f)`. -/
def expr (n l : ℕ) : RExpr F (n + (n + l)) :=
  .sum n (fun i => .leaf (Fin.natAdd n (Fin.castAdd l i)) / (.X - .leaf (Fin.castAdd (n + l) i))) -
    .sum l (fun j => .const 1 / (.X - .leaf (Fin.natAdd n (Fin.natAdd n j))))

variable {B : Backend} [Field B.Native] [DecidableEq B.Native]
  (identity : ∀ {k : ℕ} (e : RExpr B.Native k), Impl B (Identity.interface e))

def impl (n l : ℕ) : Impl B (interface n l) where
  main | (((t, m), f), α) => identity (expr n l) (t ++ (m ++ f), α)
  spatial := by
    intro (((t, m), f), α) s h
    obtain ⟨⟨⟨h_t, h_m⟩, h_f⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left
      fun h => (Backend.footprintT_ctypeProd_subset.mp h).imp_left Backend.footprintT_ctypeProd_subset.mp
    simp only [circuit_norm]
    exact ⟨Backend.footprintT_ctypeProd_subset.mpr ⟨Identity.footprintT_append_subset
      h_t (Identity.footprintT_append_subset h_m h_f), h_α⟩, fun _ _ => Set.empty_subset _⟩
  soundness := by
    intro s env (((t, m), f), α) _ h
    simp only [circuit_norm] at h ⊢
    have h := h (by simp [expr])
    simp [expr, sub_eq_zero] at h
    simpa using (logUp_iff _ _ _).mp h
  completeness := by
    intro s env (((t, m), f), α) _ h_prover
    simp only [circuit_norm] at h_prover ⊢
    obtain ⟨h_spec, h_t, h_f⟩ := h_prover
    have h := (logUp_iff (fun i => B.eval env t[i]) (fun i => B.eval env m[i]) (fun j => B.eval env f[j])).mpr
      (by simpa using h_spec)
    refine ⟨by simp [expr], by simpa [expr, sub_eq_zero] using h, ?_⟩
    simp_all [expr, sub_eq_zero]

end LogUp
end Clean2
