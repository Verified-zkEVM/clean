/-
A permutation check with a hand-written argument and its own rare event.

The circuit keeps a running product `z' * (α - b i) = z * (α - a i)` from `z = 1` and asserts that
it ends at `1`. Pointwise, cross-multiplied, the constraints give `∏ (α - a i) = ∏ (α - b i)` with
no case split on vanishing denominators, so the only bad challenges are the roots of
`∏ (X - a i) - ∏ (X - b i)`: at most `n`, half of what the generic quotient identity
(`PermutationQuotient`) pays for the same circuit shape. The price is the pointwise proof, which
the user writes. Same interface, same spec: a parent cannot tell the two apart, except by their
cost and error measures.
-/
module

public import Clean2.Challenge.Variants.Permutation
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

namespace Clean2
open Polynomial

namespace PermutationRunning
open Permutation
variable {Native : Type} [Field Native]

/-- `∏ (X - a i) - ∏ (X - b i)`, which vanishes exactly when `a` and `b` are the same multiset. -/
noncomputable def poly {n : ℕ} (a b : Vector Native n) : Native[X] :=
  ∏ i : Fin n, (X - C a[i]) - ∏ i : Fin n, (X - C b[i])

theorem eval_poly {n : ℕ} (a b : Vector Native n) (α : Native) :
    (poly a b).eval α = ∏ i : Fin n, (α - a[i]) - ∏ i : Fin n, (α - b[i]) := by
  simp [poly, eval_prod]

theorem prod_X_sub_C_eq {n : ℕ} (v : Vector Native n) :
    ∏ i : Fin n, (X - C v[i]) = ((elems v).map fun x => X - C x).prod := by
  rw [Finset.prod_eq_multiset_prod, elems, Multiset.map_map]
  rfl

/-- The symbolic argument: equal products of linear factors have equal roots. -/
theorem elems_eq_of_poly_eq_zero {n : ℕ} {a b : Vector Native n} (h : poly a b = 0) : elems a = elems b := by
  rw [poly, sub_eq_zero, prod_X_sub_C_eq, prod_X_sub_C_eq] at h
  have h := congrArg roots h
  rwa [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at h

theorem natDegree_poly_le {n : ℕ} (a b : Vector Native n) : (poly a b).natDegree ≤ n := by
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_) <;>
  · rw [prod_X_sub_C_eq, natDegree_multiset_prod_X_sub_C_eq_card]
    simp [elems]

/-- Equal multisets have equal products of `α - ·`. -/
theorem prod_sub_eq_of_elems_eq {n : ℕ} {a b : Vector Native n} (h : elems a = elems b) (α : Native) :
    ∏ i : Fin n, (α - a[i]) = ∏ i : Fin n, (α - b[i]) := by
  exact Permutation.prod_eq_of_elems_eq h (fun x => α - x)

/-- The polynomial identity holds for permutations. -/
theorem poly_eq_zero_of_elems_eq {n : ℕ} {a b : Vector Native n} (h : elems a = elems b) : poly a b = 0 := by
  rw [poly, sub_eq_zero]
  exact Permutation.prod_eq_of_elems_eq h (fun x => X - C x)

variable {B : Backend} [Field B.Native] (arith : ∀ n, Impl B (Arith.interface n))

/-- One step of the running product: `z' * (α - b) = z * (α - a)`. -/
@[circuit_norm]
def step (α a b z : B.Var) : Circuit B B.Var := do
  let num ← arith .sub (α, a)
  let den ← arith .sub (α, b)
  let t ← arith .mul (z, num)
  let z' ← arith (.witness nativePair fun (t, d) => t / d) (t, den)
  arith .mulEq (z', den, t)
  return z'

/-! The loop, by induction on its bound, over any vectors of variables and any initial value. -/
section Loop
variable (n : ℕ) (α : B.Var) (a b : Fin n → B.Var) (z : B.Var)

/-- The running product. -/
@[reducible, circuit_norm]
def loop : Circuit B B.Var := Circuit.foldr n (fun i z => step arith α (a i) (b i) z) z

theorem loop_consistent (s : B.State) : ((loop arith n α a b z).operations s).Consistent s := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm]
    exact ih _ _ s

/-- Soundness of the loop, cross-multiplied: no denominator needs to be non-zero. -/
theorem loop_sound (s : B.State) (env : B.Cell → B.Native)
    (h : ((loop arith n α a b z).operations s).SoundnessHold env s) :
    B.eval env ((loop arith n α a b z).output s) * ∏ i : Fin n, (B.eval env α - B.eval env (b i)) =
      B.eval env z * ∏ i : Fin n, (B.eval env α - B.eval env (a i)) := by
  induction n generalizing s with
  | zero => simp only [circuit_norm, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  | succ n ih =>
    simp only [circuit_norm] at h ih ⊢
    obtain ⟨h_loop, h_num, h_den, h_t, h_step⟩ := h
    have h_acc := ih (fun i => a i.succ) (fun i => b i.succ) s h_loop
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    rw [h_den, h_t, h_num] at h_step
    linear_combination (∏ i : Fin n, (B.eval env α - B.eval env (b i.succ))) * h_step +
      (B.eval env α - B.eval env (a 0)) * h_acc

/-- Completeness of the loop: if the challenge avoids every `b i`, the honest running product
satisfies the constraints, and it is the quotient of the two products. -/
theorem loop_complete (s : B.State) (env : B.Cell → B.Native)
    (h_avoid : ∀ i, B.eval env α ≠ B.eval env (b i))
    (h : ((loop arith n α a b z).operations s).HonestCompleteness env s) :
    ((loop arith n α a b z).operations s).CompletenessHold env s ∧
      B.eval env ((loop arith n α a b z).output s) * ∏ i : Fin n, (B.eval env α - B.eval env (b i)) =
        B.eval env z * ∏ i : Fin n, (B.eval env α - B.eval env (a i)) := by
  induction n generalizing s with
  | zero => simp only [circuit_norm, Finset.univ_eq_empty, Finset.prod_empty, mul_one, and_self]
  | succ n ih =>
    simp only [circuit_norm] at h ih ⊢
    obtain ⟨h_loop, h_num, h_den, h_t, h_z'⟩ := h
    obtain ⟨h_loop', h_acc⟩ := ih (fun i => a i.succ) (fun i => b i.succ) s (fun i => h_avoid i.succ) h_loop
    have h_ne : B.eval env α - B.eval env (b 0) ≠ 0 := sub_ne_zero.mpr (h_avoid 0)
    refine ⟨⟨h_loop', ?_⟩, ?_⟩
    · rw [h_z', h_den]
      exact div_mul_cancel₀ _ h_ne
    have h_mul := h_z'
    rw [h_den, h_t, h_num, eq_div_iff h_ne] at h_mul
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    linear_combination (∏ i : Fin n, (B.eval env α - B.eval env (b i.succ))) * h_mul +
      (B.eval env α - B.eval env (a 0)) * h_acc

/-- The spatial obligation of the loop, for any continuation. -/
theorem loop_local (s : B.State) (K : B.State → Prop)
    (h_α : B.footprint α ⊆ B.Alloc s) (h_a : ∀ i, B.footprint (a i) ⊆ B.Alloc s)
    (h_b : ∀ i, B.footprint (b i) ⊆ B.Alloc s) (h_z : B.footprint z ⊆ B.Alloc s)
    (h_K : B.footprint ((loop arith n α a b z).output s) ⊆
        B.Alloc (((loop arith n α a b z).operations s).advance s) →
      K (((loop arith n α a b z).operations s).advance s)) :
    ((loop arith n α a b z).operations s).LocalHold s K := by
  induction n generalizing s K with
  | zero =>
    simp only [circuit_norm] at h_K ⊢
    exact h_K h_z
  | succ n ih =>
    have h_a' : ∀ i : Fin n, B.footprint (a i.succ) ⊆ B.Alloc s := fun i => h_a i.succ
    have h_b' : ∀ i : Fin n, B.footprint (b i.succ) ⊆ B.Alloc s := fun i => h_b i.succ
    have hc := loop_consistent arith n α (fun i => a i.succ) (fun i => b i.succ) z s
    have h_post := (Ops.local_of_localHold hc
      (ih _ _ s (fun s' => B.footprint ((loop arith n α (fun i => a i.succ) (fun i => b i.succ) z).output s) ⊆ B.Alloc s')
        h_α h_a' h_b' h_z id)).2
    have h_mono := Ops.alloc_mono hc
    have h_a0 := h_a 0
    have h_b0 := h_b 0
    simp only [circuit_norm] at h_K hc ⊢
    rw [Ops.localHold_append_of_consistent hc]
    refine ih _ _ s _ h_α h_a' h_b' h_z fun _ => ?_
    simp only [circuit_norm, Set.union_subset_iff, Set.empty_subset]
    spatial_split

end Loop

/-- The bad challenges: `poly a b` is not zero, but vanishes there, for `a ++ b` given as one
vector. -/
noncomputable def Bad (n : ℕ) (v : Vector B.Native (n + n)) (x : B.Native) : Prop :=
  polyBad (poly (Vector.ofFn fun i : Fin n => v[Fin.castAdd n i]) (Vector.ofFn fun i : Fin n => v[Fin.natAdd n i])) x

theorem encard_bad_le (n : ℕ) (v : Vector B.Native (n + n)) : {x | Bad n v x}.encard ≤ n :=
  (encard_polyBad_le _).trans (Nat.cast_le.mpr (natDegree_poly_le _ _))

/-- The rare event. Its bound is `n`, the degree of `poly a b`: tighter than the `2n` of the
generic quotient identity. -/
noncomputable def event (n : ℕ) (a b : Vector B.Var n) (α : B.Var) : RareEvent B where
  m := n + n
  committed := a ++ b
  challenge := α
  Bad := Bad n
  bound := n
  encard_bad_le := encard_bad_le n

/-- The running product, with its own rare event. Implements the same interface as the generic
quotient identity (`PermutationQuotient.interface`): same spec, different circuit and bound. -/
noncomputable def impl (n : ℕ) : Impl B (PermutationQuotient.interface n) where
  main | ((a, b), α) => do
    let one ← arith (.const 1) ()
    let z ← loop arith n α (fun i => a[i]) (fun i => b[i]) one
    arith .mulEq (z, one, one)
    Circuit.assumeRare (event n a b α)
  consistent := by
    intro ((a, b), α) s
    simp only [circuit_norm]
    exact loop_consistent arith n _ _ _ _ _
  spatial := by
    intro ((a, b), α) s h
    obtain ⟨⟨h_a, h_b⟩, h_α⟩ := (Backend.footprintT_ctypeProd_subset.mp h).imp_left
      Backend.footprintT_ctypeProd_subset.mp
    have h_a : ∀ i : Fin n, B.footprint a[i] ⊆ B.Alloc s := fun i => Backend.footprint_getElem_subset h_a i i.isLt
    have h_b : ∀ i : Fin n, B.footprint b[i] ⊆ B.Alloc s := fun i => Backend.footprint_getElem_subset h_b i i.isLt
    simp only [circuit_norm] at h_α ⊢
    refine ⟨Set.empty_subset _, fun h_one h_mono => ?_⟩
    have hc := loop_consistent arith n α (fun i => a[i]) (fun i => b[i])
      ((arith (.const 1)).output () s) ((arith (.const 1)).advance () s)
    simp only [circuit_norm] at hc
    rw [Ops.localHold_append_of_consistent hc]
    have h_mono' := Ops.alloc_mono hc
    refine loop_local arith n α _ _ _ _ _ (h_α.trans h_mono) (fun i => (h_a i).trans h_mono)
      (fun i => (h_b i).trans h_mono) h_one fun h_z => ?_
    simp only [circuit_norm, Set.union_subset_iff] at h_z h_mono' ⊢
    spatial_split
  soundness := by
    intro s env ((a, b), α) _ h
    simp only [circuit_norm, event, Bad] at h ⊢
    obtain ⟨h_one, h_loop, h_end, h_rare⟩ := h
    have h_val := loop_sound arith n α (fun i => a[i]) (fun i => b[i]) _ _ env h_loop
    -- pointwise: the polynomial vanishes at the challenge
    have h_eval : (poly (a.map (B.eval env)) (b.map (B.eval env))).eval (B.eval env α) = 0 := by
      rw [eval_poly]
      simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h_val h_end ⊢
      rw [h_one] at h_end h_val
      linear_combination (-1 : B.Native) * h_val + (∏ i : Fin n, (B.eval env α - B.eval env b[(i : ℕ)])) * h_end
    -- and the challenge is not bad, so it is zero
    have h_ab : (Vector.ofFn fun i : Fin n => (Vector.map (B.eval env) (a ++ b))[Fin.castAdd n i]) = a.map (B.eval env) ∧
        (Vector.ofFn fun i : Fin n => (Vector.map (B.eval env) (a ++ b))[Fin.natAdd n i]) = b.map (B.eval env) := by
      constructor <;> ext i hi <;> simp
    rw [h_ab.1, h_ab.2] at h_rare
    exact elems_eq_of_poly_eq_zero (by_contra fun h0 => h_rare ⟨h0, h_eval⟩)
  completeness := by
    intro s env ((a, b), α) h h_prover
    simp only [circuit_norm, event, Bad] at h h_prover ⊢
    obtain ⟨h_one, h_loop⟩ := h
    obtain ⟨h_perm, h_avoid⟩ := h_prover
    have h_ab : (Vector.ofFn fun i : Fin n => (Vector.map (B.eval env) (a ++ b))[Fin.castAdd n i]) = a.map (B.eval env) ∧
        (Vector.ofFn fun i : Fin n => (Vector.map (B.eval env) (a ++ b))[Fin.natAdd n i]) = b.map (B.eval env) := by
      constructor <;> ext i hi <;> simp
    rw [h_ab.1, h_ab.2]
    simp only [Fin.getElem_fin, Vector.getElem_map] at h_avoid
    obtain ⟨h_loop', h_inv⟩ := loop_complete arith n α (fun i => a[i]) (fun i => b[i]) _ _ env h_avoid h_loop
    have h_prod := prod_sub_eq_of_elems_eq h_perm (B.eval env α)
    have h_ne : ∏ i : Fin n, (B.eval env α - B.eval env b[(i : ℕ)]) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (h_avoid i)
    refine ⟨h_loop', ?_, fun h_bad => h_bad.1 (poly_eq_zero_of_elems_eq h_perm)⟩
    simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h_prod h_inv ⊢
    rw [h_one] at h_inv ⊢
    rw [mul_one]
    apply mul_right_cancel₀ h_ne
    linear_combination h_inv + h_prod

end PermutationRunning
end Clean2
