/-
A grand-product permutation check: `b` is a permutation of `a`, with one challenge `α`.

The circuit keeps a running product `z`, from `z = 1`, through `z' * (α - b i) = z * (α - a i)`, and
asserts that it ends at `1`. The honest prover sets `z' = z * (α - a i) / (α - b i)`, so it is the
cells `z` that depend on the challenge.

- Pointwise, with no case split on the challenge: the constraints imply
  `∏ (α - a i) = ∏ (α - b i)`. In the cross-multiplied form a denominator that vanishes does not
  break the argument, it only makes the last step say `0 = 0`.
- Symbolically: `∏ (X - a i) = ∏ (X - b i)` in `F[X]` means that `a` and `b` have the same roots,
  with multiplicity, so they are the same multiset.
- The polynomial has degree at most `n`: a false claim is accepted at no more than `n`
  challenges, which is a soundness error of `n / |F|`.
- Completeness needs the challenge to avoid every `b i`: the honest prover divides by `α - b i`.
  That is a separate error of at most `n / |F|`, and it is the only place where a "bad"
  challenge appears.
-/
module

public import Clean2.Challenge.Basic
public import Clean2.Functionalities.Arith
public import Clean2.Backends.R1CS
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

namespace Clean2
open Polynomial

namespace GrandProduct
variable {Native : Type} [Field Native]

/-- The entries of a vector, as a multiset. -/
def elems {n : ℕ} (v : Vector Native n) : Multiset Native := Finset.univ.val.map fun i : Fin n => v[i]

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
theorem prod_eq_of_elems_eq {n : ℕ} {a b : Vector Native n} (h : elems a = elems b) (α : Native) :
    ∏ i : Fin n, (α - a[i]) = ∏ i : Fin n, (α - b[i]) := by
  rw [Finset.prod_eq_multiset_prod, Finset.prod_eq_multiset_prod]
  have h := congrArg (fun m => (m.map fun x => α - x).prod) h
  simp only [elems, Multiset.map_map] at h
  exact h

/-- The check: `b` is a permutation of `a`. -/
@[reducible]
noncomputable def check (n : ℕ) : ChallengeCheck Native where
  Phase1 := Vector Native n × Vector Native n
  phase1CType := .natives n ×ᵗ .natives n
  Statement := fun (a, b) => elems a = elems b
  poly := fun (a, b) => poly a b
  symbolic := fun (_, _) _ h => elems_eq_of_poly_eq_zero h
  ProverAssumptions := fun (a, b) α => elems a = elems b ∧ ∀ i : Fin n, α ≠ b[i]

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

/-- The grand-product check, for every length `n`. -/
noncomputable def impl (n : ℕ) : Impl B (check n).interface where
  main | ((a, b), α) => do
    let one ← arith (.const 1) ()
    let z ← loop arith n α (fun i => a[i]) (fun i => b[i]) one
    arith .mulEq (z, one, one)
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
    simp only [circuit_norm] at h ⊢
    obtain ⟨h_one, h_loop, h_end⟩ := h
    have h_val := loop_sound arith n α (fun i => a[i]) (fun i => b[i]) _ _ env h_loop
    rw [eval_poly]
    simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h_val h_end ⊢
    rw [h_one] at h_end h_val
    linear_combination (-1 : B.Native) * h_val + (∏ i : Fin n, (B.eval env α - B.eval env b[(i : ℕ)])) * h_end
  completeness := by
    intro s env ((a, b), α) h h_prover
    simp only [circuit_norm] at h h_prover ⊢
    obtain ⟨h_one, h_loop⟩ := h
    obtain ⟨h_perm, h_avoid⟩ := h_prover
    simp only [Fin.getElem_fin, Vector.getElem_map] at h_avoid
    obtain ⟨h_loop', h_inv⟩ := loop_complete arith n α (fun i => a[i]) (fun i => b[i]) _ _ env h_avoid h_loop
    refine ⟨h_loop', ?_⟩
    have h_prod := prod_eq_of_elems_eq h_perm (B.eval env α)
    have h_ne : ∏ i : Fin n, (B.eval env α - B.eval env b[(i : ℕ)]) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => sub_ne_zero.mpr (h_avoid i)
    simp only [circuit_norm, Fin.getElem_fin, Vector.getElem_map] at h_prod h_inv ⊢
    rw [h_one] at h_inv ⊢
    rw [mul_one]
    apply mul_right_cancel₀ h_ne
    linear_combination h_inv + h_prod

/-- **Soundness error.** If `b` is not a permutation of `a`, the prover is accepted at no more
than `n` challenges, on any backend: a soundness error of `n / |F|`. -/
theorem soundness_error (n : ℕ) (a b : Vector B.Native n) (h : elems a ≠ elems b) :
    {α | ChallengeCheck.Accepts (impl arith n) (a, b) α}.ncard ≤ n :=
  (ChallengeCheck.soundness_error (impl arith n) (a, b) trivial h).trans (natDegree_poly_le a b)

/-- **Completeness error.** If `b` is a permutation of `a`, the honest prover only fails at
challenges that hit an entry of `b`, which are at most `n`: a completeness error of `n / |F|`.
Stated as: at every challenge outside the entries of `b`, an honest assignment is accepted. -/
theorem completeness_of_avoids (n : ℕ) (a b : Vector B.Native n) (h : elems a = elems b) (α : B.Native)
    (h_avoid : α ∉ elems b) (s : B.State) (env₀ : B.Cell → B.Native)
    (input : (check n).interface.Input B.Var) (h_in : B.footprintT input ⊆ B.Alloc s)
    (h_valid : (check n).interface.inputCType.Valid (B.evalT env₀ input))
    (h_decode : (check n).interface.inputCType.decode (B.evalT env₀ input) = ((a, b), α)) :
    ∃ env, (∀ c ∈ B.Alloc s, env c = env₀ c) ∧ (((impl arith n).main input).operations s).ConstraintsHold env s :=
  ChallengeCheck.completeness (impl arith n) (a, b) α s env₀ input h_in h_valid h_decode
    ⟨h, fun i h_eq => h_avoid (h_eq ▸ Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩)⟩

omit [Field Native] in
theorem ncard_elems_le {n : ℕ} (b : Vector Native n) : {α | α ∈ elems b}.ncard ≤ n := by
  classical
  have h : {α | α ∈ elems b} = ↑(elems b).toFinset := by ext; simp
  rw [h, Set.ncard_coe_finset]
  exact (Multiset.toFinset_card_le _).trans (by simp [elems])

end GrandProduct

/-- On R1CS. -/
noncomputable def grandProductR1CS {F : Type} [Field F] (n : ℕ) :
    Impl (R1CS F) (GrandProduct.check (Native := F) n).interface :=
  GrandProduct.impl R1CS.arith n

end Clean2
