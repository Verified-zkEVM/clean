/-
Proof rules for the loops of the circuit monad, `Circuit.foldr` and `Circuit.mapFin`: one rule
per proof obligation of an `Impl` (consistency, soundness, completeness, spatial), each taking
the corresponding obligation of one iteration as a hypothesis. A gadget written as a loop
proves its obligations by applying these to the body, instead of by its own induction.

Soundness of a `foldr` goes through an invariant `I i acc`, meant to hold once the iterations
`n - 1, …, i` have run; soundness of a `mapFin` through a predicate `P i` on the `i`-th result.
-/
module

public import Clean2.Core.Circuit

@[expose] public section

namespace Clean2
variable {B : Backend}

theorem Backend.footprintT_push {n : ℕ} (xs : Vector B.Var n) (x : B.Var) :
    B.footprintT (M := natives (n + 1)) (xs.push x) = B.footprintT (M := natives n) xs ∪ B.footprint x := by
  ext c
  simp only [footprintT_natives, Set.mem_iUnion, Set.mem_union, Fin.getElem_fin]
  constructor
  · rintro ⟨i, hi⟩
    rw [Vector.getElem_push] at hi
    split at hi
    · exact Or.inl ⟨⟨i, ‹_›⟩, hi⟩
    · exact Or.inr hi
  · rintro (⟨i, hi⟩ | h)
    · exact ⟨i.castSucc, by rw [Vector.getElem_push]; simp only [Fin.val_castSucc, i.isLt, dite_true]; exact hi⟩
    · exact ⟨Fin.last n, by rw [Vector.getElem_push]; simp only [Fin.val_last, lt_irrefl, dite_false]; exact h⟩

namespace Circuit

/-! ### `foldr` -/

section Foldr
variable {α : Type} {n : ℕ}

theorem foldr_consistent (f : Fin n → α → Circuit B α) (z : α) (s : B.State)
    (h : ∀ i acc s, ((f i acc).operations s).Consistent s) :
    ((foldr n f z).operations s).Consistent s := by
  induction n generalizing z s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm]
    exact ⟨ih (fun i => f i.succ) z s (fun i => h i.succ), h 0 _ _⟩

theorem foldr_sound (f : Fin n → α → Circuit B α) (z : α) (s : B.State) (env : B.Cell → B.Native)
    (I : ℕ → α → Prop) (h_init : I n z)
    (h_step : ∀ (i : Fin n) acc s, I (i + 1) acc →
      ((f i acc).operations s).SoundnessHold env s → I i ((f i acc).output s))
    (h : ((foldr n f z).operations s).SoundnessHold env s) :
    I 0 ((foldr n f z).output s) := by
  induction n generalizing z s I with
  | zero =>
    simp only [circuit_norm]
    exact h_init
  | succ n ih =>
    simp only [circuit_norm] at h ⊢
    exact h_step 0 _ _
      (ih (fun i => f i.succ) z s (fun i => I (i + 1)) h_init (fun i => h_step i.succ) h.1) h.2

theorem foldr_complete (f : Fin n → α → Circuit B α) (z : α) (s : B.State) (env : B.Cell → B.Native)
    (h_step : ∀ i acc s, ((f i acc).operations s).HonestCompleteness env s →
      ((f i acc).operations s).CompletenessHold env s)
    (h : ((foldr n f z).operations s).HonestCompleteness env s) :
    ((foldr n f z).operations s).CompletenessHold env s := by
  induction n generalizing z s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm] at h ⊢
    exact ⟨ih (fun i => f i.succ) z s (fun i => h_step i.succ) h.1, h_step 0 _ _ h.2⟩

/-- The spatial rule. The body runs at later states, where the heap has grown from the initial
one, and gets the accumulator; it must deliver its result. -/
theorem foldr_local {M : TypeMap} [ProvableType M] (f : Fin n → M B.Var → Circuit B (M B.Var)) (z : M B.Var)
    (s₀ : B.State) (K : B.State → Prop)
    (h_consistent : ∀ i acc s, ((f i acc).operations s).Consistent s)
    (h_step : ∀ i acc s, B.Alloc s₀ ⊆ B.Alloc s → B.footprintT acc ⊆ B.Alloc s →
      ((f i acc).operations s).LocalHold s fun s' => B.footprintT ((f i acc).output s) ⊆ B.Alloc s')
    (h_z : B.footprintT z ⊆ B.Alloc s₀)
    (h_K : B.footprintT ((foldr n f z).output s₀) ⊆ B.Alloc (((foldr n f z).operations s₀).advance s₀) →
      K (((foldr n f z).operations s₀).advance s₀)) :
    ((foldr n f z).operations s₀).LocalHold s₀ K := by
  induction n generalizing z K with
  | zero =>
    simp only [circuit_norm] at h_K ⊢
    exact h_K h_z
  | succ n ih =>
    have hc := foldr_consistent (fun i => f i.succ) z s₀ (fun i => h_consistent i.succ)
    have h_post := (Ops.local_of_localHold hc
      (ih (fun i => f i.succ) z
        (fun s' => B.footprintT ((foldr n (fun i => f i.succ) z).output s₀) ⊆ B.Alloc s')
        (fun i => h_consistent i.succ) (fun i => h_step i.succ) h_z id)).2
    have h_mono := Ops.alloc_mono hc
    simp only [circuit_norm] at h_K ⊢
    rw [Ops.localHold_append_of_consistent hc]
    refine ih (fun i => f i.succ) z _ (fun i => h_consistent i.succ) (fun i => h_step i.succ) h_z fun _ => ?_
    exact Ops.localHold_mono_of_consistent (h_consistent 0 _ _) (h_step 0 _ _ h_mono h_post) h_K

/-- The allocation state after a loop whose every iteration advances the state the same way:
the iterate. This is how a loop's cost is computed. -/
theorem foldr_advance (f : Fin n → α → Circuit B α) (z : α) (g : B.State → B.State)
    (h : ∀ i acc s, ((f i acc).operations s).advance s = g s) (s : B.State) :
    ((foldr n f z).operations s).advance s = g^[n] s := by
  induction n generalizing z s with
  | zero => simp only [circuit_norm, Function.iterate_zero, id]
  | succ n ih =>
    simp only [circuit_norm, Function.iterate_succ_apply']
    rw [h, ih (fun i => f i.succ) z (fun i => h i.succ) s]

/-- Every native operation of a loop is one of the body's. -/
theorem foldr_flat (f : Fin n → α → Circuit B α) (z : α) (P : B.Op → Prop)
    (h : ∀ i acc s, ∀ op ∈ ((f i acc).operations s).toFlat, P op) (s : B.State) :
    ∀ op ∈ ((foldr n f z).operations s).toFlat, P op := by
  induction n generalizing z s with
  | zero => simp only [circuit_norm, Ops.toFlat, List.not_mem_nil, false_implies, implies_true]
  | succ n ih =>
    simp only [circuit_norm, Ops.toFlat_append, List.mem_append]
    rintro op (hop | hop)
    · exact ih (fun i => f i.succ) z (fun i => h i.succ) s op hop
    · exact h 0 _ _ op hop

/-- The number of native operations of a loop whose every iteration has the same number. -/
theorem foldr_flat_length (f : Fin n → α → Circuit B α) (z : α) (k : ℕ)
    (h : ∀ i acc s, ((f i acc).operations s).toFlat.length = k) (s : B.State) :
    ((foldr n f z).operations s).toFlat.length = n * k := by
  induction n generalizing z s with
  | zero => simp only [circuit_norm, Ops.toFlat, List.length_nil, Nat.zero_mul]
  | succ n ih =>
    simp only [circuit_norm, Ops.toFlat_append, List.length_append]
    rw [h, ih (fun i => f i.succ) z (fun i => h i.succ) s, Nat.succ_mul]

end Foldr

/-! ### `mapFin` -/

section MapFin
variable {n : ℕ}

theorem mapFin_consistent (f : Fin n → Circuit B B.Var) (s : B.State)
    (h : ∀ i s, ((f i).operations s).Consistent s) :
    ((mapFin n f).operations s).Consistent s := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm]
    exact ⟨ih (fun i => f i.castSucc) s (fun i => h i.castSucc), h (Fin.last n) _⟩

theorem mapFin_sound (f : Fin n → Circuit B B.Var) (s : B.State) (env : B.Cell → B.Native)
    (P : Fin n → B.Native → Prop)
    (h_step : ∀ i s, ((f i).operations s).SoundnessHold env s → P i (B.eval env ((f i).output s)))
    (h : ((mapFin n f).operations s).SoundnessHold env s) :
    ∀ (i : ℕ) (hi : i < n), P ⟨i, hi⟩ (B.eval env ((mapFin n f).output s)[i]) := by
  induction n generalizing s with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    simp only [circuit_norm] at h ⊢
    intro i hi
    rw [Vector.getElem_push]
    split
    · exact ih (fun i => f i.castSucc) s (fun i => P i.castSucc) (fun i => h_step i.castSucc) h.1 i ‹_›
    · rw [show (⟨i, hi⟩ : Fin (n + 1)) = Fin.last n from Fin.ext (by simp only [Fin.val_last]; omega)]
      exact h_step (Fin.last n) _ h.2

/-- What the honest prover knows about each result: the prover-side counterpart of
`mapFin_sound`. -/
theorem mapFin_honest (f : Fin n → Circuit B B.Var) (s : B.State) (env : B.Cell → B.Native)
    (P : Fin n → B.Native → Prop)
    (h_step : ∀ i s, ((f i).operations s).HonestCompleteness env s → P i (B.eval env ((f i).output s)))
    (h : ((mapFin n f).operations s).HonestCompleteness env s) :
    ∀ (i : ℕ) (hi : i < n), P ⟨i, hi⟩ (B.eval env ((mapFin n f).output s)[i]) := by
  induction n generalizing s with
  | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    simp only [circuit_norm] at h ⊢
    intro i hi
    rw [Vector.getElem_push]
    split
    · exact ih (fun i => f i.castSucc) s (fun i => P i.castSucc) (fun i => h_step i.castSucc) h.1 i ‹_›
    · rw [show (⟨i, hi⟩ : Fin (n + 1)) = Fin.last n from Fin.ext (by simp only [Fin.val_last]; omega)]
      exact h_step (Fin.last n) _ h.2

theorem mapFin_complete (f : Fin n → Circuit B B.Var) (s : B.State) (env : B.Cell → B.Native)
    (h_step : ∀ i s, ((f i).operations s).HonestCompleteness env s → ((f i).operations s).CompletenessHold env s)
    (h : ((mapFin n f).operations s).HonestCompleteness env s) :
    ((mapFin n f).operations s).CompletenessHold env s := by
  induction n generalizing s with
  | zero => simp only [circuit_norm]
  | succ n ih =>
    simp only [circuit_norm] at h ⊢
    exact ⟨ih (fun i => f i.castSucc) s (fun i => h_step i.castSucc) h.1, h_step (Fin.last n) _ h.2⟩

theorem mapFin_local (f : Fin n → Circuit B B.Var) (s₀ : B.State) (K : B.State → Prop)
    (h_consistent : ∀ i s, ((f i).operations s).Consistent s)
    (h_step : ∀ i s, B.Alloc s₀ ⊆ B.Alloc s →
      ((f i).operations s).LocalHold s fun s' => B.footprint ((f i).output s) ⊆ B.Alloc s')
    (h_K : B.footprintT (M := natives n) ((mapFin n f).output s₀) ⊆
        B.Alloc (((mapFin n f).operations s₀).advance s₀) →
      K (((mapFin n f).operations s₀).advance s₀)) :
    ((mapFin n f).operations s₀).LocalHold s₀ K := by
  induction n generalizing K with
  | zero =>
    simp only [circuit_norm] at h_K ⊢
    exact h_K (Set.empty_subset _)
  | succ n ih =>
    have hc := mapFin_consistent (fun i => f i.castSucc) s₀ (fun i => h_consistent i.castSucc)
    have h_mono := Ops.alloc_mono hc
    simp only [circuit_norm] at h_K ⊢
    rw [Ops.localHold_append_of_consistent hc]
    refine ih (fun i => f i.castSucc) _ (fun i => h_consistent i.castSucc) (fun i => h_step i.castSucc) fun h_xs => ?_
    have hc' := h_consistent (Fin.last n) (((mapFin n fun i => f i.castSucc).operations s₀).advance s₀)
    refine Ops.localHold_mono_of_consistent hc' (h_step (Fin.last n) _ h_mono) fun h_x => h_K ?_
    rw [Backend.footprintT_push]
    exact Set.union_subset (h_xs.trans (Ops.alloc_mono hc')) h_x

theorem mapFin_advance (f : Fin n → Circuit B B.Var) (g : B.State → B.State)
    (h : ∀ i s, ((f i).operations s).advance s = g s) (s : B.State) :
    ((mapFin n f).operations s).advance s = g^[n] s := by
  induction n generalizing s with
  | zero => simp only [circuit_norm, Function.iterate_zero, id]
  | succ n ih =>
    simp only [circuit_norm, Function.iterate_succ_apply']
    rw [h, ih (fun i => f i.castSucc) (fun i => h i.castSucc) s]

end MapFin
end Circuit

/-- `(· + k)^[n] s = s + n * k`: the cost of a loop of `n` iterations of `k` cells each. -/
theorem iterate_add_const (k n s : ℕ) : (· + k)^[n] s = s + n * k := by
  induction n generalizing s with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply, ih, Nat.succ_mul]; omega

end Clean2
