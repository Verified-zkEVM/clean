/-
The linear heap model shared by the expression and R1CS backends: cells are `ℕ`, the
allocation state is the next free cell, and a witness operation owns exactly that cell.
The frame laws for such a witness are proved here once, over any variable language.
-/
module

public import Clean2.Core

@[expose] public section

namespace Clean2.Linear
variable {F : Type} [Field F]

/-- The cells allocated at state `s`. -/
def Alloc (s : ℕ) : Set ℕ := {c | c < s}

@[circuit_norm] theorem mem_alloc {c s : ℕ} : c ∈ Alloc s ↔ c < s := Iff.rfl

theorem alloc_mono_succ (s : ℕ) : Alloc s ⊆ Alloc (s + 1) := fun _ hc => Nat.lt_succ_of_lt hc

theorem singleton_subset_alloc_succ (s : ℕ) : ({s} : Set ℕ) ⊆ Alloc (s + 1) := by
  intro c hc; rw [Set.mem_singleton_iff] at hc; exact hc ▸ Nat.lt_succ_self s

theorem disjoint_singleton_alloc (s : ℕ) : Disjoint ({s} : Set ℕ) (Alloc s) := by
  rw [Set.disjoint_singleton_left]; exact Nat.lt_irrefl s

section Witness
variable {V : Type} (eval : (ℕ → F) → V → F) (footprint : V → Set ℕ)

/-- The cells a witness computation reads: the footprints of its input variables. -/
def witnessReads {m : ℕ} (vars : Vector V m) : Set ℕ := ⋃ i : Fin m, footprint vars[i]

/-- The honest prover assigns the fresh cell the computed value. -/
def WitnessHonest (env : ℕ → F) (s : ℕ) {m : ℕ} (vars : Vector V m) (f : Vector F m → F) : Prop :=
  env s = f (vars.map (eval env))

variable (eval_frame : ∀ (env env' : ℕ → F) (v : V), (∀ c ∈ footprint v, env c = env' c) → eval env v = eval env' v)
include eval_frame

omit [Field F] in
theorem map_eval_congr {m : ℕ} (vars : Vector V m) (env env' : ℕ → F)
    (h : ∀ c ∈ witnessReads footprint vars, env c = env' c) :
    vars.map (eval env) = vars.map (eval env') := by
  ext i hi
  simp only [Vector.getElem_map]
  exact eval_frame env env' _ fun c hc => h c (Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hc⟩)

omit [Field F] in
theorem witnessHonest_frame {env env' : ℕ → F} {s m : ℕ} {vars : Vector V m} {f : Vector F m → F}
    (h_reads : witnessReads footprint vars ⊆ Alloc s) (h : WitnessHonest eval env s vars f)
    (h_agree : ∀ c ∈ Alloc (s + 1), env c = env' c) : WitnessHonest eval env' s vars f := by
  unfold WitnessHonest at *
  rw [← h_agree s (Nat.lt_succ_self s), h,
    map_eval_congr eval footprint eval_frame vars env env' fun c hc => h_agree c (alloc_mono_succ s (h_reads hc))]

omit [Field F] in
theorem witnessHonest_extend (env₀ : ℕ → F) {s m : ℕ} {vars : Vector V m} {f : Vector F m → F}
    (h_reads : witnessReads footprint vars ⊆ Alloc s) :
    ∃ env, (∀ c ∈ Alloc s, env c = env₀ c) ∧ WitnessHonest eval env s vars f := by
  refine ⟨Function.update env₀ s (f (vars.map (eval env₀))), fun c hc => ?_, ?_⟩
  · exact Function.update_of_ne (Nat.ne_of_lt hc) _ _
  · unfold WitnessHonest
    rw [Function.update_self]
    congr 1
    exact map_eval_congr eval footprint eval_frame vars _ _ fun c hc =>
      (Function.update_of_ne (Nat.ne_of_lt (h_reads hc)) _ _).symm

end Witness
end Clean2.Linear
