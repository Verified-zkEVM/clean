/-
A `Backend` is the native set of a proof system: the things that are true "by definition of
the proof system", which every circuit ultimately reduces to.

Everything else (arithmetic, assertions, gadgets, ...) is a *functionality*: an interface
(`Clean2.Interface`) implemented on top of a backend (`Clean2.Impl`).

The backend also fixes the *heap model*: what a cell is, which cells a variable reads, and
how allocation states grow. The core never mentions cells; it only uses the frame laws below.
-/
module

public import Clean2.Core.Provable
public import Mathlib.Data.Set.Lattice

@[expose] public section

namespace Clean2

structure Backend where
  /--
    the native type of witness values contained in cells,
    it does not necessarily have to be a field, so that we can
    express SNARKs over integers, rationals, and so on
  -/
  Native : Type
  /-- the "physical" address of a concrete witness location -/
  Cell : Type
  /-- the type of variables that circuits manipulate and talk about -/
  Var : Type
  /--
    the meaning of a variable under an assignment of the cells: given an assignment from
    physical cells to native values, this function describes how variables are computed
  -/
  eval : (Cell → Native) → Var → Native

  /-- the cells a variable reads -/
  footprint : Var → Set Cell
  /-- `eval` only looks at the footprint -/
  eval_frame : ∀ (env env' : Cell → Native) (v : Var),
    (∀ c ∈ footprint v, env c = env' c) → eval env v = eval env' v

  /-- backend state -/
  State : Type
  /-- the cells allocated at a state; the "heap" -/
  Alloc : State → Set Cell

  /-- native operations -/
  Op : Type
  /-- what an operation does to the allocation state -/
  advance : Op → State → State
  /-- the allocation set is monotonic: Alloc set never decreases on `advance` -/
  alloc_mono : ∀ op s, Alloc s ⊆ Alloc (advance op s)
  /-- the cells an operation reads -/
  reads : Op → Set Cell
  /-- the cells an operation writes -/
  writes : Op → State → Set Cell
  /-- all operations must write only cells that they have allocated -/
  writes_fresh : ∀ op s,
    Disjoint (writes op s) (Alloc s) ∧
    writes op s ⊆ Alloc (advance op s)

  /-- verifier semantics: what it means for an operation, placed at a state, to hold -/
  Holds : (Cell → Native) → State → Op → Prop
  /-- prover semantics: what the honest prover does with the cells an operation owns -/
  Honest : (Cell → Native) → State → Op → Prop

  /-- frame: honesty of a well-formed op depends only on the heap after it -/
  honest_frame :
    ∀ (env env' : Cell → Native) s op,
      reads op ⊆ Alloc s →
      Honest env s op →
      (∀ c ∈ Alloc (advance op s), env c = env' c) →
      Honest env' s op
  /-- extension: a well-formed op can always be run honestly without touching the existing heap -/
  honest_extend : ∀ (env₀ : Cell → Native) s op, reads op ⊆ Alloc s →
    ∃ env, (∀ c ∈ Alloc s, env c = env₀ c) ∧ Honest env s op

namespace Backend
variable (B : Backend)

/-- Evaluate a container of variables to a container of values. -/
@[circuit_norm]
def evalT {M : TypeMap} [ProvableType M] (env : B.Cell → B.Native) (x : M B.Var) : M B.Native :=
  ProvableType.map (B.eval env) x

/-- The cells a container of variables reads. -/
def footprintT {M : TypeMap} [ProvableType M] (x : M B.Var) : Set B.Cell :=
  ⋃ i : Fin (size M), B.footprint (toElements x)[i]

variable {B}

theorem footprint_subset_footprintT {M : TypeMap} [ProvableType M] (x : M B.Var) (i : Fin (size M)) :
    B.footprint (toElements x)[i] ⊆ B.footprintT x :=
  Set.subset_iUnion (fun i : Fin (size M) => B.footprint (toElements x)[i]) i

theorem evalT_eq_fromElements {M : TypeMap} [ProvableType M] (env : B.Cell → B.Native) (x : M B.Var) :
    B.evalT env x = fromElements ((toElements x).map (B.eval env)) := by
  unfold evalT
  rw [← ProvableType.fromElements_toElements (ProvableType.map (B.eval env) x), ProvableType.toElements_map]

theorem evalT_frame {M : TypeMap} [ProvableType M] (env env' : B.Cell → B.Native) (x : M B.Var)
    (h : ∀ c ∈ B.footprintT x, env c = env' c) : B.evalT env x = B.evalT env' x := by
  unfold evalT
  rw [← ProvableType.fromElements_toElements (ProvableType.map (B.eval env) x),
    ← ProvableType.fromElements_toElements (ProvableType.map (B.eval env') x),
    ProvableType.toElements_map, ProvableType.toElements_map]
  congr 1
  ext i hi
  simp only [Vector.getElem_map]
  exact B.eval_frame env env' _ fun c hc => h c (footprint_subset_footprintT x ⟨i, hi⟩ hc)

@[circuit_norm]
theorem footprintT_native (x : native B.Var) : B.footprintT x = B.footprint x := by
  ext c
  change (c ∈ ⋃ i : Fin 1, B.footprint (#v[x])[i]) ↔ _
  simp

@[circuit_norm]
theorem footprintT_nativePair (x y : B.Var) :
    B.footprintT (M := nativePair) (x, y) = B.footprint x ∪ B.footprint y := by
  ext c
  change (c ∈ ⋃ i : Fin 2, B.footprint (#v[x, y])[i]) ↔ _
  simp [Fin.exists_fin_two]

@[circuit_norm]
theorem footprintT_nativeTriple (x y z : B.Var) :
    B.footprintT (M := nativeTriple) (x, y, z) = B.footprint x ∪ B.footprint y ∪ B.footprint z := by
  ext c
  change (c ∈ ⋃ i : Fin 3, B.footprint (#v[x, y, z])[i]) ↔ _
  simp [Fin.exists_fin_succ, Set.mem_union, or_assoc]

@[circuit_norm]
theorem footprintT_vec0 : B.footprintT (M := natives 0) #v[] = ∅ := by
  ext c
  change (c ∈ ⋃ i : Fin 0, B.footprint (#v[])[i]) ↔ _
  simp

@[circuit_norm]
theorem footprintT_vec1 (x : B.Var) : B.footprintT (M := natives 1) #v[x] = B.footprint x := by
  ext c
  change (c ∈ ⋃ i : Fin 1, B.footprint (#v[x])[i]) ↔ _
  simp

@[circuit_norm]
theorem footprintT_vec2 (x y : B.Var) : B.footprintT (M := natives 2) #v[x, y] = B.footprint x ∪ B.footprint y := by
  ext c
  change (c ∈ ⋃ i : Fin 2, B.footprint (#v[x, y])[i]) ↔ _
  simp [Fin.exists_fin_two]

@[circuit_norm]
theorem footprintT_vec3 (x y z : B.Var) :
    B.footprintT (M := natives 3) #v[x, y, z] = B.footprint x ∪ B.footprint y ∪ B.footprint z := by
  ext c
  change (c ∈ ⋃ i : Fin 3, B.footprint (#v[x, y, z])[i]) ↔ _
  simp [Fin.exists_fin_succ, Set.mem_union, or_assoc]

theorem footprintT_natives {n : ℕ} (v : natives n B.Var) :
    B.footprintT v = ⋃ i : Fin n, B.footprint v[i] := rfl

/-- An element of a vector reads a subset of what the vector reads. For `spatial`. -/
theorem footprint_getElem_subset {n : ℕ} {v : natives n B.Var} {S : Set B.Cell}
    (h : B.footprintT v ⊆ S) (i : ℕ) (hi : i < n) : B.footprint v[i] ⊆ S :=
  (footprint_subset_footprintT v ⟨i, hi⟩).trans h

/-- The tail of a vector reads a subset of what the vector reads. For `spatial`. -/
theorem footprintT_tail_subset {n : ℕ} {v : natives (n + 1) B.Var} {S : Set B.Cell}
    (h : B.footprintT v ⊆ S) : B.footprintT (M := natives n) v.tail ⊆ S := by
  refine Set.iUnion_subset fun i => ?_
  have hi : i.val < n := i.isLt
  show B.footprint (v.tail[i.val]'(by omega)) ⊆ S
  rw [Vector.getElem_tail']
  exact footprint_getElem_subset h _ (by omega)

@[circuit_norm]
theorem footprintT_unit (x : unit B.Var) : B.footprintT x = ∅ := by
  ext c
  change (c ∈ ⋃ i : Fin 0, B.footprint (#v[])[i]) ↔ _
  simp

/-! ### Flat lists of native operations: the real semantics -/

variable (B)

def flatAdvance : List B.Op → B.State → B.State
  | [], s => s
  | op :: ops, s => flatAdvance ops (B.advance op s)

def FlatHolds (env : B.Cell → B.Native) : B.State → List B.Op → Prop
  | _, [] => True
  | s, op :: ops => B.Holds env s op ∧ FlatHolds env (B.advance op s) ops

def FlatHonest (env : B.Cell → B.Native) : B.State → List B.Op → Prop
  | _, [] => True
  | s, op :: ops => B.Honest env s op ∧ FlatHonest env (B.advance op s) ops

/-- Well-formedness: every operation reads only cells that exist when it runs. -/
def FlatLocal : B.State → List B.Op → Prop
  | _, [] => True
  | s, op :: ops => B.reads op ⊆ B.Alloc s ∧ FlatLocal (B.advance op s) ops

variable {B}

theorem flatAdvance_append (a b : List B.Op) (s : B.State) :
    B.flatAdvance (a ++ b) s = B.flatAdvance b (B.flatAdvance a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons op ops ih => simp [flatAdvance, ih]

theorem flatHolds_append {env : B.Cell → B.Native} {s : B.State} (a b : List B.Op) :
    B.FlatHolds env s (a ++ b) ↔ B.FlatHolds env s a ∧ B.FlatHolds env (B.flatAdvance a s) b := by
  induction a generalizing s with
  | nil => simp [FlatHolds, flatAdvance]
  | cons op ops ih => simp [FlatHolds, flatAdvance, ih, and_assoc]

theorem flatHonest_append {env : B.Cell → B.Native} {s : B.State} (a b : List B.Op) :
    B.FlatHonest env s (a ++ b) ↔ B.FlatHonest env s a ∧ B.FlatHonest env (B.flatAdvance a s) b := by
  induction a generalizing s with
  | nil => simp [FlatHonest, flatAdvance]
  | cons op ops ih => simp [FlatHonest, flatAdvance, ih, and_assoc]

theorem flatLocal_append {s : B.State} (a b : List B.Op) :
    B.FlatLocal s (a ++ b) ↔ B.FlatLocal s a ∧ B.FlatLocal (B.flatAdvance a s) b := by
  induction a generalizing s with
  | nil => simp [FlatLocal, flatAdvance]
  | cons op ops ih => simp [FlatLocal, flatAdvance, ih, and_assoc]

theorem flatAlloc_mono (ops : List B.Op) (s : B.State) : B.Alloc s ⊆ B.Alloc (B.flatAdvance ops s) := by
  induction ops generalizing s with
  | nil => exact le_rfl
  | cons op ops ih => exact (B.alloc_mono op s).trans (ih _)

/--
**Witness generation.** A well-formed list of operations can be run honestly on top of any
existing assignment of the heap. This is what makes completeness statements non-vacuous, and it
follows from the two frame laws alone.
-/
theorem flatHonest_exists (ops : List B.Op) :
    ∀ (s : B.State) (env₀ : B.Cell → B.Native), B.FlatLocal s ops →
      ∃ env, (∀ c ∈ B.Alloc s, env c = env₀ c) ∧ B.FlatHonest env s ops := by
  induction ops with
  | nil => exact fun s env₀ _ => ⟨env₀, fun _ _ => rfl, trivial⟩
  | cons op ops ih =>
    intro s env₀ ⟨h_reads, h_local⟩
    obtain ⟨env₁, h_agree₁, h_honest₁⟩ := B.honest_extend env₀ s op h_reads
    obtain ⟨env₂, h_agree₂, h_honest₂⟩ := ih (B.advance op s) env₁ h_local
    refine ⟨env₂, fun c hc => ?_, ?_, h_honest₂⟩
    · rw [h_agree₂ c (B.alloc_mono op s hc), h_agree₁ c hc]
    · exact B.honest_frame env₁ env₂ s op h_reads h_honest₁ fun c hc => (h_agree₂ c hc).symm

end Backend
end Clean2
