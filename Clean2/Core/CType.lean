/-
Synthetic types: how the values of a meaning type are laid out in native values.

A `CType Native T` is a shape (a provable type, used at `B.Var` for the variables and at `Native`
for their values) together with what a native value of that shape means: `Valid` says which
native values represent some `T`, and `decode` says which one. `Valid` is the *representation
invariant* and `decode` the *abstraction function*. A synthetic type is a value: two layouts of a
byte are two values of `CType F UInt8`, and an interface stated on a byte type takes it as an
argument, so that its implementations exist at one layout and the layers above are generic in it.

A contract is stated on a meaning type together with a synthetic type of it; `ofProvable` is the
embedding of provable types (every value valid, and each value its own meaning): a contract on
native values is the special case of the trivial synthetic types.

The combinators build synthetic types of compound meanings from synthetic types of their parts,
the way a provable type is built from its elements.
-/
module

public import Clean2.Core.Backend

@[expose] public section

namespace Clean2

/-! ### Shapes of compound types -/

/-- The `j`-th element of the `i`-th block of `n` blocks of size `s`. -/
theorem block_lt {i j n s : ℕ} (hi : i < n) (hj : j < s) : i * s + j < n * s :=
  calc i * s + j < i * s + s := by omega
    _ = (i + 1) * s := (Nat.succ_mul i s).symm
    _ ≤ n * s := Nat.mul_le_mul_right _ hi

/-- Two shapes side by side. Low priority: the specific instances (`nativePair`, ...) come first. -/
instance (priority := low) ProvableType.prod {M N : TypeMap} [ProvableType M] [ProvableType N] :
    ProvableType (fun α => M α × N α) where
  size := size M + size N
  toElements x := toElements x.1 ++ toElements x.2
  fromElements v :=
    (fromElements (Vector.ofFn fun i => v[i.val]), fromElements (Vector.ofFn fun i => v[size M + i.val]))
  map f x := (ProvableType.map f x.1, ProvableType.map f x.2)
  fromElements_toElements x := by
    obtain ⟨x₁, x₂⟩ := x
    congr
    · conv => rhs; rw [← ProvableType.fromElements_toElements x₁]
      congr 1; ext i hi
      simp
    · conv => rhs; rw [← ProvableType.fromElements_toElements x₂]
      congr 1; ext i hi
      simp
  toElements_map f x := by
    simp only [ProvableType.toElements_map, Vector.map_append]

/-- `n` copies of a shape. Low priority: `natives n` comes first. -/
instance (priority := low) ProvableType.vector {M : TypeMap} [ProvableType M] (n : ℕ) :
    ProvableType (fun α => Vector (M α) n) where
  size := n * size M
  toElements x := (x.map toElements).flatten
  fromElements v := Vector.ofFn fun i => fromElements (Vector.ofFn fun j =>
    v[i.val * size M + j.val]'(block_lt i.isLt j.isLt))
  map f x := x.map (ProvableType.map f)
  fromElements_toElements x := by
    ext i hi
    simp only [Vector.getElem_ofFn]
    conv => rhs; rw [← ProvableType.fromElements_toElements x[i]]
    congr 1; ext j hj
    have hlt : i * size M + j < n * size M := block_lt hi hj
    have hpos : 0 < size M := by omega
    simp only [Vector.getElem_ofFn, Vector.getElem_flatten hlt, Vector.getElem_map]
    have h₁ : (i * size M + j) / size M = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hj, Nat.zero_add]
    have h₂ : (i * size M + j) % size M = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    simp only [h₁, h₂]
  toElements_map f x := by
    simp only [Vector.map_flatten, Vector.map_map]
    congr 1
    ext i hi
    simp [ProvableType.toElements_map]

/-- A pair reads what its components read. -/
@[circuit_norm]
theorem Backend.footprintT_prod {B : Backend} {M N : TypeMap} [ProvableType M] [ProvableType N]
    (x : M B.Var) (y : N B.Var) :
    B.footprintT (M := fun α => M α × N α) (x, y) = B.footprintT x ∪ B.footprintT y := by
  ext c
  simp only [Backend.footprintT, Set.mem_iUnion, Set.mem_union]
  constructor
  · rintro ⟨i, hi⟩
    change c ∈ B.footprint (toElements x ++ toElements y)[i.val] at hi
    rw [Vector.getElem_append] at hi
    split at hi
    · exact Or.inl ⟨⟨i, ‹_›⟩, hi⟩
    · exact Or.inr ⟨⟨i - size M, by have := i.isLt; change i.val < size M + size N at this; omega⟩, hi⟩
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · refine ⟨⟨i, by change i.val < size M + size N; omega⟩, ?_⟩
      change c ∈ B.footprint (toElements x ++ toElements y)[i.val]
      rwa [Vector.getElem_append_left i.isLt]
    · refine ⟨⟨size M + i, by change size M + i.val < size M + size N; omega⟩, ?_⟩
      change c ∈ B.footprint (toElements x ++ toElements y)[size M + i.val]
      rw [Vector.getElem_append_right (by omega) (by omega)]
      simpa using hi

/-- A vector reads what its elements read. -/
@[circuit_norm]
theorem Backend.footprintT_vector {B : Backend} {M : TypeMap} [ProvableType M] {n : ℕ} (x : Vector (M B.Var) n) :
    B.footprintT (M := fun α => Vector (M α) n) x = ⋃ i : Fin n, B.footprintT x[i] := by
  ext c
  simp only [Backend.footprintT, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨k, hk⟩, hc⟩
    change k < n * size M at hk
    have hpos : 0 < size M := by
      rcases Nat.eq_zero_or_pos (size M) with h | h
      · rw [h, Nat.mul_zero] at hk; exact absurd hk (Nat.not_lt_zero k)
      · exact h
    refine ⟨⟨k / size M, Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])⟩, ⟨k % size M, Nat.mod_lt _ hpos⟩, ?_⟩
    change c ∈ B.footprint ((x.map toElements).flatten)[k] at hc
    rw [Vector.getElem_flatten hk, Vector.getElem_map] at hc
    exact hc
  · rintro ⟨i, j, hc⟩
    have hlt : (i : ℕ) * size M + j < n * size M := block_lt i.isLt j.isLt
    refine ⟨⟨(i : ℕ) * size M + j, hlt⟩, ?_⟩
    change c ∈ B.footprint (((x.map toElements).flatten)[(i : ℕ) * size M + j]'hlt)
    have hpos : 0 < size M := by have := j.isLt; omega
    have h₁ : (i * size M + j) / size M = i := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
    have h₂ : (i * size M + j) % size M = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.isLt]
    rw [Vector.getElem_flatten hlt, Vector.getElem_map]
    simp only [h₁, h₂]
    exact hc

/-! ### Synthetic types -/

/-- A synthetic type with meaning `T`: how values of `T` are laid out in native values. -/
structure CType (Native T : Type) where
  /-- the layout, as a provable type: `Shape B.Var` are the variables of a `T` -/
  Shape : TypeMap
  [inst : ProvableType Shape]
  /-- the representation invariant: which native values represent some `T` -/
  Valid : Shape Native → Prop
  /-- the abstraction function: which `T` they represent -/
  decode : Shape Native → T

attribute [instance] CType.inst

namespace CType
variable {Native T U : Type}

/-- A provable type represents its own values. -/
@[reducible]
def ofProvable (M : TypeMap) [ProvableType M] : CType Native (M Native) where
  Shape := M
  Valid _ := True
  decode x := x

/-! The native synthetic types, for contracts on native values. -/

@[reducible]
def native : CType Native Native := ofProvable Clean2.native
@[reducible]
def nativePair : CType Native (Native × Native) := ofProvable Clean2.nativePair
@[reducible]
def nativeTriple : CType Native (Native × Native × Native) := ofProvable Clean2.nativeTriple
@[reducible]
def natives (n : ℕ) : CType Native (Vector Native n) := ofProvable (Clean2.natives n)
@[reducible]
def unit : CType Native Unit := ofProvable Clean2.unit

/-- A pair, each component in its own synthetic type. -/
@[reducible]
def prod (a : CType Native T) (b : CType Native U) : CType Native (T × U) where
  Shape α := a.Shape α × b.Shape α
  Valid x := a.Valid x.1 ∧ b.Valid x.2
  decode x := (a.decode x.1, b.decode x.2)

/-- A vector, element by element. -/
@[reducible]
def vec (n : ℕ) (a : CType Native T) : CType Native (Vector T n) where
  Shape α := Vector (a.Shape α) n
  Valid x := ∀ i : Fin n, a.Valid x[i]
  decode x := x.map a.decode

/-- The same layout and invariant, read as another type. -/
@[reducible]
def map (a : CType Native T) (f : T → U) : CType Native U where
  Shape := a.Shape
  Valid := a.Valid
  decode := f ∘ a.decode

end CType

@[inherit_doc CType.prod] infixr:35 " ×ᵗ " => CType.prod

/-! The invariant and the meaning, pushed through the combinators. All are `rfl`: the combinators
are reducible, and these only make the reductions available to `simp`. -/

section
variable {Native T U : Type}

@[circuit_norm] theorem CType.ofProvable_Valid {M : TypeMap} [ProvableType M] (x : M Native) :
    (CType.ofProvable M).Valid x = True := rfl
@[circuit_norm] theorem CType.ofProvable_decode {M : TypeMap} [ProvableType M] (x : M Native) :
    (CType.ofProvable M).decode x = x := rfl
@[circuit_norm] theorem CType.prod_Valid (a : CType Native T) (b : CType Native U) (x : a.Shape Native × b.Shape Native) :
    (a ×ᵗ b).Valid x = (a.Valid x.1 ∧ b.Valid x.2) := rfl
@[circuit_norm] theorem CType.prod_decode (a : CType Native T) (b : CType Native U) (x : a.Shape Native × b.Shape Native) :
    (a ×ᵗ b).decode x = (a.decode x.1, b.decode x.2) := rfl
@[circuit_norm] theorem CType.vec_Valid (a : CType Native T) {n : ℕ} (x : Vector (a.Shape Native) n) :
    (CType.vec n a).Valid x = ∀ i : Fin n, a.Valid x[i] := rfl
@[circuit_norm] theorem CType.vec_decode (a : CType Native T) {n : ℕ} (x : Vector (a.Shape Native) n) :
    (CType.vec n a).decode x = x.map a.decode := rfl
@[circuit_norm] theorem CType.map_Valid (a : CType Native T) (f : T → U) (x : a.Shape Native) :
    (a.map f).Valid x = a.Valid x := rfl
@[circuit_norm] theorem CType.map_decode (a : CType Native T) (f : T → U) (x : a.Shape Native) :
    (a.map f).decode x = f (a.decode x) := rfl

end

/-! The footprints of compound synthetic types, keyed on the shapes as they occur: `(a ×ᵗ b).Shape`,
not `fun α => a.Shape α × b.Shape α`. These are what `spatial` sees. -/

@[circuit_norm]
theorem Backend.footprintT_ctypeProd {B : Backend} {T U : Type} (a : CType B.Native T) (b : CType B.Native U)
    (x : a.Shape B.Var) (y : b.Shape B.Var) :
    B.footprintT (M := (a ×ᵗ b).Shape) (x, y) = B.footprintT x ∪ B.footprintT y :=
  Backend.footprintT_prod x y

@[circuit_norm]
theorem Backend.footprintT_ctypeVec {B : Backend} {T : Type} (a : CType B.Native T) {n : ℕ} (v : Vector (a.Shape B.Var) n) :
    B.footprintT (M := (CType.vec n a).Shape) v = ⋃ i : Fin n, B.footprintT v[i] :=
  Backend.footprintT_vector v

/-! As subset facts, to be applied as terms, for `spatial` proofs about abstract synthetic types. -/

theorem Backend.footprintT_ctypeProd_subset {B : Backend} {T U : Type} {a : CType B.Native T} {b : CType B.Native U}
    {x : a.Shape B.Var} {y : b.Shape B.Var} {S : Set B.Cell} :
    B.footprintT (M := (a ×ᵗ b).Shape) (x, y) ⊆ S ↔ B.footprintT x ⊆ S ∧ B.footprintT y ⊆ S := by
  rw [Backend.footprintT_ctypeProd, Set.union_subset_iff]

theorem Backend.footprintT_ctypeVec_subset {B : Backend} {T : Type} {a : CType B.Native T} {n : ℕ}
    {v : Vector (a.Shape B.Var) n} {S : Set B.Cell} :
    B.footprintT (M := (CType.vec n a).Shape) v ⊆ S ↔ ∀ i : Fin n, B.footprintT v[i] ⊆ S := by
  rw [Backend.footprintT_ctypeVec, Set.iUnion_subset_iff]

theorem Backend.footprintT_native_subset {B : Backend} {x : native B.Var} {S : Set B.Cell} :
    B.footprintT x ⊆ S ↔ B.footprint x ⊆ S := by
  rw [Backend.footprintT_native]

end Clean2
