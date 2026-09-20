/-
`TypeMap` and `ProvableType`: the shapes of circuit inputs and outputs.

A `TypeMap` is a container `M : Type → Type` that is used at two element types:
- `M B.Var` for the variables a circuit manipulates (backend-specific), and
- `M B.Native` for the native values those variables denote.
An interface is stated on `M Native`; an implementation is stated on `M B.Var`.
Nothing here assumes anything about the native type.
-/
module

public import Clean2.Core.Attr
public import Mathlib.Data.Nat.Notation

@[expose] public section

namespace Clean2

abbrev TypeMap := Type → Type

/--
A container of a fixed number of elements, uniformly in the element type.
`map` changes the element type; this is what evaluates variables to values.
-/
class ProvableType (M : TypeMap) where
  size : ℕ
  toElements {α : Type} : M α → Vector α size
  fromElements {α : Type} : Vector α size → M α
  map {α β : Type} : (α → β) → M α → M β
  fromElements_toElements {α : Type} : ∀ x : M α, fromElements (toElements x) = x := by intros; rfl
  toElements_map {α β : Type} (f : α → β) (x : M α) : toElements (map f x) = (toElements x).map f

export ProvableType (size toElements fromElements)

attribute [circuit_norm] ProvableType.map

theorem ProvableType.map_eq_fromElements {M : TypeMap} [ProvableType M] {α β : Type} (f : α → β) (x : M α) :
    ProvableType.map f x = fromElements ((toElements x).map f) := by
  rw [← ProvableType.fromElements_toElements (ProvableType.map f x), ProvableType.toElements_map]

/-- The single-element container. -/
abbrev native : TypeMap := fun α => α

instance : ProvableType native where
  size := 1
  toElements x := #v[x]
  fromElements v := v[0]
  map f x := f x
  toElements_map f x := by simp

abbrev nativePair : TypeMap := fun α => α × α

instance : ProvableType nativePair where
  size := 2
  toElements | (x, y) => #v[x, y]
  fromElements v := (v[0], v[1])
  map f | (x, y) => (f x, f y)
  toElements_map f | (x, y) => by simp

abbrev nativeTriple : TypeMap := fun α => α × α × α

instance : ProvableType nativeTriple where
  size := 3
  toElements | (x, y, z) => #v[x, y, z]
  fromElements v := (v[0], v[1], v[2])
  map f | (x, y, z) => (f x, f y, f z)
  toElements_map f | (x, y, z) => by simp

/-- `n` elements. -/
abbrev natives (n : ℕ) : TypeMap := fun α => Vector α n

instance {n : ℕ} : ProvableType (natives n) where
  size := n
  toElements v := v
  fromElements v := v
  map f v := v.map f
  toElements_map _ _ := rfl

/-! ### Vectors by head and tail, for gadgets defined on `natives n` -/

/-- Indexing into the tail of a vector. -/
theorem _root_.Vector.getElem_tail' {α : Type} {n : ℕ} (v : Vector α (n + 1)) (i : ℕ) (hi : i < n) :
    v.tail[i] = v[i + 1] := by
  simp [Nat.add_comm]

/-- The empty container, for circuits without input or output. -/
abbrev unit : TypeMap := fun _ => Unit

instance : ProvableType unit where
  size := 0
  toElements _ := #v[]
  fromElements _ := ()
  map _ _ := ()
  toElements_map _ _ := by simp

end Clean2
