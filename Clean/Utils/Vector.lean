import Mathlib.Data.Fintype.Basic

variable {α β : Type} {n : ℕ}

def Vector (α : Type) (n: ℕ) := { l: List α // l.length = n }

instance [Repr α] {n: ℕ} : Repr (Vector α n) where
  reprPrec l _ := repr l.val

@[reducible]
def vec (l: List α) : Vector α l.length := ⟨ l, rfl ⟩

namespace Vector
  theorem vec_eq (l : ℕ) (v w: Vector α l) : v.val = w.val ↔ v = w := by
    constructor
    · intro h
      cases v
      cases w
      simp [Subtype.mk_eq_mk] at h
      simp [h]
    · aesop

  theorem length_matches (v: Vector α n) : v.1.length = n := v.2

  @[simp]
  def map (f: α → β) : Vector α n → Vector β n
    | ⟨ l, h ⟩ => ⟨ l.map f, by rw [List.length_map, h] ⟩

  @[simp]
  def zip : Vector α n → Vector β n → Vector (α × β) n
    | ⟨ [], ha ⟩, ⟨ [], _ ⟩  => ⟨ [], ha ⟩
    | ⟨ a::as, ha ⟩, ⟨ b::bs, hb ⟩ => ⟨ (a, b) :: List.zip as bs, by sorry ⟩

  @[simp]
  def get (v: Vector α n) (i: Fin n) : α :=
    let i' : Fin v.1.length := Fin.cast (length_matches v).symm i
    v.val.get i'

  -- map over monad
  @[simp]
  def mapM { M : Type → Type } [Monad M] (v : Vector (M α) n) : M (Vector α n) :=
    -- there `List.mapM` which we can use, but there doesn't seem to be an equivalent of `List.length_map` for monads
    do
      let l' ← List.mapM id v.val
      return ⟨ l', by sorry ⟩

  -- other direction
  @[simp]
  def unmapM { M : Type → Type } [Monad M] (v : M (Vector α n)) : Vector (M α) n :=
    sorry

end Vector
