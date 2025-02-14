import Mathlib.Data.Fintype.Basic

variable {α β : Type} {n : ℕ}

def Vector (α : Type) (n: ℕ) := { l: List α // l.length = n }

@[reducible]
def vec (l: List α) : Vector α l.length := ⟨ l, rfl ⟩

namespace Vector
  theorem length_matches (v: Vector α n) : v.1.length = n := v.2

  @[simp]
  def map (f: α → β) : Vector α n → Vector β n
    | ⟨ l, h ⟩ => ⟨ l.map f, by rw [List.length_map, h] ⟩

  def get (v: Vector α n) (i: Fin n) : α :=
    let i' : Fin v.1.length := Fin.cast (length_matches v).symm i
    v.val.get i'

  -- map over monad
  def mapM { M : Type → Type } [Monad M] (v : Vector (M α) n) : M (Vector α n) :=
    -- there `List.mapM` which we can use, but there doesn't seem to be an equivalent of `List.length_map` for monads
    sorry

  def zip : Vector α n → Vector β n → Vector (α × β) n :=
    sorry

end Vector
