import Mathlib.Data.Fintype.Basic

variable {α β : Type} {n : ℕ}

def Vector (α : Type) (n: ℕ) := { l: List α // l.length = n }

def vector (l: List α) : Vector α l.length := ⟨ l, rfl ⟩

namespace Vector
  theorem length_matches (v: Vector α n) : v.1.length = n := v.2

  def map (f: α → β) : Vector α n → Vector β n
    | ⟨ l, h ⟩ => ⟨ l.map f, by rw [List.length_map, h] ⟩
end Vector
