import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Basic
import Mathlib.Data.ZMod.Basic

variable {α β : Type} {n : ℕ}

def Vector (α : Type) (n: ℕ) := { l: List α // l.length = n }

instance [Repr α] {n: ℕ} : Repr (Vector α n) where
  reprPrec l _ := repr l.val

@[reducible]
def vec (l: List α) : Vector α l.length := ⟨ l, rfl ⟩

namespace Vector
  def len (_: Vector α n) : ℕ := n

  @[ext]
  theorem ext (l : ℕ) (v w: Vector α l) : v.val = w.val → v = w := by
    intro h
    cases v
    cases w
    simp [Subtype.mk_eq_mk] at h
    simp [h]

  @[simp]
  def map (f: α → β) : Vector α n → Vector β n
    | ⟨ l, h ⟩ => ⟨ l.map f, by rw [List.length_map, h] ⟩

  def zip {n} : Vector α n → Vector β n → Vector (α × β) n
    | ⟨ [], ha ⟩, ⟨ [], _ ⟩  => ⟨ [], ha ⟩
    | ⟨ a::as, (ha : as.length + 1 = n) ⟩,
      ⟨ b::bs, (hb : bs.length + 1 = n) ⟩ =>
      let ⟨ z, hz ⟩ := zip ⟨ as, rfl ⟩ ⟨ bs, by apply Nat.add_one_inj.mp; rw [ha, hb] ⟩
      ⟨ (a, b) :: z, by show z.length + 1 = n; rw [hz, ha] ⟩

  @[simp]
  def get (v: Vector α n) (i: Fin n) : α :=
    let i' : Fin v.1.length := Fin.cast v.prop.symm i
    v.val.get i'

  @[simp]
  def push (v: Vector α n) (a: α) : Vector α (n + 1) :=
    ⟨ a :: v.val, by simp [v.prop] ⟩

  @[simp]
  def append {m} (v: Vector α n) (w: Vector α m) : Vector α (n + m) :=
    ⟨ v.val ++ w.val, by simp [v.prop, w.prop] ⟩

  -- map over monad
  def mapM {M : Type → Type} {n} [Monad M] (v : Vector (M α) n) : M (Vector α n) :=
    match (v : Vector (M α) n) with
    | ⟨ [], h ⟩ => pure ⟨ [], h ⟩
    | ⟨ a :: as, (h : as.length + 1 = n) ⟩ => do
      let hd ← a
      let tl ← mapM ⟨ as, rfl ⟩
      pure ⟨ hd :: tl.val, by rwa [List.length_cons, tl.prop]⟩
end Vector
