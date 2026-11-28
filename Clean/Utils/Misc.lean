/-
Miscellaneous utility lemmas/methods that don't fit anywhere else.
-/
module

public import Mathlib.Data.Fin.Basic

@[expose] public section
variable {α : Type}

theorem cast_apply {α β β' : Type} (h : β = β') (f : α → β) (x : α) :
    (cast (h ▸ rfl) f : α → β') x = cast (h ▸ rfl) (f x) := by
  subst h; rfl

theorem cast_apply' {α α' β : Type} (h : α = α') (f : α → β) (x : α') :
    (cast (h ▸ rfl) f : α' → β) x = f (cast (h ▸ rfl) x : α) := by
  subst h; rfl

theorem cast_fst {α α' β : Type} (h : α = α') (p : α × β) :
    (cast h p.1 : α') = (cast (h ▸ rfl) p : α' × β).1 := by
  subst h; rfl

theorem cast_snd {α β β' : Type} (h : β = β') (p : α × β) :
    (cast h p.2 : β') = (cast (h ▸ rfl) p : α × β').2 := by
  subst h; rfl

theorem fst_cast {α β β' : Type} (h : β = β') (p : α × β) :
    (cast (h ▸ rfl) p : α × β').1 = p.1 := by
  subst h; rfl

theorem snd_cast {α α' β : Type} (h : α = α') (p : α × β) :
    (cast (h ▸ rfl) p : α' × β).2 = p.2 := by
  subst h; rfl

theorem Fin.foldl_const_succ (n : ℕ) (f : Fin (n + 1) → α) (init : α) :
    Fin.foldl (n + 1) (fun _ i => f i) init = f (.last n) := by
  induction n generalizing init with
  | zero =>
      simp only [Nat.zero_add, Nat.reduceAdd, cast_eq_self, last_zero, isValue, foldl_succ]
      aesop
  | succ n ih =>
    let f' (i : Fin (n + 1)) := f (i.succ)
    rw [Fin.foldl_succ]
    show Fin.foldl (n + 1) (fun x i ↦ f' i) _ = _
    rw [ih]
    simp only [f']
    rw [Fin.succ_last, ←Fin.natCast_eq_last]

theorem Fin.foldl_const_zero (f : Fin 0 → α) (init : α) :
    Fin.foldl 0 (fun _ i => f i) init = init := by aesop

theorem Fin.foldl_const (n : ℕ) (f : Fin n → α) (init : α) :
  Fin.foldl n (fun _ i => f i) init = match n with
    | 0 => init
    | n + 1 => f (.last n) := by
  split <;> simp [foldl_const_succ]

/-- Closed form of a fold: if `acc` starts at `init` and follows `f` step by step,
then the fold over `Fin n` ends at `acc n`. -/
theorem Fin.foldl_eq_of_succ {n : ℕ} {f : α → Fin n → α} {init : α} {acc : ℕ → α}
    (h_init : acc 0 = init) (h_succ : ∀ i : Fin n, f (acc i) i = acc (i + 1)) :
    Fin.foldl n f init = acc n := by
  induction n with
  | zero => rw [Fin.foldl_zero, h_init]
  | succ n ih =>
    have h_castSucc := fun i : Fin n => h_succ i.castSucc
    have h_last := h_succ (Fin.last n)
    simp only [Fin.val_castSucc] at h_castSucc
    rw [Fin.val_last] at h_last
    rw [Fin.foldl_succ_last, ih h_castSucc, h_last]
