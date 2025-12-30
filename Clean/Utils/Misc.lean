/-
Miscellaneous utility lemmas/methods that don't fit anywhere else.
-/
import Mathlib.Data.Fin.Basic
variable {α : Type}

theorem funext_heq {α α' β : Type} (h : α = α') {f : α → β} {g : α' → β} :
    (∀ x : α, f x = g (cast h x)) → HEq f g := by
  subst h
  intro hfg
  apply heq_of_eq
  funext x
  exact hfg x

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

lemma Fin.foldl_eq_foldl_finRange (n : ℕ) (f : α → Fin n → α) (init : α) :
    Fin.foldl n f init = (List.finRange n).foldl f init := by
  induction n generalizing init with
  | zero => aesop
  | succ n ih =>
    simp only [Fin.foldl_succ, List.finRange_succ, List.foldl_cons]
    specialize ih (fun x i => f x i.succ) (f init 0)
    rw [ih, List.foldl_map]
