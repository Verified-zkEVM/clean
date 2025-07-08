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

theorem Fin.foldl_const_succ (n : ℕ) (f : Fin (n + 1) → α) (init : α) :
    Fin.foldl (n + 1) (fun _ i => f i) init = f n := by
  induction n generalizing init with
  | zero => rfl
  | succ n ih =>
    let f' (i : Fin (n + 1)) := f (i.succ)
    rw [Fin.foldl_succ]
    show Fin.foldl (n + 1) (fun x i ↦ f' i) _ = _
    rw [ih]
    simp only [f']
    rw [Fin.natCast_eq_last, Fin.succ_last, ←Fin.natCast_eq_last]

theorem Fin.foldl_const_zero (f : Fin 0 → α) (init : α) :
    Fin.foldl 0 (fun _ i => f i) init = init := by
  rfl

theorem Fin.foldl_const (n : ℕ) (f : Fin n → α) (init : α) :
  Fin.foldl n (fun _ i => f i) init = match n with
    | 0 => init
    | n + 1 => f n := by
  split <;> simp [foldl_const_succ]

lemma Fin.foldl_eq_foldl_finRange (n : ℕ) (f : α → Fin n → α) (init : α) :
    Fin.foldl n f init = (List.finRange n).foldl f init := by
  induction n generalizing init with
  | zero => rfl
  | succ n ih =>
    simp only [Fin.foldl_succ, List.finRange_succ, List.foldl_cons]
    specialize ih (fun x i => f x i.succ) (f init 0)
    rw [ih, List.foldl_map]
