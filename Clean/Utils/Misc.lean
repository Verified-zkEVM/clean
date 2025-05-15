/-
Miscellaneous utility lemmas/methods that don't fit anywhere else.
-/
import Mathlib.Tactic

theorem Fin.foldl_const {α : Type} (n : ℕ) (f : Fin (n + 1) → α) (init : α) :
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
