module

public import Mathlib.Data.Multiset.Basic
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Tactic.Linarith

/-! # Trails forced by finite multiset balance

Edges have arbitrary occurrence labels and arbitrary vertices. Endpoint degree balance
forces a source-to-sink trail contained in the supplied edge multiset. No finite vertex
type, clock, or acyclicity premise is needed. Additional disconnected cycles may remain.
The extraction proof removes one source edge at each induction step. -/

@[expose] public section

namespace Utils.ResourceHistory

namespace Walk

universe u v

variable {α : Type u} {V : Type v} [DecidableEq α] [DecidableEq V]

/-- Out-degree of `v` in the edge multiset `E`: the number of edges whose **source** is `v`. -/
def outdeg (E : Multiset α) (edge : α → V × V) (v : V) : ℕ :=
  (E.filter (fun a => (edge a).1 = v)).card

/-- In-degree of `v`: the number of edges whose **target** is `v`. -/
def indeg (E : Multiset α) (edge : α → V × V) (v : V) : ℕ :=
  (E.filter (fun a => (edge a).2 = v)).card

/-- Degree balance: when `src ≠ snk`, `src` has one more outgoing than incoming edge,
`snk` has one more incoming than outgoing edge, and every other vertex is balanced.
When `src = snk`, every vertex is balanced. -/
def Balanced (E : Multiset α) (edge : α → V × V) (src snk : V) : Prop :=
  ∀ v, (outdeg E edge v : ℤ) - indeg E edge v
      = (if v = src then 1 else 0) - (if v = snk then 1 else 0)

/-- A walk along `edge`s from `a` to `b`: the edge list's sources and targets chain up
(`src = e₀.1`, `e_i.2 = e_{i+1}.1`, last `.2 = snk`); the empty walk requires `a = b`. -/
def IsWalk (edge : α → V × V) : V → V → List α → Prop
  | a, b, [] => a = b
  | a, b, x :: rest => (edge x).1 = a ∧ IsWalk edge (edge x).2 b rest

/-- Erasing one element `e ∈ E` drops the count of a filter by `1` exactly when `e` satisfies it. -/
lemma card_filter_erase {E : Multiset α} {e : α} (he : e ∈ E)
    (P : α → Prop) [DecidablePred P] :
    (E.filter P).card = ((E.erase e).filter P).card + (if P e then 1 else 0) := by
  conv_lhs => rw [← Multiset.cons_erase he]
  rw [Multiset.filter_cons, Multiset.card_add]
  by_cases h : P e <;> simp [h, Nat.add_comm]

/-- **The induction step.** If `E` is balanced with source `src`, sink `snk`, and `e` is an out-edge
of `src` (`(edge e).1 = src`), then `E.erase e` is balanced with the source moved to `(edge e).2`
(one step along `e`) and the same sink. -/
lemma balanced_erase {E : Multiset α} {e : α} (he : e ∈ E) (edge : α → V × V)
    {src snk : V} (h : Balanced E edge src snk) (h1 : (edge e).1 = src) :
    Balanced (E.erase e) edge (edge e).2 snk := by
  intro v
  have ho : (outdeg E edge v : ℤ)
      = (outdeg (E.erase e) edge v : ℤ) + (if (edge e).1 = v then 1 else 0) := by
    simp only [outdeg]; exact_mod_cast card_filter_erase he (fun a => (edge a).1 = v)
  have hi : (indeg E edge v : ℤ)
      = (indeg (E.erase e) edge v : ℤ) + (if (edge e).2 = v then 1 else 0) := by
    simp only [indeg]; exact_mod_cast card_filter_erase he (fun a => (edge a).2 = v)
  have hv := h v
  have e1 : (if (edge e).1 = v then (1 : ℤ) else 0) = (if v = src then 1 else 0) := by
    simp [h1, eq_comm]
  have e2 : (if (edge e).2 = v then (1 : ℤ) else 0) = (if v = (edge e).2 then 1 else 0) := by
    simp [eq_comm]
  rw [e1] at ho
  rw [e2] at hi
  linarith

/-- Degree balance forces a walk from `src` to `snk` whose edges form a sub-multiset of `E`. -/
theorem exists_trail (edge : α → V × V) (E : Multiset α) :
    ∀ (src snk : V), Balanced E edge src snk →
      ∃ path : List α, IsWalk edge src snk path ∧ (↑path : Multiset α) ≤ E := by
  induction E using Multiset.strongInductionOn with
  | _ E IH =>
    intro src snk h
    by_cases hss : src = snk
    · exact ⟨[], hss, by simp [Multiset.zero_le]⟩
    · have hsrc := h src
      rw [if_pos rfl, if_neg hss] at hsrc
      have hpos : 0 < outdeg E edge src := by omega
      simp only [outdeg] at hpos
      obtain ⟨e, he_filter⟩ := Multiset.exists_mem_of_ne_zero (Multiset.card_pos.mp hpos)
      obtain ⟨he_mem, he1⟩ := Multiset.mem_filter.mp he_filter
      have hbal' : Balanced (E.erase e) edge (edge e).2 snk := balanced_erase he_mem edge h he1
      obtain ⟨path', hwalk', hsub'⟩ :=
        IH (E.erase e) (Multiset.erase_lt.mpr he_mem) (edge e).2 snk hbal'
      refine ⟨e :: path', ⟨he1, hwalk'⟩, ?_⟩
      rw [← Multiset.cons_erase he_mem]
      exact Multiset.cons_le_cons e hsub'

omit [DecidableEq α] [DecidableEq V] in
/-- A walk over a mapped edge list is a walk of the composed edge function (the sum-typed trail's
per-injection projection). -/
theorem isWalk_map {β : Type*} (edge : β → V × V) (f : α → β) :
    ∀ (l : List α) (a b : V), IsWalk edge a b (l.map f) ↔
      IsWalk (fun x => edge (f x)) a b l
  | [], _, _ => Iff.rfl
  | _ :: rest, a, b => by
      simp only [List.map_cons]
      exact and_congr Iff.rfl (isWalk_map edge f rest _ b)

omit [DecidableEq α] [DecidableEq V] in
/-- **Transporting a walk along a pointwise correspondence.** Two row lists in the same order whose
edges agree entry for entry describe the same walk. This is what a *projection* of the trail needs:
the projected list is not a `List.map` of the original — the two row types are related by a relation,
not a function — so `isWalk_map` does not apply. -/
theorem isWalk_forall₂ {β : Type*} (edge : α → V × V) (edge' : β → V × V)
    (R : α → β → Prop) (hR : ∀ {x y}, R x y → edge x = edge' y) :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' →
      ∀ {a b : V}, IsWalk edge a b l → IsWalk edge' a b l'
  | [], [], _, _, _, h => h
  | x :: rest, y :: rest', hf, a, b, h => by
      obtain ⟨hxy, hrest⟩ := List.forall₂_cons.mp hf
      obtain ⟨hhead, htail⟩ := h
      refine ⟨?_, ?_⟩
      · rw [← hR hxy]; exact hhead
      · rw [← hR hxy]; exact isWalk_forall₂ edge edge' R hR hrest htail

omit [DecidableEq α] [DecidableEq V] in
/-- A walk over an append splits at the junction vertex. -/
theorem isWalk_append (edge : α → V × V) :
    ∀ (l₁ l₂ : List α) (a b : V), IsWalk edge a b (l₁ ++ l₂) ↔
      ∃ c, IsWalk edge a c l₁ ∧ IsWalk edge c b l₂
  | [], l₂, a, b => by
      constructor
      · intro h
        exact ⟨a, rfl, by exact h⟩
      · rintro ⟨c, rfl, h⟩
        exact h
  | x :: rest, l₂, a, b => by
      simp only [List.cons_append]
      change ((edge x).1 = a ∧ IsWalk edge (edge x).2 b (rest ++ l₂)) ↔ _
      rw [isWalk_append edge rest l₂]
      constructor
      · rintro ⟨h1, c, h2, h3⟩
        exact ⟨c, ⟨h1, h2⟩, h3⟩
      · rintro ⟨c, ⟨h1, h2⟩, h3⟩
        exact ⟨h1, c, h2, h3⟩

end Walk

end Utils.ResourceHistory
