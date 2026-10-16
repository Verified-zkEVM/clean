module

public import Clean.Utils.ResourceHistory.Ranked
public import Mathlib.Data.List.Sort

/-! # Ordered histories

Balance gives a subtrail. Finite acyclicity makes it exhaustive; a strict order on
versions then identifies it with a supplied chronological list. Neither the vertex
type nor the version order has to be finite or globally well-founded.
-/

@[expose] public section

namespace Utils.ResourceHistory

open Walk Ranked

variable {Edge Vertex : Type*} [DecidableEq Edge] [DecidableEq Vertex]

/-- No nonempty closed walk can use occurrences from this inventory. -/
def Acyclic (edges : Multiset Edge) (edge : Edge → Vertex × Vertex) : Prop :=
  ∀ vertex (path : List Edge), (↑path : Multiset Edge) ≤ edges →
    IsWalk edge vertex vertex path → path = []

/-- A finite balanced nonempty inventory contains a closed walk. -/
theorem eq_zero_of_acyclic_balanced (edges : Multiset Edge) (edge : Edge → Vertex × Vertex)
    (acyclic : Acyclic edges edge)
    (balanced : edges.map (fun e => (edge e).2) = edges.map (fun e => (edge e).1)) :
    edges = 0 := by
  by_contra nonempty
  obtain ⟨e, member⟩ := Multiset.exists_mem_of_ne_zero nonempty
  have endpoints : EndpointBalanced edges edge (edge e).1 (edge e).1 :=
    congrArg (Multiset.cons (edge e).1) balanced
  have erased := balanced_erase member edge
    (balanced_of_endpointBalanced edges edge _ _ endpoints) rfl
  obtain ⟨path, walk, sub⟩ := exists_trail edge (edges.erase e) _ _ erased
  have contained : (↑(e :: path) : Multiset Edge) ≤ edges := by
    rw [← Multiset.cons_erase member]
    exact Multiset.cons_le_cons e sub
  have empty := acyclic (edge e).1 (e :: path) contained ⟨rfl, walk⟩
  cases empty

/-- Finite acyclicity upgrades endpoint balance to exhaustive occurrence coverage. -/
theorem exhaustive_of_acyclic (edges : Multiset Edge) (edge : Edge → Vertex × Vertex)
    (initial final : Vertex) (balanced : EndpointBalanced edges edge initial final)
    (acyclic : Acyclic edges edge) : ExhaustiveTrail edges edge initial final := by
  obtain ⟨path, walk, sub⟩ := exists_trail edge edges initial final
    (balanced_of_endpointBalanced edges edge initial final balanced)
  obtain ⟨rest, decomposition⟩ := Multiset.le_iff_exists_add.mp sub
  have pathBalance := endpointBalanced_of_isWalk edge walk
  have restBalance : rest.map (fun e => (edge e).2) = rest.map (fun e => (edge e).1) := by
    rw [decomposition] at balanced
    simp only [EndpointBalanced, Multiset.map_add, ← Multiset.cons_add] at balanced
    rw [pathBalance] at balanced
    exact add_left_cancel balanced
  have empty := eq_zero_of_acyclic_balanced rest edge
    (fun vertex trail contained closed => acyclic vertex trail
      (contained.trans (by rw [decomposition]; exact Multiset.le_add_left _ _)) closed) restBalance
  refine ⟨path, walk, ?_⟩
  rw [empty, add_zero] at decomposition
  exact decomposition.symm

omit [DecidableEq Edge] [DecidableEq Vertex] in
/-- Strict local progress composes along every nonempty walk. -/
theorem progresses_of_walk (edge : Edge → Vertex × Vertex) (before : Vertex → Vertex → Prop)
    (trans : ∀ ⦃a b c⦄, before a b → before b c → before a c) {initial final : Vertex} {path : List Edge}
    (walk : IsWalk edge initial final path) (nonempty : path ≠ [])
    (increases : ∀ e ∈ path, before (edge e).1 (edge e).2) : before initial final := by
  induction path generalizing initial with
  | nil => exact (nonempty rfl).elim
  | cons e rest ih =>
    obtain ⟨source, tail⟩ := walk
    have step := increases e (List.mem_cons_self ..)
    rw [source] at step
    cases rest with
    | nil => exact tail ▸ step
    | cons other rest =>
      exact trans step (ih tail (by simp) (fun x hx => increases x (List.mem_cons_of_mem _ hx)))

omit [DecidableEq Edge] [DecidableEq Vertex] in
/-- A strict order is sufficient, even when it is not well-founded outside this inventory. -/
theorem acyclic_of_strict (edges : Multiset Edge) (edge : Edge → Vertex × Vertex)
    (before : Vertex → Vertex → Prop) (irrefl : ∀ a, ¬ before a a) (trans : ∀ ⦃a b c⦄, before a b → before b c → before a c)
    (increases : ∀ e ∈ edges, before (edge e).1 (edge e).2) : Acyclic edges edge := by
  intro vertex path contained walk
  by_contra nonempty
  exact irrefl vertex (progresses_of_walk edge before trans walk nonempty
    (fun e member => increases e (Multiset.mem_of_le contained (Multiset.mem_coe.mpr member))))

omit [DecidableEq Edge] [DecidableEq Vertex] in
theorem targets_ordered_of_walk (edge : Edge → Vertex × Vertex) (before : Vertex → Vertex → Prop)
    (trans : ∀ ⦃a b c⦄, before a b → before b c → before a c) {initial final : Vertex} {path : List Edge}
    (walk : IsWalk edge initial final path)
    (increases : ∀ e ∈ path, before (edge e).1 (edge e).2) :
    (∀ e ∈ path, before initial (edge e).2) ∧
      path.Pairwise (fun a b => before (edge a).2 (edge b).2) := by
  induction path generalizing initial with
  | nil => simp
  | cons e rest ih =>
    obtain ⟨source, tail⟩ := walk
    have suffix := ih tail (fun x hx => increases x (List.mem_cons_of_mem _ hx))
    have step := increases e (List.mem_cons_self ..)
    rw [source] at step
    constructor
    · intro x member
      rcases List.mem_cons.mp member with rfl | member
      · exact step
      · exact trans step (suffix.1 x member)
    · exact List.pairwise_cons.mpr ⟨suffix.1, suffix.2⟩

/-- Balance forces the links of an already scheduled history; they are not hypotheses.
The supplied order need only compare versions of records at the same resource key. -/
theorem walk_of_ordered_balance (rows : List Edge) (edge : Edge → Vertex × Vertex)
    (before : Vertex → Vertex → Prop) (irrefl : ∀ a, ¬ before a a) (trans : ∀ ⦃a b c⦄, before a b → before b c → before a c)
    (initial final : Vertex) (balanced : EndpointBalanced (↑rows) edge initial final)
    (increases : ∀ e ∈ rows, before (edge e).1 (edge e).2)
    (ordered : rows.Pairwise (fun a b => before (edge a).2 (edge b).2)) :
    IsWalk edge initial final rows := by
  obtain ⟨path, walk, exhaustive⟩ := exhaustive_of_acyclic (↑rows) edge initial final balanced
    (acyclic_of_strict (↑rows) edge before irrefl trans increases)
  have perm : path.Perm rows := Multiset.coe_eq_coe.mp exhaustive
  have sorted := (targets_ordered_of_walk edge before trans walk
    (fun e member => increases e (perm.mem_iff.mp member))).2
  have equal : path = rows := perm.eq_of_pairwise
    (fun a _ b _ ab ba => (irrefl _ (trans ab ba)).elim) sorted ordered
  rwa [equal] at walk

omit [DecidableEq Edge] [DecidableEq Vertex] in
/-- Remove only transitions that are identities after a proved state projection.
This is applied before ranking real events; administrative representation changes
need not advance the architectural clock. -/
theorem balance_filter_project {Logical : Type*} (edges : Multiset Edge)
    (edge : Edge → Vertex × Vertex) (project : Vertex → Logical) (keep : Edge → Bool)
    (initial final : Vertex) (balanced : EndpointBalanced edges edge initial final)
    (silent : ∀ e ∈ edges, keep e = false → project (edge e).1 = project (edge e).2) :
    EndpointBalanced (edges.filter fun e => keep e = true)
      (fun e => (project (edge e).1, project (edge e).2)) (project initial) (project final) := by
  have projected := balanced.map edges edge initial final project
  have split := Multiset.filter_add_not (fun e => keep e = true) edges
  have silentMap : (edges.filter fun e => ¬keep e = true).map (fun e => project (edge e).2) =
      (edges.filter fun e => ¬keep e = true).map (fun e => project (edge e).1) := by
    apply Multiset.map_congr rfl
    intro e member
    obtain ⟨member, disabled⟩ := Multiset.mem_filter.mp member
    exact (silent e member (Bool.eq_false_iff.mpr disabled)).symm
  rw [← split] at projected
  simp only [EndpointBalanced, Multiset.map_add, ← Multiset.cons_add] at projected
  rw [silentMap] at projected
  exact add_right_cancel projected

end Utils.ResourceHistory
