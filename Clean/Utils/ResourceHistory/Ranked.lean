module

public import Clean.Utils.ResourceHistory.Walk
public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-! # Ranked balance gives an exhaustive trail

Endpoint balance produces a subtrail; disconnected balanced cycles may remain.
If every edge strictly increases a natural-number rank, no nonempty balanced residue
can exist. The extracted trail therefore contains every supplied edge occurrence.

The resulting trail has strictly ordered source ranks, giving occurrence uniqueness
and an order suitable for subsequent induction over local transition semantics. -/

@[expose] public section

namespace Utils.ResourceHistory.Ranked

open Utils.ResourceHistory.Walk

universe u v

variable {Edge : Type u} {Vertex : Type v} [DecidableEq Edge] [DecidableEq Vertex]

/-- Balance as equality of produced and consumed endpoint multisets.  For transitions
`source → target`, the boundary contributes the initial source on the produced side and the final
target on the consumed side. -/
def EndpointBalanced (edges : Multiset Edge) (edge : Edge → Vertex × Vertex)
    (initial final : Vertex) : Prop :=
  initial ::ₘ edges.map (fun row => (edge row).2) =
    final ::ₘ edges.map (fun row => (edge row).1)

omit [DecidableEq Edge] in
/-- Degree balance and endpoint-multiset balance are equivalent presentations.  This direction lets
the existing Eulerian extraction theorem feed the ranked exhaustiveness argument without another
trusted graph premise. -/
theorem endpointBalanced_of_balanced (edges : Multiset Edge) (edge : Edge → Vertex × Vertex)
    (initial final : Vertex) (balanced : Balanced edges edge initial final) :
    EndpointBalanced edges edge initial final := by
  apply Multiset.ext.mpr
  intro vertex
  simp only [Multiset.count_cons, Multiset.count_map]
  have sourceFilter :
      edges.filter (fun row => vertex = (edge row).1) =
        edges.filter (fun row => (edge row).1 = vertex) := by
    simp only [eq_comm]
  have targetFilter :
      edges.filter (fun row => vertex = (edge row).2) =
        edges.filter (fun row => (edge row).2 = vertex) := by
    simp only [eq_comm]
  rw [sourceFilter, targetFilter]
  have h := balanced vertex
  simp only [outdeg, indeg] at h
  by_cases hif : initial = final
  · subst final
    simp at h ⊢
    omega
  · by_cases hi : vertex = initial
    · simp [hif, hi] at h ⊢
      omega
    · have hif' : final ≠ initial := Ne.symm hif
      by_cases hf : vertex = final <;> simp [hi, hf, hif'] at h ⊢ <;> omega

omit [DecidableEq Edge] in
/-- Endpoint-multiset balance implies the degree presentation used by the trail extractor. -/
theorem balanced_of_endpointBalanced (edges : Multiset Edge) (edge : Edge → Vertex × Vertex)
    (initial final : Vertex) (balanced : EndpointBalanced edges edge initial final) :
    Balanced edges edge initial final := by
  intro vertex
  have counts := congrArg (Multiset.count vertex) balanced
  simp only [Multiset.count_cons, Multiset.count_map] at counts
  have sourceFilter :
      edges.filter (fun row => vertex = (edge row).1) =
        edges.filter (fun row => (edge row).1 = vertex) := by
    simp only [eq_comm]
  have targetFilter :
      edges.filter (fun row => vertex = (edge row).2) =
        edges.filter (fun row => (edge row).2 = vertex) := by
    simp only [eq_comm]
  rw [sourceFilter, targetFilter] at counts
  simp only [outdeg, indeg]
  by_cases hif : initial = final
  · subst final
    simp at counts ⊢
    omega
  · by_cases hi : vertex = initial
    · simp [hif, hi] at counts ⊢
      omega
    · have hif' : final ≠ initial := Ne.symm hif
      by_cases hf : vertex = final <;> simp [hi, hf, hif'] at counts ⊢ <;> omega

omit [DecidableEq Edge] [DecidableEq Vertex] in
/-- Every walk has the expected telescoping endpoint-multiset balance. -/
theorem endpointBalanced_of_isWalk (edge : Edge → Vertex × Vertex) :
    ∀ {initial final : Vertex} {path : List Edge}, IsWalk edge initial final path →
      EndpointBalanced (↑path) edge initial final
  | initial, final, [], walk => by
      simp only [IsWalk] at walk
      simp [EndpointBalanced, walk]
  | initial, final, row :: rest, walk => by
      obtain ⟨source, tail⟩ := walk
      have ih := endpointBalanced_of_isWalk edge tail
      change (edge row).2 ::ₘ (↑rest : Multiset Edge).map (fun row => (edge row).2) =
        final ::ₘ (↑rest : Multiset Edge).map (fun row => (edge row).1) at ih
      change initial ::ₘ (edge row).2 ::ₘ (↑rest : Multiset Edge).map (fun row => (edge row).2) =
        final ::ₘ (edge row).1 ::ₘ (↑rest : Multiset Edge).map (fun row => (edge row).1)
      rw [← source, Multiset.cons_swap final (edge row).1]
      exact congrArg (Multiset.cons (edge row).1) ih

omit [DecidableEq Vertex] in
/-- A strictly ranked edge multiset has no nonempty balanced cycle. -/
theorem eq_zero_of_endpointBalanced_self (edges : Multiset Edge)
    (edge : Edge → Vertex × Vertex) (rank : Vertex → ℕ) {initial : Vertex}
    (increases : ∀ row ∈ edges, rank (edge row).1 < rank (edge row).2)
    (balanced : EndpointBalanced edges edge initial initial) :
    edges = 0 := by
  have endpointEq : edges.map (fun row => (edge row).2) =
      edges.map (fun row => (edge row).1) :=
    (Multiset.cons_inj_right initial).mp balanced
  by_contra nonempty
  obtain ⟨row, member⟩ := Multiset.exists_mem_of_ne_zero nonempty
  have sumLt :
      (edges.map fun row => rank (edge row).1).sum <
        (edges.map fun row => rank (edge row).2).sum :=
    Multiset.sum_lt_sum
      (fun row member => (increases row member).le)
      ⟨row, member, increases row member⟩
  have sumEq :
      (edges.map fun row => rank (edge row).2).sum =
        (edges.map fun row => rank (edge row).1).sum := by
    have mapped := congrArg (fun rows : Multiset Vertex => (rows.map rank).sum) endpointEq
    simp only [Multiset.map_map, Function.comp_apply] at mapped
    exact mapped
  omega

/-- A trail that uses every edge exactly once.  Equality as a multiset permits the path order to be
derived rather than assumed while retaining duplicate row labels faithfully. -/
def ExhaustiveTrail (edges : Multiset Edge) (edge : Edge → Vertex × Vertex)
    (initial final : Vertex) : Prop :=
  ∃ path : List Edge, IsWalk edge initial final path ∧ (↑path : Multiset Edge) = edges

/-- **Ranked balance ⇒ exhaustive trail.**  The older balance theorem yields a subtrail.  Subtracting
it leaves a balanced cycle; strict rank increase forces that residue to be empty. -/
theorem exists_exhaustiveTrail (edges : Multiset Edge) (edge : Edge → Vertex × Vertex)
    (rank : Vertex → ℕ) (initial final : Vertex)
    (balanced : Balanced edges edge initial final)
    (increases : ∀ row ∈ edges, rank (edge row).1 < rank (edge row).2) :
    ExhaustiveTrail edges edge initial final := by
  obtain ⟨path, walk, subtrail⟩ := exists_trail edge edges initial final balanced
  obtain ⟨residue, decomposition⟩ := Multiset.le_iff_exists_add.mp subtrail
  have wholeEndpoints := endpointBalanced_of_balanced edges edge initial final balanced
  have pathEndpoints := endpointBalanced_of_isWalk edge walk
  have residueEndpoints : EndpointBalanced residue edge final final := by
    rw [decomposition] at wholeEndpoints
    simp only [EndpointBalanced, Multiset.map_add] at wholeEndpoints pathEndpoints ⊢
    have whole' :
        (initial ::ₘ (↑path : Multiset Edge).map (fun row => (edge row).2)) +
            residue.map (fun row => (edge row).2) =
          (final ::ₘ (↑path : Multiset Edge).map (fun row => (edge row).1)) +
            residue.map (fun row => (edge row).1) := by
      rw [Multiset.cons_add, Multiset.cons_add]
      exact wholeEndpoints
    rw [pathEndpoints] at whole'
    exact congrArg (Multiset.cons final) (add_left_cancel whole')
  have residueIncrease : ∀ row ∈ residue, rank (edge row).1 < rank (edge row).2 := by
    intro row member
    apply increases row
    rw [decomposition]
    exact Multiset.mem_add.mpr (Or.inr member)
  have residueEmpty :=
    eq_zero_of_endpointBalanced_self residue edge rank residueIncrease residueEndpoints
  refine ⟨path, walk, ?_⟩
  rw [residueEmpty, add_zero] at decomposition
  exact decomposition.symm

/-- Direct endpoint-balance API for the grounding engine.  Degree balance remains an internal detail
of the existing trail extractor; callers need only the message permutation produced by a channel. -/
theorem exists_exhaustiveTrail_of_endpointBalanced (edges : Multiset Edge)
    (edge : Edge → Vertex × Vertex) (rank : Vertex → ℕ) (initial final : Vertex)
    (balanced : EndpointBalanced edges edge initial final)
    (increases : ∀ row ∈ edges, rank (edge row).1 < rank (edge row).2) :
    ExhaustiveTrail edges edge initial final :=
  exists_exhaustiveTrail edges edge rank initial final
    (balanced_of_endpointBalanced edges edge initial final balanced) increases

omit [DecidableEq Edge] [DecidableEq Vertex] in
private theorem targets_pairwise_of_isWalk (edge : Edge → Vertex × Vertex) (rank : Vertex → ℕ)
    {initial final : Vertex} {path : List Edge} (walk : IsWalk edge initial final path)
    (increases : ∀ row ∈ path, rank (edge row).1 < rank (edge row).2) :
    (∀ row ∈ path, rank initial < rank (edge row).2) ∧
      (path.map fun row => (edge row).2).Pairwise (fun a b => rank a < rank b) := by
  induction path generalizing initial with
  | nil => simp
  | cons row rest ih =>
      obtain ⟨source, tail⟩ := walk
      have next := increases row (List.mem_cons_self ..)
      have suffix := ih tail (fun other member => increases other (List.mem_cons_of_mem _ member))
      constructor
      · intro other member
        rcases List.mem_cons.mp member with rfl | member
        · rw [source] at next
          exact next
        · exact lt_trans (source ▸ next) (suffix.1 other member)
      · rw [List.map_cons, List.pairwise_cons]
        refine ⟨?_, suffix.2⟩
        intro vertex member
        obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp member
        exact suffix.1 other otherMember

/-- Balance and a strict local rank force destination uniqueness. This is the boundary-provider
payoff: assigning each address to the target of an ordered control edge rules out duplicate
initial/final records, including identical duplicate rows in the witness multiset. -/
theorem targets_nodup_of_endpointBalanced (edges : Multiset Edge)
    (edge : Edge → Vertex × Vertex) (rank : Vertex → ℕ) (initial final : Vertex)
    (balanced : EndpointBalanced edges edge initial final)
    (increases : ∀ row ∈ edges, rank (edge row).1 < rank (edge row).2) :
    (edges.map fun row => (edge row).2).Nodup := by
  obtain ⟨path, walk, exhaustive⟩ :=
    exists_exhaustiveTrail_of_endpointBalanced edges edge rank initial final balanced increases
  have sorted := (targets_pairwise_of_isWalk edge rank walk (fun row member =>
    increases row (exhaustive ▸ Multiset.mem_coe.mpr member))).2
  have unique : (path.map fun row => (edge row).2).Nodup :=
    sorted.imp (fun smaller => fun equal => (ne_of_lt smaller) (congrArg rank equal))
  rw [← exhaustive, Multiset.map_coe, Multiset.coe_nodup]
  exact unique

omit [DecidableEq Edge] [DecidableEq Vertex] in
/-- Endpoint balance survives any projection of the structural channel key. -/
theorem EndpointBalanced.map {Other : Type*} (edges : Multiset Edge)
    (edge : Edge → Vertex × Vertex) (initial final : Vertex)
    (balanced : EndpointBalanced edges edge initial final) (project : Vertex → Other) :
    EndpointBalanced edges (fun row => (project (edge row).1, project (edge row).2))
      (project initial) (project final) := by
  have mapped := congrArg (Multiset.map project) balanced
  simp only [Multiset.map_cons, Multiset.map_map, Function.comp_apply] at mapped
  exact mapped

omit [DecidableEq Vertex] in
/-- Keys tied to a destination rank inherit uniqueness, without requiring an injective encoding
or a caller-supplied uniqueness premise. -/
theorem keys_nodup_of_endpointBalanced {Key : Type*} (edges : Multiset Edge)
    (edge : Edge → Vertex × Vertex) (rank : Vertex → ℕ) (key : Edge → Key) (encode : Key → ℕ)
    (initial final : Vertex) (balanced : EndpointBalanced edges edge initial final)
    (increases : ∀ row ∈ edges, rank (edge row).1 < rank (edge row).2)
    (keyEq : ∀ row ∈ edges, rank (edge row).2 = encode (key row)) :
    (edges.map key).Nodup := by
  have projected := balanced.map edges edge initial final rank
  have unique := targets_nodup_of_endpointBalanced edges _ id _ _ projected increases
  have mapped : edges.map (fun row => rank (edge row).2) = (edges.map key).map encode := by
    rw [Multiset.map_map]
    apply Multiset.map_congr rfl
    exact keyEq
  rw [mapped] at unique
  exact Multiset.Nodup.of_map _ unique

omit [DecidableEq Vertex] in
/-- List form of distinct destination ranks. The list-to-multiset transport is checked over
opaque rows, so applications to decoded physical AIR tables do not unfold their decoders. -/
theorem rankedKeys_nodup_list (rows : List Edge) (edge : Edge → Vertex × Vertex)
    (rank : Vertex → ℕ) (initial final : Vertex)
    (balanced : EndpointBalanced (↑rows : Multiset Edge) edge initial final)
    (strict : ∀ row ∈ rows, rank (edge row).1 < rank (edge row).2) :
    (rows.map fun row => rank (edge row).2).Nodup := by
  exact keys_nodup_of_endpointBalanced _ edge rank
    (fun row => rank (edge row).2) id initial final balanced strict (fun _ _ => rfl)

omit [DecidableEq Edge] [DecidableEq Vertex] in
private theorem sources_pairwise_of_isWalk (edge : Edge → Vertex × Vertex) (rank : Vertex → ℕ)
    {initial final : Vertex} {path : List Edge} (walk : IsWalk edge initial final path)
    (increases : ∀ row ∈ path, rank (edge row).1 < rank (edge row).2) :
    (∀ row ∈ path, rank initial ≤ rank (edge row).1) ∧
      (path.map fun row => rank (edge row).1).Pairwise (· < ·) := by
  induction path generalizing initial with
  | nil => simp
  | cons row rest ih =>
    obtain ⟨source, tail⟩ := walk
    have next := increases row (List.mem_cons_self ..)
    have suffix := ih tail (fun other member => increases other (List.mem_cons_of_mem _ member))
    constructor
    · intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact le_of_eq (congrArg rank source.symm)
      · exact le_trans (le_of_lt (source ▸ next)) (suffix.1 other member)
    · rw [List.map_cons, List.pairwise_cons]
      refine ⟨?_, suffix.2⟩
      intro value member
      obtain ⟨other, otherMember, rfl⟩ := List.mem_map.mp member
      exact lt_of_lt_of_le next (suffix.1 other otherMember)

omit [DecidableEq Edge] [DecidableEq Vertex] in
/-- Strict clock progress makes every event's incoming rank distinct, including duplicate
physical occurrences. No assumption about the initial rank or a terminal instruction is needed. -/
theorem sourceRanks_nodup_of_isWalk (edge : Edge → Vertex × Vertex) (rank : Vertex → ℕ)
    {initial final : Vertex} {path : List Edge} (walk : IsWalk edge initial final path)
    (increases : ∀ row ∈ path, rank (edge row).1 < rank (edge row).2) :
    (path.map fun row => rank (edge row).1).Nodup :=
  (sources_pairwise_of_isWalk edge rank walk increases).2.imp ne_of_lt

omit [DecidableEq Edge] [DecidableEq Vertex] in
/-- Incoming ranks follow the order of the walk, not the physical table order. -/
theorem sourceRanks_pairwise_of_isWalk (edge : Edge → Vertex × Vertex) (rank : Vertex → ℕ)
    {initial final : Vertex} {path : List Edge} (walk : IsWalk edge initial final path)
    (increases : ∀ row ∈ path, rank (edge row).1 < rank (edge row).2) :
    (path.map fun row => rank (edge row).1).Pairwise (· < ·) :=
  (sources_pairwise_of_isWalk edge rank walk increases).2

omit [DecidableEq Edge] [DecidableEq Vertex] in
/-- Destination ranks also follow the walk; a protocol can stamp its successor with event time. -/
theorem targetRanks_pairwise_of_isWalk (edge : Edge → Vertex × Vertex) (rank : Vertex → ℕ)
    {initial final : Vertex} {path : List Edge} (walk : IsWalk edge initial final path)
    (increases : ∀ row ∈ path, rank (edge row).1 < rank (edge row).2) :
    (path.map fun row => rank (edge row).2).Pairwise (· < ·) := by
  have ordered := (targets_pairwise_of_isWalk edge rank walk increases).2
  simp only [List.pairwise_map] at ordered ⊢
  exact ordered

end Utils.ResourceHistory.Ranked
