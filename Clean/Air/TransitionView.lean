module

public import Clean.Air.FlatEnsemble
public import Clean.Air.UnitBalance

/-! # Reading transitions from physical AIR tables

`TransitionView` records the exact interaction equation for a single unit pull/push pair.
The physical readers preserve occurrences and transport local specifications under complete
component registration alignment. `LedgerView` provides gated and multi-access extensions. -/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]
variable {Message : TypeMap} [ProvableType Message]

/-- A view of a component's actual pull/push pair on one channel. -/
structure TransitionView (channel : Channel F Message) where
  component : Component F
  edge : Environment F → Message F × Message F
  interactions : ∀ env, component.operations.interactionValuesWith channel.toRaw env =
    [channel.pulledValue (edge env).1, channel.pushedValue (edge env).2]

namespace TransitionView

variable {channel : Channel F Message}

/-- Preserve a registry's finite component identity while reading physical environments. -/
def readIndexedRows {Index : Type*} (indices : List Index) (tables : List (Table F)) :
    List (Index × Environment F) :=
  (indices.zip tables).flatMap fun (index, table) =>
    table.table.map fun row => (index, table.environment row)

/-- Keep the component identity with each physical row; different row layouts stay separate. -/
def readRows (views : List (TransitionView channel)) (tables : List (Table F)) :
    List (TransitionView channel × Environment F) :=
  (views.zip tables).flatMap fun (view, table) =>
    table.table.map fun row => (view, table.environment row)

/-- Reading physical environments preserves every interaction, on any selected channel. -/
theorem readIndexedRows_interactions {Index : Type*} (indices : List Index)
    (component : Index → Component F) (tables : List (Table F)) (selected : RawChannel F)
    (aligned : List.Forall₂ (fun index table => component index = table.component) indices tables) :
    tables.flatMap (·.interactionsWith selected) =
      (readIndexedRows indices tables).flatMap (fun (index, env) =>
        (component index).operations.interactionValuesWith selected env) := by
  induction aligned with
  | nil => rfl
  | @cons index table indices tables same _ ih =>
    simp only [readIndexedRows, List.zip_cons_cons, List.flatMap_cons, List.flatMap_append,
      List.flatMap_map] at ih ⊢
    rw [ih]
    congr 1
    unfold Table.interactionsWith
    rw [same]

theorem readRows_eq_indexed {Index : Type*} (indices : List Index)
    (view : Index → TransitionView channel) (tables : List (Table F)) :
    readRows (indices.map view) tables =
      (readIndexedRows indices tables).map (fun (index, env) => (view index, env)) := by
  induction indices generalizing tables with
  | nil => simp [readRows, readIndexedRows]
  | cons index indices ih =>
    cases tables with
    | nil => simp [readRows, readIndexedRows]
    | cons table tables =>
      simp only [readRows, readIndexedRows, List.map_cons, List.zip_cons_cons, List.flatMap_cons,
        List.map_append, List.map_map, Function.comp_def] at ih ⊢
      rw [ih]

theorem readRows_view_mem (views : List (TransitionView channel)) (tables : List (Table F))
    (row : TransitionView channel × Environment F) (member : row ∈ readRows views tables) :
    row.1 ∈ views := by
  obtain ⟨⟨view, table⟩, paired, mapped⟩ := List.mem_flatMap.mp member
  obtain ⟨physical, _, rfl⟩ := List.mem_map.mp mapped
  exact (List.of_mem_zip paired).1

/-- Component alignment, including list length, follows from Clean's witness component equation. -/
theorem aligned_of_map_eq (views : List (TransitionView channel)) (tables : List (Table F))
    (aligned : views.map (·.component) = tables.map (·.component)) :
    List.Forall₂ (fun view table => view.component = table.component) views tables := by
  have equal : List.Forall₂ (· = ·) (views.map (·.component)) (tables.map (·.component)) := by
    simp only [List.forall₂_eq_eq_eq]
    exact aligned
  simp only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at equal
  exact equal

/-- The decoded transitions retain every physical row's actual interactions. -/
theorem readRows_interactions (views : List (TransitionView channel)) (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables) :
    tables.flatMap (·.interactionsWith channel.toRaw) =
      (readRows views tables).flatMap (fun (view, env) =>
        [channel.pulledValue (view.edge env).1, channel.pushedValue (view.edge env).2]) := by
  induction aligned with
  | nil => rfl
  | @cons view table views tables same _ ih =>
    simp only [readRows, List.zip_cons_cons, List.flatMap_cons, List.flatMap_append,
      List.flatMap_map] at ih ⊢
    rw [ih]
    congr 1
    unfold Table.interactionsWith
    congr 1
    funext row
    rw [← same, view.interactions]

/-- A table specification applies to the very environment used to read its transitions. -/
theorem readRows_spec (views : List (TransitionView channel)) (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables)
    (valid : ∀ table ∈ tables, table.Spec) :
    ∀ row ∈ readRows views tables, row.1.component.Spec row.2 := by
  induction aligned with
  | nil => simp [readRows]
  | @cons view table views tables same _ ih =>
    intro row member
    simp only [readRows, List.zip_cons_cons, List.flatMap_cons, List.mem_append, List.mem_map] at member
    rcases member with ⟨physical, member, rfl⟩ | member
    · rw [same]
      exact valid table (by simp) physical member
    · exact ih (fun table member => valid table (List.mem_cons_of_mem _ member)) row member

theorem readIndexedRows_spec {Index : Type*} (indices : List Index)
    (view : Index → TransitionView channel) (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) (indices.map view) tables)
    (valid : ∀ table ∈ tables, table.Spec) :
    ∀ row ∈ readIndexedRows indices tables, (view row.1).component.Spec row.2 := by
  intro row member
  have specs := readRows_spec (indices.map view) tables aligned valid
  rw [readRows_eq_indexed] at specs
  exact specs (view row.1, row.2) (List.mem_map.mpr ⟨row, member, rfl⟩)

theorem readIndexedRows_keys_nodup {Index Key : Type*} (indices : List Index)
    (view : Index → TransitionView channel) (tables : List (Table F)) (key : Message F → Key)
    (registered : List (TransitionView channel)) (same : registered = indices.map view)
    (unique : ((readRows registered tables).map fun row => key (row.1.edge row.2).2).Nodup) :
    ((readIndexedRows indices tables).map fun row => key ((view row.1).edge row.2).2).Nodup := by
  rw [same, readRows_eq_indexed] at unique
  simp only [List.map_map, Function.comp_def] at unique
  exact unique

end TransitionView
end Air.Flat
