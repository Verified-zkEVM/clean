module

public import Clean.Air.TransitionView

/-! # Selecting complete message classes and physical rows

Filtering solely by complete payload preserves balance and its characteristic bound.
Physical-row selection preserves component identity, prover data, and evaluation environments;
its connection to message filtering must be proved. -/

@[expose] public section

variable {F : Type}

section Balance
variable [FiniteField F] [DecidableEq F]

/-- Selecting by payload retains either every occurrence of a message or none of them. -/
theorem balanceOf_filter_messages (interactions : List (Interaction F)) (keep : Array F → Bool)
    (message : Array F) :
    balanceOf (interactions.filter fun interaction => keep interaction.msg) message =
      if keep message then balanceOf interactions message else 0 := by
  induction interactions with
  | nil => simp [balanceOf]
  | cons head rest ih =>
    by_cases same : head.msg = message
    · simp only [List.filter_cons, balanceOf_cons, same]
      cases selected : keep message <;> simp [selected, balanceOf_cons, same, ih]
    · cases selected : keep head.msg <;> cases wanted : keep message <;>
        simp [selected, wanted, balanceOf_cons, same, ih]

/-- Global balance restricts to any class of complete payloads, with its count guard intact. -/
theorem BalancedInteractions.filter_messages {interactions : List (Interaction F)}
    (balanced : BalancedInteractions interactions) (keep : Array F → Bool) :
    BalancedInteractions (interactions.filter fun interaction => keep interaction.msg) := by
  refine ⟨?_, ?_⟩
  · exact balanced.1.imp (lt_of_le_of_lt (List.length_filter_le ..)) id
  · intro message
    rw [balanceOf_filter_messages, balanced.2]
    simp

end Balance

namespace ProvableType

variable {Message : TypeMap} [ProvableType Message]

/-- Decode only correctly sized payloads when selecting a typed message class. -/
def selectMessage (keep : Message F → Bool) (message : Array F) : Bool :=
  if bound : message.size = size Message then keep (fromElements ⟨message, bound⟩) else false

theorem selectMessage_toElements (keep : Message F → Bool) (message : Message F) :
    selectMessage keep (toElements message).toArray = keep message := by
  simp only [selectMessage, Vector.size_toArray, ↓reduceDIte]
  exact congrArg keep (fromElements_toElements message)

end ProvableType

namespace Air.Flat.Table

variable [FiniteField F]

/-- Retain complete physical rows; their environments and prover data are unchanged. -/
def filterRows (table : Table F) (keep : Environment F → Bool) : Table F :=
  { table with
    table := table.table.filter fun row => keep (table.environment row)
    uniform_width := fun row member => table.uniform_width row (List.mem_filter.mp member).1 }

theorem filterRows_spec (table : Table F) (keep : Environment F → Bool) (valid : table.Spec) :
    (table.filterRows keep).Spec := by
  intro row member
  exact valid row (List.mem_filter.mp member).1

/-- A homogeneous row is retained exactly when its actual interactions are selected. -/
theorem filterRows_interactions (table : Table F) (channel : RawChannel F)
    (keep : Environment F → Bool) (select : Array F → Bool)
    (homogeneous : ∀ row ∈ table.table, ∀ interaction ∈
      table.component.operations.interactionValuesWith channel (table.environment row),
      select interaction.msg = keep (table.environment row)) :
    (table.filterRows keep).interactionsWith channel =
      (table.interactionsWith channel).filter (fun interaction => select interaction.msg) := by
  simp only [interactionsWith, filterRows, environment]
  generalize table.table = rows at homogeneous ⊢
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have same := homogeneous row (List.mem_cons_self ..)
    have rest := ih (fun other member => homogeneous other (List.mem_cons_of_mem _ member))
    have selected :
        (table.component.operations.interactionValuesWith channel (table.environment row)).filter
          (fun interaction => select interaction.msg) =
        if keep (table.environment row) then
          table.component.operations.interactionValuesWith channel (table.environment row) else [] := by
      rw [List.filter_congr (fun interaction present => same interaction present)]
      cases keep (table.environment row) <;> simp
    simp only [environment] at selected
    simp only [List.filter_cons, List.flatMap_cons, List.filter_append]
    rw [selected]
    obtain hk | hk := Bool.eq_false_or_eq_true (keep (Environment.fromArray row table.data)) <;>
      simp [hk, rest]

end Air.Flat.Table

namespace Air.Flat.TransitionView

variable [FiniteField F]
variable {Index : Type*}

/-- A transition preserving a message class can be selected as a whole physical row. -/
theorem filterRows_interactions {Message : TypeMap} [ProvableType Message] {channel : Channel F Message}
    (view : TransitionView channel) (table : Table F) (aligned : view.component = table.component)
    (keep : Message F → Bool) (preserved : ∀ env, keep (view.edge env).2 = keep (view.edge env).1) :
    (table.filterRows (fun env => keep (view.edge env).1)).interactionsWith channel.toRaw =
      (table.interactionsWith channel.toRaw).filter
        (fun interaction => ProvableType.selectMessage keep interaction.msg) := by
  apply table.filterRows_interactions
  intro physical _ interaction member
  rw [← aligned, view.interactions] at member
  rcases List.mem_cons.mp member with equal | member
  · rw [equal]
    exact ProvableType.selectMessage_toElements _ _
  · rw [List.mem_singleton.mp member]
    exact (ProvableType.selectMessage_toElements _ _).trans (preserved _)

/-- Select a row class separately in each registered component, retaining empty tables. -/
def selectTables (indices : List Index) (tables : List (Table F))
    (keep : Index → Environment F → Bool) : List (Table F) :=
  (indices.zip tables).map fun (index, table) => table.filterRows (keep index)

theorem selectTables_aligned (indices : List Index) (tables : List (Table F))
    (component : Index → Component F) (keep : Index → Environment F → Bool)
    (aligned : List.Forall₂ (fun index table => component index = table.component) indices tables) :
    List.Forall₂ (fun index table => component index = table.component) indices
      (selectTables indices tables keep) := by
  induction aligned with
  | nil => exact .nil
  | cons same _ ih => exact .cons same ih

theorem selectTables_spec (indices : List Index) (tables : List (Table F))
    (keep : Index → Environment F → Bool) (valid : ∀ table ∈ tables, table.Spec) :
    ∀ table ∈ selectTables indices tables keep, table.Spec := by
  intro table member
  obtain ⟨⟨index, original⟩, paired, rfl⟩ := List.mem_map.mp member
  exact original.filterRows_spec (keep index) (valid original (List.of_mem_zip paired).2)

/-- Selection commutes with decoding and preserves physical occurrences and their order. -/
theorem readIndexedRows_selectTables (indices : List Index) (tables : List (Table F))
    (keep : Index → Environment F → Bool) :
    readIndexedRows indices (selectTables indices tables keep) =
      (readIndexedRows indices tables).filter (fun (index, env) => keep index env) := by
  induction indices generalizing tables with
  | nil => simp [readIndexedRows, selectTables]
  | cons index indices ih =>
    cases tables with
    | nil => simp [readIndexedRows, selectTables]
    | cons table tables =>
      simp only [selectTables, List.zip_cons_cons, List.map_cons, readIndexedRows, List.flatMap_cons,
        List.filter_append] at ih ⊢
      rw [ih]
      congr 1
      simp only [Table.filterRows, Table.environment, List.filter_map, Function.comp_def]

/-- Selecting physical rows preserves the source of every interaction, on any channel. -/
theorem selectTables_interactions_sublist (indices : List Index) (tables : List (Table F))
    (component : Index → Component F) (keep : Index → Environment F → Bool) (channel : RawChannel F)
    (aligned : List.Forall₂ (fun index table => component index = table.component) indices tables) :
    ((selectTables indices tables keep).flatMap (·.interactionsWith channel)).Sublist
      (tables.flatMap (·.interactionsWith channel)) := by
  rw [readIndexedRows_interactions indices component _ channel
    (selectTables_aligned indices tables component keep aligned),
    readIndexedRows_interactions indices component tables channel aligned,
    readIndexedRows_selectTables]
  exact List.filter_sublist.flatMap _

end Air.Flat.TransitionView
