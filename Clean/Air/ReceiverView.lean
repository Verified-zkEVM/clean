module

public import Clean.Air.TransitionView

/-! # Exact physical receiver inventories

A receiver view ties typed unit requests to the component's actual evaluated interactions.
The inventory retains physical repetitions and registration boundaries. -/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F]
variable {Message : TypeMap} [ProvableType Message]

/-- One physical row consumes exactly one complete typed message. -/
structure ReceiverView (channel : Channel F Message) where
  component : Component F
  message : Environment F → Message F
  interactions : ∀ env, component.operations.interactionValuesWith channel.toRaw env =
    [channel.pulledValue (message env)]

namespace ReceiverView

variable {channel : Channel F Message}

def tableMessages (view : ReceiverView channel) (table : Table F) : List (Message F) :=
  table.table.map fun physical => view.message (table.environment physical)

/-- Read every physical occurrence, preserving the registered component identity. -/
def messages (views : List (ReceiverView channel)) (tables : List (Table F)) : List (Message F) :=
  (TransitionView.readIndexedRows views tables).map fun (view, env) => view.message env

theorem messages_cons (view : ReceiverView channel) (views : List (ReceiverView channel))
    (table : Table F) (tables : List (Table F)) :
    messages (view :: views) (table :: tables) = tableMessages view table ++ messages views tables := by
  simp only [messages, TransitionView.readIndexedRows, List.zip_cons_cons, List.flatMap_cons,
    List.map_append, List.map_map, Function.comp_def, tableMessages]

/-- Split the physical receiver inventory at a registration boundary. -/
theorem messages_take_drop (views : List (ReceiverView channel)) (tables : List (Table F)) (n : ℕ) :
    messages views tables = messages (views.take n) (tables.take n) ++
      messages (views.drop n) (tables.drop n) := by
  unfold messages TransitionView.readIndexedRows
  conv_lhs => rw [← List.take_append_drop n (views.zip tables)]
  simp only [List.zip_eq_zipWith, List.take_zipWith, List.drop_zipWith,
    List.flatMap_append, List.map_append]

theorem aligned_of_map_eq (views : List (ReceiverView channel)) (tables : List (Table F))
    (aligned : views.map (·.component) = tables.map (·.component)) :
    List.Forall₂ (fun view table => view.component = table.component) views tables := by
  have equal : List.Forall₂ (· = ·) (views.map (·.component)) (tables.map (·.component)) := by
    simp only [List.forall₂_eq_eq_eq]
    exact aligned
  simp only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at equal
  exact equal

/-- The typed inventory is exactly the complete physical ledger, including multiplicities. -/
theorem messages_interactions (views : List (ReceiverView channel)) (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables) :
    tables.flatMap (·.interactionsWith channel.toRaw) = (messages views tables).map channel.pulledValue := by
  rw [TransitionView.readIndexedRows_interactions views (·.component) tables channel.toRaw aligned]
  simp only [interactions, messages, List.map_map, Function.comp_def]
  exact List.flatMap_pure_eq_map _ _

/-- An actual unit pull identifies its complete typed message in the receiver inventory. -/
theorem message_mem_of_pull_mem (views : List (ReceiverView channel)) (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables)
    (message : Message F)
    (member : channel.pulledValue message ∈ tables.flatMap (·.interactionsWith channel.toRaw)) :
    message ∈ messages views tables := by
  rw [messages_interactions views tables aligned] at member
  obtain ⟨other, present, equal⟩ := List.mem_map.mp member
  have encoded := Vector.toArray_inj.mp (congrArg Interaction.msg equal)
  have same : other = message := by
    have decoded := congrArg fromElements encoded
    simp only [ProvableType.fromElements_toElements] at decoded
    exact decoded
  exact same ▸ present

/-- A registered receiver's physical occurrences form a sublist of the complete inventory. -/
theorem tableMessages_sublist (views : List (ReceiverView channel)) (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables)
    (index : ℕ) (bound : index < views.length) :
    (tableMessages views[index] (tables[index]'(by rw [← aligned.length_eq]; exact bound))).Sublist
      (messages views tables) := by
  induction aligned generalizing index with
  | nil => simp at bound
  | @cons view table views tables same aligned ih =>
    cases index with
    | zero =>
      simp only [List.getElem_cons_zero, messages_cons]
      exact List.sublist_append_left _ _
    | succ index =>
      simp only [List.getElem_cons_succ, messages_cons]
      exact (ih index (by simp only [List.length_cons, Nat.succ_lt_succ_iff] at bound; exact bound)).trans (List.sublist_append_right _ _)

/-- Global message-key uniqueness applies to every physical row of any registered receiver. -/
theorem tableMessages_keys_nodup {Key : Type*} (views : List (ReceiverView channel))
    (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables)
    (key : Message F → Key) (unique : ((messages views tables).map key).Nodup)
    (index : ℕ) (bound : index < views.length) :
    ((tableMessages views[index] (tables[index]'(by rw [← aligned.length_eq]; exact bound))).map key).Nodup :=
  unique.sublist ((tableMessages_sublist views tables aligned index bound).map key)

end ReceiverView
end Air.Flat
