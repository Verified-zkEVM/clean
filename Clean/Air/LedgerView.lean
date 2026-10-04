module

public import Clean.Air.TransitionView
public import Clean.Air.MessageFilter
public import Clean.Air.Footprint
public import Clean.Utils.ResourceHistory.Ranked

/-! # Exact views of gated physical ledgers

Direction and activity are explicit in the mathematical view. The physical list
still includes disabled slots, so its length remains the capacity charged by Clean.
Views are justified under raw row constraints, allowing Boolean gates to be decoded
without strengthening a channel's semantic guarantees.
-/

@[expose] public section

namespace Air.Flat

private theorem flatMap_zipIdx {A B : Type*} (items : List A) (f : A → List B) :
    items.zipIdx.flatMap (fun item => f item.1) = items.flatMap f := by
  have same := congrArg (List.flatMap f) (List.zipIdx_map_fst 0 items)
  simp only [List.flatMap_map] at same
  exact same

variable {F : Type} [FiniteField F] [DecidableEq F]
variable {Message : TypeMap} [ProvableType Message]

inductive LedgerDirection where
  | produce
  | consume
  deriving DecidableEq

/-- One physical interaction slot, including disabled slots. -/
structure LedgerEntry (Message : Type) where
  direction : LedgerDirection
  active : Bool
  message : Message

namespace LedgerEntry

def interaction (channel : Channel F Message) (entry : LedgerEntry (Message F)) : Interaction F :=
  match entry.direction with
  | .produce => channel.pushedIfValue (if entry.active then 1 else 0) entry.message
  | .consume => channel.pulledIfValue (if entry.active then 1 else 0) entry.message

def produced (entries : List (LedgerEntry (Message F))) : List (Message F) :=
  entries.flatMap fun entry =>
    if entry.active && entry.direction == .produce then [entry.message] else []

def consumed (entries : List (LedgerEntry (Message F))) : List (Message F) :=
  entries.flatMap fun entry =>
    if entry.active && entry.direction == .consume then [entry.message] else []

/-- Removing zero slots and separating directions preserves all active occurrences. -/
theorem active_perm (channel : Channel F Message) (entries : List (LedgerEntry (Message F))) :
    ((entries.map (interaction channel)).filter fun i => decide (i.mult ≠ 0)).Perm
      ((produced entries).map channel.pushedValue ++ (consumed entries).map channel.pulledValue) := by
  induction entries with
  | nil => exact .nil
  | cons entry rest ih =>
    rcases entry with ⟨direction, active, message⟩
    cases direction <;> cases active <;>
      simp only [interaction, produced, consumed, List.map_cons, List.flatMap_cons,
        List.filter_cons, Channel.pushedIfValue, Channel.pulledIfValue, Bool.false_eq_true,
        ↓reduceIte, Bool.false_and, Bool.true_and, beq_self_eq_true, List.map_append,
        List.nil_append, List.singleton_append,
        neg_zero, ne_eq, not_true_eq_false, decide_false, neg_ne_zero,
        one_ne_zero, not_false_eq_true, decide_true] at *
    · exact ih
    · exact ih.cons _
    · exact ih
    · exact (ih.cons _).trans List.perm_middle.symm

/-- Raw balance supplies exact typed conservation, with the original physical bound intact. -/
theorem balanced_perm (channel : Channel F Message) (entries : List (LedgerEntry (Message F)))
    (balanced : BalancedInteractions (entries.map (interaction channel))) :
    (produced entries).Perm (consumed entries) := by
  have active := balanced.filter_nonzero
  have separated := balancedInteractions_of_perm active (active_perm channel entries)
  exact ((channel.balanced_unit_iff _ _).mp separated).2

end LedgerEntry

/-- A component view contains exactly its real interaction slots on the selected channel. -/
structure LedgerView (channel : Channel F Message) where
  component : Component F
  entries : Environment F → List (LedgerEntry (Message F))
  interactions : ∀ env, component.operations.ConstraintsHold env →
    component.operations.interactionValuesWith channel.toRaw env =
      (entries env).map (LedgerEntry.interaction channel)

namespace LedgerView

variable {channel : Channel F Message}

/-- Physical identities survive even when rows and their evaluated messages are equal. -/
structure RowOccurrence (F : Type) [FiniteField F] where
  tableIndex : ℕ
  rowIndex : ℕ
  component : Component F
  environment : Environment F

def readOccurrences (tables : List (Table F)) : List (RowOccurrence F) :=
  tables.zipIdx.flatMap fun (table, tableIndex) =>
    table.table.zipIdx.map fun (row, rowIndex) =>
      ⟨tableIndex, rowIndex, table.component, table.environment row⟩

omit [DecidableEq F] in
/-- Adding physical coordinates preserves the entire evaluated ledger. -/
theorem readOccurrences_interactions (tables : List (Table F)) (channel : RawChannel F) :
    (readOccurrences tables).flatMap (fun occurrence =>
      occurrence.component.operations.interactionValuesWith channel occurrence.environment) =
      tables.flatMap (·.interactionsWith channel) := by
  simp only [readOccurrences, List.flatMap_assoc, List.flatMap_map]
  rw [flatMap_zipIdx tables (fun table => table.table.zipIdx.flatMap (fun row =>
    table.component.operations.interactionValuesWith channel (table.environment row.1)))]
  apply List.flatMap_congr
  intro table _
  exact flatMap_zipIdx table.table (fun row =>
    table.component.operations.interactionValuesWith channel (table.environment row))

omit [DecidableEq F] in
/-- Component alignment is checked before zipping views with physical tables. -/
theorem read_interactions (views : List (LedgerView channel)) (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables)
    (constraints : ∀ table ∈ tables, table.Constraints) :
    tables.flatMap (·.interactionsWith channel.toRaw) =
      ((views.zip tables).flatMap fun (view, table) =>
        table.table.flatMap fun row => view.entries (table.environment row)).map
          (LedgerEntry.interaction channel) := by
  induction aligned with
  | nil => rfl
  | @cons view table views tables same tail ih =>
    simp only [List.flatMap_cons, List.zip_cons_cons, List.map_append]
    rw [ih (fun t ht => constraints t (List.mem_cons_of_mem _ ht))]
    congr 1
    rw [List.map_flatMap]
    unfold Table.interactionsWith
    apply List.flatMap_congr
    intro row member
    rw [← same, view.interactions]
    rw [same]
    exact constraints table (List.mem_cons_self ..) row member

/-- The original one-pair API embeds without changing any interaction. -/
def ofTransition (view : TransitionView channel) : LedgerView channel where
  component := view.component
  entries env := [⟨.consume, true, (view.edge env).1⟩, ⟨.produce, true, (view.edge env).2⟩]
  interactions env _ := by
    rw [view.interactions]
    rfl

/-- Constraints and balance of the actual physical inventory give exact conservation
and charge every decoded slot, including inactive slots, to the characteristic bound. -/
theorem balanced_inventory (views : List (LedgerView channel)) (tables : List (Table F))
    (aligned : List.Forall₂ (fun view table => view.component = table.component) views tables)
    (constraints : ∀ table ∈ tables, table.Constraints)
    (balanced : BalancedInteractions (tables.flatMap (·.interactionsWith channel.toRaw))) :
    let entries := (views.zip tables).flatMap fun (view, table) =>
      table.table.flatMap fun row => view.entries (table.environment row)
    (entries.length < ringChar F ∨ ringChar F = 0) ∧
      (LedgerEntry.produced entries).Perm (LedgerEntry.consumed entries) := by
  rw [read_interactions views tables aligned constraints] at balanced
  have bound := balanced.1
  simp only [List.length_map] at bound
  exact ⟨bound, LedgerEntry.balanced_perm channel _ balanced⟩

end LedgerView

/-- An arbitrary finite list of gated transitions in one physical row. -/
structure GatedTransitionView (channel : Channel F Message) where
  component : Component F
  transitions : Environment F → List (Bool × (Message F × Message F))
  interactions : ∀ env, component.operations.ConstraintsHold env →
    component.operations.interactionValuesWith channel.toRaw env =
      (transitions env).flatMap (fun (active, incoming, outgoing) =>
        [channel.pulledIfValue (if active then 1 else 0) incoming,
         channel.pushedIfValue (if active then 1 else 0) outgoing])

def GatedTransitionView.toLedgerView {channel : Channel F Message}
    (view : GatedTransitionView channel) : LedgerView channel where
  component := view.component
  entries env := (view.transitions env).flatMap fun (active, incoming, outgoing) =>
    [⟨.consume, active, incoming⟩, ⟨.produce, active, outgoing⟩]
  interactions env checked := by
    rw [view.interactions env checked, List.map_flatMap]
    rfl

end Air.Flat
