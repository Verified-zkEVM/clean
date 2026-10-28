module

public import Clean.Air.WitnessGeneration.Generation
public import Std.Data.HashMap
public import Std.Data.TreeMap

@[expose] public section

/-!
# The demand tally

The generator's record of the channel messages whose pushes and pulls don't cancel yet. A `Tally`
holds the nonzero net multiplicities as demands, in the order they became nonzero, stored so that
both updating a message and iterating in order are fast. Net multiplicities are integers, pushes
minus pulls, so that they count the same in every field, including binary ones.

Reasoning about a tally only needs its net multiplicities `Tally.net`, its demands `Tally.demands`,
and their lemmas: `net_add`, `mem_demands` and `isEmpty_iff`.
-/

namespace Air.Flat.WitnessGeneration

variable {F : Type} [FiniteField F]

/-- Field elements hash by their value. -/
instance : Hashable F := ⟨fun x => hash (FiniteField.val x)⟩

/-! ### Demand -/

/-- An unanswered channel message: its net multiplicity, pushes minus pulls, is nonzero. -/
structure Demand (F : Type) where
  channel : String
  message : Array F
  /-- The net multiplicity of the message, pushes minus pulls. -/
  multiplicity : ℤ

namespace Demand

/-- The channel and the message: what the tally records a net multiplicity for. -/
def key (demand : Demand F) : String × Array F := (demand.channel, demand.message)

/-- Whether the message was pushed or pulled more often. -/
def direction (demand : Demand F) : Interaction.Direction :=
  if 0 < demand.multiplicity then .push else .pull

end Demand

/-! ### Tally -/

/-- The nonzero net multiplicities of channel messages, as demands by position, in the order they
became nonzero, with the position of each message. -/
structure Tally (F : Type) [FiniteField F] where
  byPosition : Std.TreeMap ℕ (Demand F)
  positions : Std.HashMap (String × Array F) ℕ
  /-- The position of the next new demand. -/
  next : ℕ
  /-- The positions are those of the demands, which have distinct keys. -/
  positions_spec : ∀ (key : String × Array F) (position : ℕ), positions[key]? = some position ↔
    ∃ demand : Demand F, byPosition[position]? = some demand ∧ demand.key = key
  nonzero : ∀ (position : ℕ) (demand : Demand F), byPosition[position]? = some demand →
    demand.multiplicity ≠ 0
  lt_next : ∀ position : ℕ, position ∈ byPosition → position < next

namespace Tally

def empty : Tally F where
  byPosition := ∅
  positions := ∅
  next := 0
  positions_spec := by simp
  nonzero := by simp
  lt_next := by simp

/-- The net multiplicity of a channel message. -/
def net (tally : Tally F) (key : String × Array F) : ℤ :=
  ((tally.positions[key]?.bind fun position => tally.byPosition[position]?).map
    (·.multiplicity)).getD 0

/-- The demands, in the order their messages became unbalanced. -/
def demands (tally : Tally F) : List (Demand F) := tally.byPosition.toList.map (·.2)

def isEmpty (tally : Tally F) : Bool := tally.byPosition.isEmpty

lemma getElem?_byPosition_of_positions {tally : Tally F} {key : String × Array F} {position : ℕ}
    (h : tally.positions[key]? = some position) :
    ∃ demand, tally.byPosition[position]? = some demand ∧ demand.key = key :=
  (tally.positions_spec key position).mp h

/-- Set the demand at `position` to a new nonzero multiplicity, keeping its message. -/
def update (tally : Tally F) (position : ℕ) (demand : Demand F)
    (hdemand : tally.byPosition[position]? = some demand) (multiplicity : ℤ)
    (hmultiplicity : multiplicity ≠ 0) : Tally F where
  byPosition := tally.byPosition.insert position { demand with multiplicity }
  positions := tally.positions
  next := tally.next
  positions_spec key position' := by
    rw [tally.positions_spec, Std.TreeMap.getElem?_insert]
    by_cases h : position = position'
    · subst h
      simp [hdemand, Demand.key]
    · simp [h]
  nonzero position' demand' := by
    rw [Std.TreeMap.getElem?_insert]
    split
    · rintro ⟨⟩
      exact hmultiplicity
    · exact tally.nonzero position' demand'
  lt_next position' hmem := by
    rw [Std.TreeMap.mem_insert] at hmem
    rcases hmem with h | h
    · rw [Nat.compare_eq_eq] at h
      subst h
      exact tally.lt_next _ (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by simp [hdemand]))
    · exact tally.lt_next _ h

/-- Remove the demand at `position`. -/
def remove (tally : Tally F) (position : ℕ) (demand : Demand F)
    (hdemand : tally.byPosition[position]? = some demand) : Tally F where
  byPosition := tally.byPosition.erase position
  positions := tally.positions.erase demand.key
  next := tally.next
  positions_spec key position' := by
    rw [Std.HashMap.getElem?_erase, Std.TreeMap.getElem?_erase]
    by_cases hkey : demand.key = key
    · subst hkey
      simp only [beq_self_eq_true, ite_true, reduceCtorEq, false_iff, not_exists, not_and]
      intro demand' hdemand' hkey'
      split at hdemand'
      · contradiction
      · rename_i hposition
        have := (tally.positions_spec demand.key position').mpr ⟨demand', hdemand', hkey'⟩
        have := (tally.positions_spec demand.key position).mpr ⟨demand, hdemand, rfl⟩
        simp_all
    · simp only [beq_iff_eq, hkey, ite_false, tally.positions_spec]
      by_cases hposition : position = position'
      · subst hposition
        simp only [Nat.compare_eq_eq, ite_true, reduceCtorEq, false_and, exists_false,
          iff_false, not_exists, not_and]
        intro demand' hdemand' hkey'
        simp_all
      · simp [hposition]
  nonzero position' demand' := by
    rw [Std.TreeMap.getElem?_erase]
    split
    · simp
    · exact tally.nonzero position' demand'
  lt_next position' hmem := tally.lt_next _ (Std.TreeMap.mem_of_mem_erase hmem)

/-- Append a demand with a nonzero multiplicity for a message without one. -/
def append (tally : Tally F) (demand : Demand F) (hkey : tally.positions[demand.key]? = none)
    (hmultiplicity : demand.multiplicity ≠ 0) : Tally F where
  byPosition := tally.byPosition.insert tally.next demand
  positions := tally.positions.insert demand.key tally.next
  next := tally.next + 1
  positions_spec key position := by
    rw [Std.HashMap.getElem?_insert, Std.TreeMap.getElem?_insert]
    by_cases hdemand : demand.key = key
    · subst hdemand
      simp only [beq_self_eq_true, ite_true, Option.some.injEq]
      constructor
      · rintro rfl
        simp
      · rintro ⟨demand', hdemand', hkey'⟩
        split at hdemand'
        · simp_all
        · have := (tally.positions_spec demand.key position).mpr ⟨demand', hdemand', hkey'⟩
          simp_all
    · simp only [beq_iff_eq, hdemand, ite_false, tally.positions_spec]
      by_cases hposition : tally.next = position
      · subst hposition
        have hnone : tally.byPosition[tally.next]? = none :=
          Std.TreeMap.getElem?_eq_none fun hmem => Nat.lt_irrefl _ (tally.lt_next _ hmem)
        simp [hnone, hdemand]
      · simp [hposition]
  nonzero position demand' := by
    rw [Std.TreeMap.getElem?_insert]
    split
    · rintro ⟨⟩
      exact hmultiplicity
    · exact tally.nonzero position demand'
  lt_next position hmem := by
    rw [Std.TreeMap.mem_insert, Nat.compare_eq_eq] at hmem
    rcases hmem with rfl | h
    · omega
    · exact Nat.lt_succ_of_lt (tally.lt_next _ h)

/-- Add a multiplicity for a channel message, dropping its demand when it cancels to zero. -/
def add (tally : Tally F) (channel : String) (message : Array F) (multiplicity : ℤ) : Tally F :=
  match hposition : tally.positions[(channel, message)]? with
  | some position =>
      match hdemand : tally.byPosition[position]? with
      | some demand =>
          let total := demand.multiplicity + multiplicity
          if htotal : total = 0 then tally.remove position demand hdemand
          else tally.update position demand hdemand total htotal
      | none => absurd (getElem?_byPosition_of_positions hposition) (by simp [hdemand])
  | none =>
      if hmultiplicity : multiplicity = 0 then tally
      else tally.append { channel, message, multiplicity } hposition hmultiplicity

/-- What an interaction adds to the net multiplicity of its message: its multiplicity read as a
natural number, positive for a push and negative for a pull. -/
def signedCount (interaction : Interaction F) : ℤ :=
  match interaction.direction with
  | .push => FiniteField.val interaction.mult
  | .pull => -FiniteField.val interaction.mult

def addInteractions (tally : Tally F) (interactions : List (Interaction F)) : Tally F :=
  interactions.foldl (fun tally interaction =>
    tally.add interaction.channel.name interaction.msg (signedCount interaction)) tally

def removeInteractions (tally : Tally F) (interactions : List (Interaction F)) : Tally F :=
  interactions.foldl (fun tally interaction =>
    tally.add interaction.channel.name interaction.msg (-signedCount interaction)) tally

/-! ### Net multiplicities and demands -/

lemma net_eq_of_getElem? {tally : Tally F} {position : ℕ} {demand : Demand F}
    (h : tally.byPosition[position]? = some demand) :
    tally.net demand.key = demand.multiplicity := by
  have hposition := (tally.positions_spec demand.key position).mpr ⟨demand, h, rfl⟩
  simp [net, hposition, h]

lemma net_eq_zero {tally : Tally F} {key : String × Array F} (h : tally.positions[key]? = none) :
    tally.net key = 0 := by
  simp [net, h]

@[simp] lemma net_empty (key : String × Array F) : (empty : Tally F).net key = 0 :=
  net_eq_zero Std.HashMap.getElem?_empty

lemma net_update {tally : Tally F} {position : ℕ} {demand : Demand F}
    (hdemand : tally.byPosition[position]? = some demand) {multiplicity : ℤ}
    (hmultiplicity : multiplicity ≠ 0) (key : String × Array F) :
    (tally.update position demand hdemand multiplicity hmultiplicity).net key =
      if key = demand.key then multiplicity else tally.net key := by
  have hposition := (tally.positions_spec demand.key position).mpr ⟨demand, hdemand, rfl⟩
  split
  · subst key
    simp [net, update, hposition, Std.TreeMap.getElem?_insert]
  · cases hkey : tally.positions[key]? with
    | none => simp [net, update, hkey]
    | some position' =>
        obtain ⟨demand', hdemand', rfl⟩ := getElem?_byPosition_of_positions hkey
        have hne : position ≠ position' := by
          rintro rfl
          simp_all
        simp [net, update, hkey, Std.TreeMap.getElem?_insert, hne]

lemma net_remove {tally : Tally F} {position : ℕ} {demand : Demand F}
    (hdemand : tally.byPosition[position]? = some demand) (key : String × Array F) :
    (tally.remove position demand hdemand).net key =
      if key = demand.key then 0 else tally.net key := by
  split
  · subst key
    simp [net, remove]
  · cases hkey : tally.positions[key]? with
    | none => simp [net, remove, Std.HashMap.getElem?_erase, hkey]
    | some position' =>
        obtain ⟨demand', hdemand', rfl⟩ := getElem?_byPosition_of_positions hkey
        have hne : position ≠ position' := by
          rintro rfl
          simp_all
        have hkey' : (demand.key == demand'.key) = false := beq_false_of_ne (Ne.symm ‹_›)
        simp [net, remove, Std.HashMap.getElem?_erase, hkey', hkey, Std.TreeMap.getElem?_erase, hne]

lemma net_append {tally : Tally F} {demand : Demand F}
    (hkey : tally.positions[demand.key]? = none) (hmultiplicity : demand.multiplicity ≠ 0)
    (key : String × Array F) :
    (tally.append demand hkey hmultiplicity).net key =
      if key = demand.key then demand.multiplicity else tally.net key := by
  split
  · subst key
    simp [net, append, Std.TreeMap.getElem?_insert]
  · rename_i hne
    cases hkey' : tally.positions[key]? with
    | none => simp [net, append, Std.HashMap.getElem?_insert, Ne.symm hne, hkey']
    | some position =>
        have hlt : position < tally.next := by
          obtain ⟨demand', hdemand', -⟩ := getElem?_byPosition_of_positions hkey'
          exact tally.lt_next _ (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by simp [hdemand']))
        simp [net, append, Std.HashMap.getElem?_insert, Ne.symm hne, hkey',
          Std.TreeMap.getElem?_insert, Nat.ne_of_gt hlt]

/-- Adding a multiplicity adds it to the net multiplicity of its message. -/
theorem net_add (tally : Tally F) (channel : String) (message : Array F) (multiplicity : ℤ)
    (key : String × Array F) :
    (tally.add channel message multiplicity).net key =
      tally.net key + if key = (channel, message) then multiplicity else 0 := by
  unfold add
  split
  · rename_i position hposition
    split
    · rename_i demand hdemand
      obtain ⟨demand', hdemand', hkey⟩ := getElem?_byPosition_of_positions hposition
      obtain rfl : demand = demand' := by simp_all
      have hnet := net_eq_of_getElem? hdemand
      dsimp only
      by_cases htotal : demand.multiplicity + multiplicity = 0
      · rw [dite_eq_left htotal, net_remove]
        split <;> simp_all [eq_comm]
      · rw [dite_eq_right htotal, net_update]
        split <;> simp_all
    · rename_i hdemand
      exact absurd (getElem?_byPosition_of_positions hposition) (by simp [hdemand])
  · rename_i hposition
    split
    · simp_all
    · rw [net_append (demand := { channel, message, multiplicity }) hposition]
      have hnet := net_eq_zero hposition
      split <;> simp_all [Demand.key]

/-- The demands are the nonzero net multiplicities. -/
theorem mem_demands (tally : Tally F) (demand : Demand F) :
    demand ∈ tally.demands ↔
      tally.net demand.key = demand.multiplicity ∧ demand.multiplicity ≠ 0 := by
  simp only [demands, List.mem_map, Prod.exists, exists_eq_right,
    Std.TreeMap.mem_toList_iff_getElem?_eq_some]
  constructor
  · rintro ⟨position, hdemand⟩
    exact ⟨net_eq_of_getElem? hdemand, tally.nonzero _ _ hdemand⟩
  · rintro ⟨hnet, hnonzero⟩
    simp only [net] at hnet
    cases hposition : tally.positions[demand.key]? with
    | none => simp_all
    | some position =>
        obtain ⟨demand', hdemand', hkey⟩ := getElem?_byPosition_of_positions hposition
        refine ⟨position, ?_⟩
        rw [hdemand']
        cases demand
        cases demand'
        simp_all [Demand.key]

theorem isEmpty_iff (tally : Tally F) : tally.isEmpty ↔ ∀ key, tally.net key = 0 := by
  simp only [isEmpty, Std.TreeMap.isEmpty_iff_forall_not_mem]
  constructor
  · intro hempty key
    cases hposition : tally.positions[key]? with
    | none => exact net_eq_zero hposition
    | some position =>
        obtain ⟨demand, hdemand, -⟩ := getElem?_byPosition_of_positions hposition
        exact absurd (Std.TreeMap.mem_iff_isSome_getElem?.mpr (by simp [hdemand])) (hempty position)
  · intro hzero position hmem
    obtain ⟨demand, hdemand⟩ := Option.isSome_iff_exists.mp
      (Std.TreeMap.mem_iff_isSome_getElem?.mp hmem)
    exact tally.nonzero _ _ hdemand ((net_eq_of_getElem? hdemand).symm.trans (hzero _))

end Tally

end Air.Flat.WitnessGeneration
