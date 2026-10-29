module

public import CompStark.Lookup.Lookup

/-!
# Buses of a batch's lookups

Two facts about how CompStark lays out the global lookups of a batch (`CompStark/Lookup/`), which
reduce a bus's balance to the tuples of the lookups on it:

* Packing keeps every bus's tuples (`flatMap_filter_packSameBus`): the packed lookups on a bus
  hold the tuples of the lookups on that bus.
* The bus numbers name the buses (`busIds_eq_busNumber`): a global lookup's bus number is a
  function of its bus's name, and different names have different numbers (`busNumber_inj`).
-/

@[expose] public section

namespace CleanCompStark
open CompStark.Lookup CompStark.Stark

variable {K : Type}

/-! ### Packing -/

theorem foldl_packStep_bus (budget : ℕ) (bus : Option String) :
    ∀ (ms : List (Lookup K)) (s : List (Lookup K) × Lookup K), (∀ m ∈ ms, m.bus = bus) →
      (∀ x ∈ s.1, x.bus = bus) → s.2.bus = bus →
      (∀ x ∈ (ms.foldl (packStep budget) s).1, x.bus = bus) ∧
        (ms.foldl (packStep budget) s).2.bus = bus
  | [], _, _, h1, h2 => ⟨h1, h2⟩
  | m :: ms, s, hms, h1, h2 => by
    rw [List.foldl_cons]
    apply foldl_packStep_bus budget bus ms _ (fun x hx => hms x (List.mem_cons_of_mem _ hx))
    · unfold packStep
      dsimp only
      split
      · exact h1
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact h1 x hx
        · rw [List.mem_singleton.mp hx]
          exact h2
    · unfold packStep
      dsimp only
      split
      · exact h2
      · exact hms m List.mem_cons_self

/-- Packing the lookups of one bus gives lookups on that bus. -/
theorem bus_packBus (budget : ℕ) (bus : Option String) (ms : List (Lookup K))
    (hms : ∀ m ∈ ms, m.bus = bus) : ∀ l ∈ packBus budget ms, l.bus = bus := by
  cases ms with
  | nil => intro l hl; simp [packBus] at hl
  | cons m ms =>
    intro l hl
    simp only [packBus] at hl
    have h := foldl_packStep_bus budget bus ms ([], m)
      (fun x hx => hms x (List.mem_cons_of_mem _ hx)) (by simp) (hms m List.mem_cons_self)
    rcases List.mem_append.mp hl with hl | hl
    · exact h.1 l hl
    · rw [List.mem_singleton.mp hl]
      exact h.2

theorem flatMap_ite_eq {α β : Type*} [DecidableEq α] (a : α) (xs : List β) :
    ∀ l : List α, l.Nodup → (l.flatMap fun b => if b = a then xs else []) = if a ∈ l then xs else []
  | [], _ => by simp
  | b :: l, hnd => by
    rw [List.nodup_cons] at hnd
    rw [List.flatMap_cons, flatMap_ite_eq a xs l hnd.2]
    by_cases hb : b = a
    · subst hb
      simp [hnd.1]
    · simp [hb, Ne.symm hb]

/-- **Packing keeps every bus's tuples.** -/
theorem flatMap_filter_packSameBus (budget : ℕ) (ls : List (Lookup K)) (name : String) :
    ((packSameBus budget ls).filter (·.bus == some name)).flatMap (·.entries) =
      (ls.filter (·.bus == some name)).flatMap (·.entries) := by
  unfold packSameBus
  rw [List.filter_append, List.flatMap_append, List.filter_flatMap, List.flatMap_assoc]
  have hnone : ((ls.filter (·.bus.isNone)).filter (·.bus == some name)) = [] := by
    rw [List.filter_filter, List.filter_eq_nil_iff]
    intro l _
    cases l.bus <;> simp
  rw [hnone, List.flatMap_nil, List.nil_append]
  have hbus : ∀ b ∈ buses ls,
      ((packBus budget (ls.filter (·.bus == some b))).filter (·.bus == some name)).flatMap
        (·.entries) = if b = name then (ls.filter (·.bus == some name)).flatMap (·.entries)
          else [] := by
    intro b _
    have hall := bus_packBus budget (some b) (ls.filter (·.bus == some b)) (by
      intro m hm
      simpa using (List.mem_filter.mp hm).2)
    split
    · subst b
      rw [List.filter_eq_self.mpr (fun l hl => by simp [hall l hl]), flatMap_packBus]
    · rename_i hb
      refine (congrArg _ (List.filter_eq_nil_iff.mpr fun l hl => ?_)).trans List.flatMap_nil
      simp only [hall l hl, beq_iff_eq, Option.some.injEq]
      exact hb
  rw [List.flatMap_congr hbus,
    flatMap_ite_eq _ _ _ (show (buses ls).Nodup from (foldl_busesStep ls [] List.nodup_nil).1)]
  split
  · rfl
  · rename_i hname
    rw [List.filter_eq_nil_iff.mpr, List.flatMap_nil]
    intro l hl hbusl
    simp only [beq_iff_eq] at hbusl
    exact hname (show name ∈ buses ls from
      (foldl_busesStep ls [] List.nodup_nil).2.2 l hl name hbusl)

/-- Packing global lookups gives global lookups. -/
theorem bus_isSome_packSameBus (budget : ℕ) (ls : List (Lookup K))
    (hls : ∀ m ∈ ls, m.bus.isSome) : ∀ l ∈ packSameBus budget ls, l.bus.isSome := by
  intro l hl
  unfold packSameBus at hl
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨hl, hnone⟩ := List.mem_filter.mp hl
    have := hls l hl
    simp_all
  · obtain ⟨b, -, hl⟩ := List.mem_flatMap.mp hl
    rw [bus_packBus budget (some b) _ (fun m hm => by simpa using (List.mem_filter.mp hm).2) l hl]
    rfl

/-! ### Bus numbers -/

/-- The names and the next free number after numbering the buses of the instances `ls`, the global
buses already numbered as `names` and `next` the next free number (`busIdsFrom`). -/
def busNames (names : List (String × ℕ)) (next : ℕ) :
    List (List (Lookup K)) → List (String × ℕ) × ℕ
  | [] => (names, next)
  | inst :: rest =>
    let s := inst.foldl busStep ([], names, next)
    busNames s.2.1 s.2.2 rest

/-- A numbering state: the numbers are distinct and below the next free number. -/
def NumberingValid (names : List (String × ℕ)) (next : ℕ) : Prop :=
  (names.map (·.2)).Nodup ∧ ∀ x ∈ names, x.2 < next

theorem foldl_busStep (ls : List (Lookup K)) :
    ∀ (s : List ℕ × List (String × ℕ) × ℕ), NumberingValid s.2.1 s.2.2 →
      ∃ T : List ℕ, (ls.foldl busStep s).1 = s.1 ++ T ∧ T.length = ls.length ∧
        (∀ x ∈ ls.zip T, ∀ name, x.1.bus = some name →
          (ls.foldl busStep s).2.1.lookup name = some x.2) ∧
        NumberingValid (ls.foldl busStep s).2.1 (ls.foldl busStep s).2.2 ∧
        ∀ name v, s.2.1.lookup name = some v → (ls.foldl busStep s).2.1.lookup name = some v := by
  induction ls with
  | nil => intro s hs; exact ⟨[], by simp, rfl, by simp, hs, fun _ _ h => h⟩
  | cons l ls ih =>
    intro s hs
    obtain ⟨ids, names, next⟩ := s
    -- one step
    obtain ⟨b, hstep, hb, hvalid, hmono⟩ : ∃ b, (busStep (ids, names, next) l).1 = ids ++ [b] ∧
        (∀ name, l.bus = some name → (busStep (ids, names, next) l).2.1.lookup name = some b) ∧
        NumberingValid (busStep (ids, names, next) l).2.1 (busStep (ids, names, next) l).2.2 ∧
        ∀ name v, names.lookup name = some v →
          (busStep (ids, names, next) l).2.1.lookup name = some v := by
      unfold busStep
      cases hl : l.bus with
      | none => exact ⟨next, rfl, by simp, ⟨hs.1, fun x hx => Nat.lt_succ_of_lt (hs.2 x hx)⟩,
          fun _ _ h => h⟩
      | some c =>
        dsimp only
        cases hc : names.lookup c with
        | some k => exact ⟨k, rfl, by simp [hc], hs, fun _ _ h => h⟩
        | none =>
          refine ⟨next, rfl, ?_, ⟨?_, ?_⟩, ?_⟩
          · intro name hname
            simp only [Option.some.injEq] at hname
            subst hname
            simp [List.lookup_append, hc]
          · rw [List.map_append, List.nodup_append]
            refine ⟨hs.1, List.nodup_singleton _, ?_⟩
            intro a ha b hb
            simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
            subst hb
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
            exact Nat.ne_of_lt (hs.2 x hx)
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact Nat.lt_succ_of_lt (hs.2 x hx)
            · rw [List.mem_singleton.mp hx]
              exact Nat.lt_succ_self _
          · intro name v h
            simp [List.lookup_append, h]
    obtain ⟨T, hT, hlen, hzip, hvalid', hmono'⟩ := ih _ hvalid
    refine ⟨b :: T, ?_, by simp [hlen], ?_, hvalid', fun name v h => hmono' name v (hmono name v h)⟩
    · rw [List.foldl_cons, hT, hstep, List.append_assoc, List.singleton_append]
    · intro x hx name hname
      rw [List.zip_cons_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rw [List.foldl_cons]
        exact hmono' name b (hb name hname)
      · rw [List.foldl_cons]
        exact hzip x hx name hname

theorem busIdsFrom_lookup :
    ∀ (ls : List (List (Lookup K))) (names : List (String × ℕ)) (next : ℕ),
      NumberingValid names next →
      NumberingValid (busNames names next ls).1 (busNames names next ls).2 ∧
        (∀ name v, names.lookup name = some v → (busNames names next ls).1.lookup name = some v) ∧
        ∀ j (hj : j < ls.length), ∀ x ∈ ls[j].zip ((busIdsFrom names next ls).getD j []),
          ∀ name, x.1.bus = some name → (busNames names next ls).1.lookup name = some x.2
  | [], names, next, h => ⟨h, fun _ _ h => h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | inst :: rest, names, next, h => by
    obtain ⟨T, hT, -, hzip, hvalid, hmono⟩ := foldl_busStep inst ([], names, next) h
    obtain ⟨hvalid', hmono', hrest⟩ := busIdsFrom_lookup rest _ _ hvalid
    refine ⟨hvalid', fun name v hv => hmono' name v (hmono name v hv), ?_⟩
    intro j hj x hx name hname
    cases j with
    | zero =>
      simp only [busIdsFrom, List.getD_cons_zero, List.getElem_cons_zero, hT,
        List.nil_append] at hx
      exact hmono' name x.2 (hzip x hx name hname)
    | succ j =>
      simp only [busIdsFrom, List.getD_cons_succ, List.getElem_cons_succ] at hx
      exact hrest j (by simpa using hj) x hx name hname

/-- The number of the bus `name` in the numbering of the instances' lookups `ls`: its number if
some lookup is on it, else a number no bus has. -/
def busNumber (ls : List (List (Lookup K))) (name : String) : ℕ :=
  ((busNames [] 0 ls).1.lookup name).getD (busNames [] 0 ls).2

/-- **The bus numbers name the buses.** The bus number of a global lookup is its bus's
`busNumber`. -/
theorem busIds_eq_busNumber (ls : List (List (Lookup K))) (j : ℕ) (hj : j < ls.length)
    (x : Lookup K × ℕ) (hx : x ∈ ls[j].zip ((busIds ls).getD j [])) (name : String)
    (hname : x.1.bus = some name) : x.2 = busNumber ls name := by
  have h := (busIdsFrom_lookup ls [] 0 ⟨List.nodup_nil, by simp⟩).2.2 j hj x hx name hname
  simp [busNumber, h]

/-- A global lookup's bus number is the `busNumber` of a name only if that is its bus. -/
theorem busNumber_inj (ls : List (List (Lookup K))) (j : ℕ) (hj : j < ls.length)
    (x : Lookup K × ℕ) (hx : x ∈ ls[j].zip ((busIds ls).getD j [])) (name name' : String)
    (hname : x.1.bus = some name) (h : x.2 = busNumber ls name') : name' = name := by
  obtain ⟨hvalid, -, hlookup⟩ := busIdsFrom_lookup ls [] 0 ⟨List.nodup_nil, by simp⟩
  have hv := hlookup j hj x hx name hname
  obtain ⟨l₁, l₂, heq, -⟩ := List.lookup_eq_some_iff.mp hv
  have hmem : (name, x.2) ∈ (busNames [] 0 ls).1 := by rw [heq]; simp
  unfold busNumber at h
  cases hl : (busNames [] 0 ls).1.lookup name' with
  | none =>
    rw [hl, Option.getD_none] at h
    exact absurd (hvalid.2 _ hmem) (by rw [h]; exact Nat.lt_irrefl _)
  | some w =>
    rw [hl, Option.getD_some] at h
    obtain ⟨l₁', l₂', heq', -⟩ := List.lookup_eq_some_iff.mp hl
    have hmem' : (name', w) ∈ (busNames [] 0 ls).1 := by rw [heq']; simp
    have := List.inj_on_of_nodup_map hvalid.1 hmem hmem' (by simp [h])
    simp only [Prod.mk.injEq] at this
    exact this.1.symm

end CleanCompStark
