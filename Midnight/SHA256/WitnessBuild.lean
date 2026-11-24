import Midnight.SHA256.WitnessCircuit
import Clean.Halo2.Lemmas
import Init.Data.Range.Lemmas

/-!
Composition facts for the source's `StateT Cache (Circuit F)` programs. The
cache, returned cells and region index are the actual program outputs. Semantic
table assumptions and cache meanings remain caller-supplied predicates.
-/
namespace Midnight.SHA256.WitnessBuild
open Halo2 WitnessCircuit

/-- A builder advances its region index by exactly its emitted region count. -/
def Lawful {α : Type} (action : Build α) : Prop :=
  ∀ cache self, (action cache).nextRegionIndex self =
    self + ((action cache).operations self).regionCount

theorem pure_bind {α β : Type} (value : α) (next : α → Build β) :
    (pure value >>= next) = next value := rfl

theorem bind_pure {α : Type} (first : Build α) : (first >>= pure) = first := by
  funext cache self
  change ((first cache self).1, (first cache self).2.1 ++ [], (first cache self).2.2) = _
  simp only [List.append_nil]

theorem bind_assoc {α β γ : Type} (first : Build α) (next : α → Build β)
    (last : β → Build γ) :
    ((first >>= next) >>= last) = (first >>= fun value => next value >>= last) := by
  funext cache self
  change (_, (_ ++ _) ++ _, _) = (_, _ ++ (_ ++ _), _)
  simp only [List.append_assoc]

/-- Source loops which always yield are ordinary sequential folds. -/
theorem forIn_yield_cons {α β : Type} (item : α) (items : List α) (initial : β)
    (step : α → β → Build β) :
    forIn (item :: items) initial (fun item state => do return .yield (← step item state)) =
      (do let state ← step item initial
          forIn items state (fun item state => do return .yield (← step item state))) := by
  rw [List.forIn_cons, bind_assoc]
  congr 1

theorem bind_output {α β : Type} (first : Build α) (next : α → Build β)
    (cache : Cache) (self : RegionIndex) :
    ((first >>= next) cache).output self =
      (next ((first cache).output self).1 ((first cache).output self).2).output
        ((first cache).nextRegionIndex self) := rfl

theorem bind_operations {α β : Type} (first : Build α) (next : α → Build β)
    (cache : Cache) (self : RegionIndex) :
    ((first >>= next) cache).operations self =
      (first cache).operations self ++
        (next ((first cache).output self).1 ((first cache).output self).2).operations
          ((first cache).nextRegionIndex self) := rfl

theorem bind_nextRegionIndex {α β : Type} (first : Build α) (next : α → Build β)
    (cache : Cache) (self : RegionIndex) :
    ((first >>= next) cache).nextRegionIndex self =
      (next ((first cache).output self).1 ((first cache).output self).2).nextRegionIndex
        ((first cache).nextRegionIndex self) := rfl

theorem lawful_pure {α : Type} (value : α) : Lawful (pure value) := by
  intro cache self
  rfl

theorem lawful_bind {α β : Type} {first : Build α} {next : α → Build β}
    (hfirst : Lawful first) (hnext : ∀ value, Lawful (next value)) :
    Lawful (first >>= next) := by
  intro cache self
  simp only [bind_nextRegionIndex, bind_operations, Operations.regionCount_append]
  rw [hnext, hfirst]
  exact Nat.add_assoc _ _ _

theorem lawful_region {α : Type} (name : String) (body : Region α) :
    Lawful (WitnessCircuit.region name body) := by
  intro cache self
  rfl

/-- Exact constraint splitting at the index actually returned by `first`. -/
theorem bind_constraints {α β : Type} (first : Build α) (next : α → Build β)
    (hfirst : Lawful first) (place : RegionIndex → Nat) (env : Environment F)
    (cache : Cache) (self : RegionIndex) :
    Constraints place env (((first >>= next) cache).operations self) self ↔
      Constraints place env ((first cache).operations self) self ∧
      Constraints place env
        ((next ((first cache).output self).1 ((first cache).output self).2).operations
          ((first cache).nextRegionIndex self)) ((first cache).nextRegionIndex self) := by
  rw [bind_operations, constraints_append, ← hfirst cache self]

/-- Honest witness splitting uses the same cache and region-index threading. -/
theorem bind_extendsWitnesses {α β : Type} (first : Build α) (next : α → Build β)
    (hfirst : Lawful first) (place : RegionIndex → Nat) (env : ProverEnvironment F)
    (cache : Cache) (self : RegionIndex) :
    ExtendsWitnesses place env (((first >>= next) cache).operations self) self ↔
      ExtendsWitnesses place env ((first cache).operations self) self ∧
      ExtendsWitnesses place env
        ((next ((first cache).output self).1 ((first cache).output self).2).operations
          ((first cache).nextRegionIndex self)) ((first cache).nextRegionIndex self) := by
  rw [bind_operations, extendsWitnesses_append, ← hfirst cache self]

theorem lawful_forIn_list {α β : Type} (items : List α) (initial : β)
    (step : α → β → Build (ForInStep β))
    (step_lawful : ∀ item ∈ items, ∀ state, Lawful (step item state)) :
    Lawful (forIn items initial step) := by
  induction items generalizing initial with
  | nil => simpa only [List.forIn_nil] using lawful_pure initial
  | cons item items ih =>
    rw [List.forIn_cons]
    apply lawful_bind (step_lawful item (List.mem_cons_self) initial)
    intro result
    cases result with
    | done result => exact lawful_pure result
    | yield result =>
      exact ih result (fun next member => step_lawful next (List.mem_cons_of_mem _ member))

/-- Ordered prefix induction for the source's loops without early exit. Each
step knows its exact position through a decomposition of the original list. -/
theorem forIn_list_prefix {α β : Type} (items : List α) (initial : β)
    (step : α → β → Build β) (prior : List α)
    (invariant : List α → β → Cache → RegionIndex → Prop)
    (place : RegionIndex → Nat) (env : Environment F)
    (step_lawful : ∀ item ∈ items, ∀ state, Lawful (step item state))
    (preserves : ∀ processed item remaining, items = processed ++ item :: remaining →
      ∀ state cache self, invariant (prior ++ processed) state cache self →
      Constraints place env ((step item state cache).operations self) self →
      invariant (prior ++ processed ++ [item]) ((step item state cache).output self).1
        ((step item state cache).output self).2
        ((step item state cache).nextRegionIndex self))
    (cache : Cache) (self : RegionIndex) (entry : invariant prior initial cache self)
    (satisfied : Constraints place env
      ((forIn items initial (fun item state => do return .yield (← step item state)) :
        Build β) cache |>.operations self) self) :
    invariant (prior ++ items)
      ((forIn items initial (fun item state => do return .yield (← step item state)) :
        Build β) cache |>.output self).1
      ((forIn items initial (fun item state => do return .yield (← step item state)) :
        Build β) cache |>.output self).2
      ((forIn items initial (fun item state => do return .yield (← step item state)) :
        Build β) cache |>.nextRegionIndex self) := by
  induction items generalizing initial prior cache self with
  | nil =>
    change invariant (prior ++ []) initial cache self
    simpa only [List.append_nil] using entry
  | cons item items ih =>
    rw [forIn_yield_cons] at satisfied
    have parts := (bind_constraints (step item initial) _
      (step_lawful item List.mem_cons_self initial) place env cache self).mp satisfied
    have post := preserves [] item items rfl initial cache self
      (by simpa only [List.append_nil] using entry) parts.1
    simp only [List.append_nil] at post
    rw [forIn_yield_cons]
    simp only [bind_output, bind_nextRegionIndex]
    have result := ih ((step item initial cache).output self).1 (prior ++ [item])
      (fun next member => step_lawful next (List.mem_cons_of_mem _ member))
      (by
        intro processed next remaining split state nextCache nextIndex valid constraints
        have h := preserves (item :: processed) next remaining
          (by simp only [List.cons_append, List.cons.injEq, true_and]; exact split)
          state nextCache nextIndex
        simp only [List.append_assoc, List.cons_append, List.nil_append] at valid ⊢
        simpa only [List.append_assoc, List.cons_append] using h valid constraints)
      ((step item initial cache).output self).2
      ((step item initial cache).nextRegionIndex self) post parts.2
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using result

/-- Honest completeness composes over the same source fold. Each step must
derive its constraints and the next invariant from its real witness programs. -/
theorem forIn_list_prefix_complete {α β : Type} (items : List α) (initial : β)
    (step : α → β → Build β) (prior : List α)
    (invariant : List α → β → Cache → RegionIndex → Prop)
    (place : RegionIndex → Nat) (env : ProverEnvironment F)
    (step_lawful : ∀ item ∈ items, ∀ state, Lawful (step item state))
    (completes : ∀ processed item remaining, items = processed ++ item :: remaining →
      ∀ state cache self, invariant (prior ++ processed) state cache self →
      ExtendsWitnesses place env ((step item state cache).operations self) self →
      Constraints place env.toEnvironment ((step item state cache).operations self) self ∧
      invariant (prior ++ processed ++ [item]) ((step item state cache).output self).1
        ((step item state cache).output self).2
        ((step item state cache).nextRegionIndex self))
    (cache : Cache) (self : RegionIndex) (entry : invariant prior initial cache self)
    (witnesses : ExtendsWitnesses place env
      ((forIn items initial (fun item state => do return .yield (← step item state)) :
        Build β) cache |>.operations self) self) :
    Constraints place env.toEnvironment
      ((forIn items initial (fun item state => do return .yield (← step item state)) :
        Build β) cache |>.operations self) self ∧
    invariant (prior ++ items)
      ((forIn items initial (fun item state => do return .yield (← step item state)) :
        Build β) cache |>.output self).1
      ((forIn items initial (fun item state => do return .yield (← step item state)) :
        Build β) cache |>.output self).2
      ((forIn items initial (fun item state => do return .yield (← step item state)) :
        Build β) cache |>.nextRegionIndex self) := by
  induction items generalizing initial prior cache self with
  | nil =>
    constructor
    · trivial
    · change invariant (prior ++ []) initial cache self
      simpa only [List.append_nil] using entry
  | cons item items ih =>
    rw [forIn_yield_cons] at witnesses
    have parts := (bind_extendsWitnesses (step item initial) _
      (step_lawful item List.mem_cons_self initial) place env cache self).mp witnesses
    have first := completes [] item items rfl initial cache self
      (by simpa only [List.append_nil] using entry) parts.1
    simp only [List.append_nil] at first
    rw [forIn_yield_cons]
    simp only [bind_output, bind_nextRegionIndex]
    have result := ih ((step item initial cache).output self).1 (prior ++ [item])
      (fun next member => step_lawful next (List.mem_cons_of_mem _ member))
      (by
        intro processed next remaining split state nextCache nextIndex valid witnesses
        have h := completes (item :: processed) next remaining
          (by simp only [List.cons_append, List.cons.injEq, true_and]; exact split)
          state nextCache nextIndex
        simp only [List.append_assoc, List.cons_append, List.nil_append] at valid ⊢
        simpa only [List.append_assoc, List.cons_append] using h valid witnesses)
      ((step item initial cache).output self).2
      ((step item initial cache).nextRegionIndex self) first.2 parts.2
    constructor
    · apply (bind_constraints _ _ (step_lawful item List.mem_cons_self initial)
        place env.toEnvironment cache self).mpr
      exact ⟨first.1, result.1⟩
    · simpa only [List.append_assoc, List.cons_append, List.nil_append] using result.2

end Midnight.SHA256.WitnessBuild
