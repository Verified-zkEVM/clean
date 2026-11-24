import Midnight.SHA256.Configure
import Midnight.SHA256.Semantics.Tables
import Clean.Halo2.Lemmas

/-! The two actual selected SHA lookup tuples, with a shared-row table contract
proved from the native table load operations. -/
namespace Midnight.SHA256.Semantics.Gates
open Halo2

/-- First active tuple in the native batched plain/spread lookup. -/
def spreadLookup0 : LookupArgument F where
  masterSelector := ⟨4⟩
  inputs := [queryFixed ⟨0⟩, queryAdvice ⟨6⟩ 0, queryAdvice ⟨0⟩ 0]
  tables := [queryFixed ⟨13⟩, queryFixed ⟨14⟩, queryFixed ⟨15⟩]
  inputsNoSimpleSelectors := by selector_free
  tablesFree := by selector_free
  arity := rfl

/-- Second active tuple, sharing the same source table columns. -/
def spreadLookup1 : LookupArgument F where
  masterSelector := ⟨4⟩
  inputs := [queryFixed ⟨1⟩, queryAdvice ⟨7⟩ 0, queryAdvice ⟨1⟩ 0]
  tables := [queryFixed ⟨13⟩, queryFixed ⟨14⟩, queryFixed ⟨15⟩]
  inputsNoSimpleSelectors := by selector_free
  tablesFree := by selector_free
  arity := rfl

theorem spreadLookups_source :
    cleanLookups.filter (fun l => l.masterSelector.index == 4) = [spreadLookup0, spreadLookup1] := by
  decide +kernel

theorem activation_spread (row : Nat) : activation 4 row =
    [.enableLookup spreadLookup0 [⟨4, false⟩] row,
     .enableLookup spreadLookup1 [⟨4, false⟩] row] := by
  have hg : cleanGates.filter (fun g => g.selector.index == 4) = [] := by decide +kernel
  simp [activation, hg, spreadLookups_source]

/-- Ambient table facts in both directions; no advice or gate meaning is assumed. -/
structure SpreadTable (env : Environment F) : Prop where
  sound : ∀ row : Nat, row < env.usableRows →
    SpreadLookup (env.fixed ⟨13⟩ row) (env.fixed ⟨14⟩ row) (env.fixed ⟨15⟩ row)
  complete : ∀ tag plain expanded : F, SpreadLookup tag plain expanded →
    ∃ row : Nat, row < env.usableRows ∧ env.fixed ⟨13⟩ row = tag ∧
      env.fixed ⟨14⟩ row = plain ∧ env.fixed ⟨15⟩ row = expanded

theorem spreadTable_of_load {place : RegionIndex → Nat} {env : Environment F}
    (i : RegionIndex)
    (loaded : Constraints place env ((loadSpread ⟨⟨13⟩⟩ ⟨⟨14⟩⟩ ⟨⟨15⟩⟩).operations i) i)
    (capacity : spreadRows.length ≤ env.usableRows) : SpreadTable env := by
  constructor
  · exact loadSpread_sound _ _ _ i loaded
  · intro tag plain expanded member
    exact loadSpread_complete _ _ _ i loaded capacity member

set_option linter.constructorNameAsVariable false in
/-- A source selector activation proves both complete triples are in the loaded
table. Each triple uses one common table row, including its width tag. -/
theorem activation_spread_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat} (table : SpreadTable env)
    (satisfied : RegionOperations.Constraints place self env (activation 4 row)) :
    SpreadLookup (env.fixed ⟨0⟩ (place self + row : Nat))
      (env.advice ⟨6⟩ (place self + row : Nat)) (env.advice ⟨0⟩ (place self + row : Nat)) ∧
    SpreadLookup (env.fixed ⟨1⟩ (place self + row : Nat))
      (env.advice ⟨7⟩ (place self + row : Nat)) (env.advice ⟨1⟩ (place self + row : Nat)) := by
  rw [activation_spread] at satisfied
  simp only [RegionOperations.Constraints, RegionOperation.Constraints,
    spreadLookup0, spreadLookup1, circuit_norm] at satisfied
  obtain ⟨⟨r₀, hr₀, e₀⟩, ⟨r₁, hr₁, e₁⟩, _⟩ := satisfied
  simp only [List.map_cons, List.map_nil, Expression.eval, Query.eval, Int.add_zero,
    List.cons.injEq, and_true] at e₀ e₁
  have t₀ := table.sound r₀ hr₀
  have t₁ := table.sound r₁ hr₁
  rw [← e₀.1, ← e₀.2.1, ← e₀.2.2] at t₀
  rw [← e₁.1, ← e₁.2.1, ← e₁.2.2] at t₁
  exact ⟨t₀, t₁⟩

end Midnight.SHA256.Semantics.Gates
