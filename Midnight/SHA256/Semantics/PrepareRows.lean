import Midnight.SHA256.Semantics.PrepareGates

/-! Compose the native word-preparation gate contracts with all actual lookup
activations and fixed width tags. These lemmas consume constraint facts from
the source regions; no lookup meaning or desired output is assumed as a
prover precondition. -/
namespace Midnight.SHA256.Semantics.PrepareRows
open Halo2 Gates PrepareGates

attribute [local irreducible] SpreadLookup Midnight.SHA256.activation
set_option linter.constructorNameAsVariable false

/-- The two fixed tags assigned in a native spread-lookup row. -/
def Tags (place : RegionIndex → Nat) (self : RegionIndex) (env : Environment F)
    (row left right : Nat) : Prop :=
  env.fixed ⟨0⟩ (place self + row : Nat) = (left : F) ∧
  env.fixed ⟨1⟩ (place self + row : Nat) = (right : F)

theorem lookup_row {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row left right : Nat}
    (table : SpreadTable env)
    (active : RegionOperations.Constraints place self env (activation 4 row))
    (tags : Tags place self env row left right) :
    SpreadLookup (left : F) (Gates.read env (place self + row : Nat) 0 0)
      (Gates.read env (place self + row : Nat) 1 0) ∧
    SpreadLookup (right : F) (Gates.read env (place self + row : Nat) 2 0)
      (Gates.read env (place self + row : Nat) 3 0) := by
  have h := activation_spread_sound (place := place) (self := self) (env := env)
    (row := row) table active
  rw [tags.1, tags.2] at h
  simpa only [Gates.read, Synthesis.shaAdvice, Int.add_zero, Fin.val_ofNat, Fin.val_natCast, Fin.val_zero, Fin.val_one, Nat.reduceMod,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
    show ((2 : Fin 8) : Nat) = 2 from rfl,
    show ((3 : Fin 8) : Nat) = 3 from rfl] using h

section ThreeRows
variable {place : RegionIndex → Nat} {self : RegionIndex} {env : Environment F}
  (table : SpreadTable env)
  (active0 : RegionOperations.Constraints place self env (activation 4 0))
  (active1 : RegionOperations.Constraints place self env (activation 4 1))
  (active2 : RegionOperations.Constraints place self env (activation 4 2))

include table active0 active1 active2

/-- The A decomposition's zero-width fifth limb shares the final row with the
three-bit carry. Both tuples are activated by the native source. -/
theorem a_lookups
    (tags0 : Tags place self env 0 10 9)
    (tags1 : Tags place self env 1 11 2)
    (tags2 : Tags place self env 2 0 3) :
    ALookups env (place self + 1 : Nat) ∧
    SpreadLookup 3 (Gates.read env (place self + 1 : Nat) 2 1)
      (Gates.read env (place self + 1 : Nat) 3 1) := by
  have h0 := lookup_row (place := place) (self := self) (env := env) (row := 0)
    table active0 tags0
  have h1 := lookup_row (place := place) (self := self) (env := env) (row := 1)
    table active1 tags1
  have h2 := lookup_row (place := place) (self := self) (env := env) (row := 2)
    table active2 tags2
  norm_num [ALookups, Gates.read, Synthesis.shaAdvice, Nat.cast_add] at h0 h1 h2 ⊢
  exact ⟨⟨h0.1, h0.2, h1.1, h1.2⟩, h2.2⟩

theorem e_lookups
    (tags0 : Tags place self env 0 7 12)
    (tags1 : Tags place self env 1 2 5)
    (tags2 : Tags place self env 2 6 3) :
    ELookups env (place self + 1 : Nat) ∧
    SpreadLookup 3 (Gates.read env (place self + 1 : Nat) 2 1)
      (Gates.read env (place self + 1 : Nat) 3 1) := by
  have h0 := lookup_row (place := place) (self := self) (env := env) (row := 0)
    table active0 tags0
  have h1 := lookup_row (place := place) (self := self) (env := env) (row := 1)
    table active1 tags1
  have h2 := lookup_row (place := place) (self := self) (env := env) (row := 2)
    table active2 tags2
  norm_num [ELookups, Gates.read, Synthesis.shaAdvice, Nat.cast_add] at h0 h1 h2 ⊢
  exact ⟨⟨h0.1, h0.2, h1.1, h1.2, h2.1⟩, h2.2⟩

theorem message_lookups
    (tags0 : Tags place self env 0 12 7)
    (tags1 : Tags place self env 1 3 4)
    (tags2 : Tags place self env 2 3 3) :
    MessageLookups env (place self + 1 : Nat) ∧
    SpreadLookup 3 (Gates.read env (place self + 1 : Nat) 2 1)
      (Gates.read env (place self + 1 : Nat) 3 1) := by
  have h0 := lookup_row (place := place) (self := self) (env := env) (row := 0)
    table active0 tags0
  have h1 := lookup_row (place := place) (self := self) (env := env) (row := 1)
    table active1 tags1
  have h2 := lookup_row (place := place) (self := self) (env := env) (row := 2)
    table active2 tags2
  norm_num [MessageLookups, Gates.read, Synthesis.shaAdvice, Nat.cast_add] at h0 h1 h2 ⊢
  exact ⟨⟨h0.1, h0.2, h1.1, h1.2, h2.1⟩, h2.2⟩

local notation "r" => Gates.read env (place self + 1 : Nat)
local notation "total" => List.sum (summandValues env (place self + 1 : Nat))

/-- The three actual A rows force the modular sum and every representation
invariant needed by later rounds. Inputs are bounded words; output bounds and
spread correctness are conclusions of the native constraints. -/
theorem a_result
    (gate : RegionOperations.Constraints place self env (activation 12 1))
    (addition : RegionOperations.Constraints place self env (activation 15 1))
    (tags0 : Tags place self env 0 10 9)
    (tags1 : Tags place self env 1 11 2)
    (tags2 : Tags place self env 2 0 3)
    (inputs : ∀ value ∈ summandValues env (place self + 1 : Nat), value < 2 ^ 32) :
    Decomposition.Bounded (aValues env (place self + 1 : Nat)) ∧
    (r 4 (-1)).val = Decomposition.pack (aValues env (place self + 1 : Nat)) ∧
    (r 4 (-1)).val < 2 ^ 32 ∧ (r 4 0).val = spread (r 4 (-1)).val ∧
    (r 4 (-1)).val = total % 2 ^ 32 ∧ (r 2 1).val = total / 2 ^ 32 := by
  have lookups := a_lookups (place := place) (self := self) (env := env)
    table active0 active1 active2 tags0 tags1 tags2
  have bounds := PrepareGates.a_bounded (env := env) (absolute := (place self + 1 : Nat)) lookups.1
  have decoded := PrepareGates.a_sound (place := place) (self := self) (env := env)
    (row := 1) gate lookups.1
  have summed := addMod_sound (place := place) (self := self) (env := env) (row := 1)
    addition inputs decoded.2.1 lookups.2
  exact ⟨bounds, decoded.1, decoded.2.1, decoded.2.2, summed⟩

theorem e_result
    (gate : RegionOperations.Constraints place self env (activation 13 1))
    (addition : RegionOperations.Constraints place self env (activation 15 1))
    (tags0 : Tags place self env 0 7 12)
    (tags1 : Tags place self env 1 2 5)
    (tags2 : Tags place self env 2 6 3)
    (inputs : ∀ value ∈ summandValues env (place self + 1 : Nat), value < 2 ^ 32) :
    Decomposition.Bounded (eValues env (place self + 1 : Nat)) ∧
    (r 4 (-1)).val = Decomposition.pack (eValues env (place self + 1 : Nat)) ∧
    (r 4 (-1)).val < 2 ^ 32 ∧ (r 4 0).val = spread (r 4 (-1)).val ∧
    (r 4 (-1)).val = total % 2 ^ 32 ∧ (r 2 1).val = total / 2 ^ 32 := by
  have lookups := e_lookups (place := place) (self := self) (env := env)
    table active0 active1 active2 tags0 tags1 tags2
  have bounds := PrepareGates.e_bounded (env := env) (absolute := (place self + 1 : Nat)) lookups.1
  have decoded := PrepareGates.e_sound (place := place) (self := self) (env := env)
    (row := 1) gate lookups.1
  have summed := addMod_sound (place := place) (self := self) (env := env) (row := 1)
    addition inputs decoded.2.1 lookups.2
  exact ⟨bounds, decoded.1, decoded.2.1, decoded.2.2, summed⟩

theorem message_result
    (gate : RegionOperations.Constraints place self env (activation 14 1))
    (addition : RegionOperations.Constraints place self env (activation 15 1))
    (tags0 : Tags place self env 0 12 7)
    (tags1 : Tags place self env 1 3 4)
    (tags2 : Tags place self env 2 3 3)
    (inputs : ∀ value ∈ summandValues env (place self + 1 : Nat), value < 2 ^ 32) :
    Decomposition.Bounded (messageValues env (place self + 1 : Nat)) ∧
    (r 4 (-1)).val = Decomposition.pack (messageValues env (place self + 1 : Nat)) ∧
    (r 4 (-1)).val < 2 ^ 32 ∧
    (r 4 (-1)).val = total % 2 ^ 32 ∧ (r 2 1).val = total / 2 ^ 32 := by
  have lookups := message_lookups (place := place) (self := self) (env := env)
    table active0 active1 active2 tags0 tags1 tags2
  have decoded := PrepareGates.message_sound (place := place) (self := self) (env := env)
    (row := 1) gate lookups.1
  have summed := addMod_sound (place := place) (self := self) (env := env) (row := 1)
    addition inputs decoded.2.2 lookups.2
  exact ⟨decoded.1, decoded.2.1, decoded.2.2, summed⟩

end ThreeRows
end Midnight.SHA256.Semantics.PrepareRows
