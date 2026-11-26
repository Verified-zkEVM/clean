import Midnight.SHA256.Semantics.GatesSource
import Midnight.SHA256.Semantics.GatesParity
import Midnight.SHA256.Semantics.Prepare

/-! Integer contracts extracted from the native word-preparation gates. Gate
premises are actual Clean operation constraints at the source rotations. The
lookup facts below are supplied by the shared spread lookup extraction. -/

namespace Midnight.SHA256.Semantics.PrepareGates
open Halo2 Gates Midnight.SHA256.Semantics Decomposition Midnight.Keygen

set_option linter.constructorNameAsVariable false

attribute [local irreducible] SpreadLookup Midnight.SHA256.activation

private theorem clean_sum (a b : Midnight.Keygen.E) : a + b = Halo2.Expression.add a b := rfl

private theorem clean_sub (a b : Midnight.Keygen.E) :
    a - b = Halo2.Expression.add a (Halo2.Expression.mul (Halo2.Expression.const (-1)) b) := rfl

private theorem clean_mul (a b : Midnight.Keygen.E) : a * b = Halo2.Expression.mul a b := rfl

section Equations
variable {place : RegionIndex → Nat} {self : RegionIndex}
  {env : Environment F} {row : Nat}

local notation "r" => Gates.read env (place self + row : Nat)

theorem a_equations
    (satisfied : RegionOperations.Constraints place self env (activation 12 row)) :
    (2 ^ 22 : F) * r 0 (-1) + 2 ^ 13 * r 2 (-1) + 2 ^ 2 * r 0 0 + r 2 0 = r 4 (-1) ∧
    (2 ^ 44 : F) * r 1 (-1) + 2 ^ 26 * r 3 (-1) + 2 ^ 4 * r 1 0 + r 3 0 = r 4 0 := by
  rw [activation_a] at satisfied
  have h := satisfied.1
  norm_num [RegionOperation.Constraints, aGate, aSpec, GateSpec.toClean,
    pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm] at h
  norm_num [Gates.read, Synthesis.shaAdvice]
  constructor
  · linear_combination (norm := ring_nf) h.1
  · linear_combination (norm := ring_nf) h.2

theorem e_equations
    (satisfied : RegionOperations.Constraints place self env (activation 13 row)) :
    (2 ^ 25 : F) * r 0 (-1) + 2 ^ 13 * r 2 (-1) + 2 ^ 11 * r 0 0 +
      2 ^ 6 * r 2 0 + r 0 1 = r 4 (-1) ∧
    (2 ^ 50 : F) * r 1 (-1) + 2 ^ 26 * r 3 (-1) + 2 ^ 22 * r 1 0 +
      2 ^ 12 * r 3 0 + r 1 1 = r 4 0 := by
  rw [activation_e] at satisfied
  have h := satisfied.1
  norm_num [RegionOperation.Constraints, eGate, eSpec, GateSpec.toClean,
    pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm] at h
  norm_num [Gates.read, Synthesis.shaAdvice]
  constructor
  · linear_combination (norm := ring_nf) h.1
  · linear_combination (norm := ring_nf) h.2

theorem message_equations
    (satisfied : RegionOperations.Constraints place self env (activation 14 row)) :
    ((2 ^ 20 : F) * r 0 (-1) + 2 ^ 19 * r 7 (-1) + 2 ^ 18 * r 7 0 +
      2 ^ 17 * r 7 1 + 2 ^ 10 * r 2 (-1) + 2 ^ 7 * r 0 0 + 2 ^ 3 * r 2 0 + r 0 1 =
      r 4 (-1)) ∧
    r 7 (-1) * (r 7 (-1) - 1) = 0 ∧
    r 7 0 * (r 7 0 - 1) = 0 ∧ r 7 1 * (r 7 1 - 1) = 0 := by
  rw [activation_message] at satisfied
  have h := satisfied.1
  norm_num [RegionOperation.Constraints, messageGate, messageSpec, GateSpec.toClean,
    pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm] at h
  norm_num [Gates.read, Synthesis.shaAdvice]
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (norm := ring_nf) h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem addMod_equation
    (satisfied : RegionOperations.Constraints place self env (activation 15 row)) :
    r 5 (-1) + r 6 (-1) + r 5 0 + r 6 0 + r 4 1 + r 5 1 + r 6 1 =
      r 4 (-1) + r 2 1 * (2 ^ 32 : F) := by
  rw [activation_addMod] at satisfied
  have h := satisfied.1
  norm_num [RegionOperation.Constraints, addModGate, addModSpec, GateSpec.toClean,
    pow4ip, pow2ip, sumExpr, clean_sum, clean_sub, clean_mul, circuit_norm] at h
  norm_num [Gates.read, Synthesis.shaAdvice]
  linear_combination (norm := ring_nf) h

end Equations

/-- The lookup facts at the exact limb cells used by the A decomposition. -/
def ALookups (env : Environment F) (absolute : Int) : Prop :=
  SpreadLookup 10 (read env absolute 0 (-1)) (read env absolute 1 (-1)) ∧
  SpreadLookup 9 (read env absolute 2 (-1)) (read env absolute 3 (-1)) ∧
  SpreadLookup 11 (read env absolute 0 0) (read env absolute 1 0) ∧
  SpreadLookup 2 (read env absolute 2 0) (read env absolute 3 0)

def aValues (env : Environment F) (absolute : Int) : List Limb :=
  aLimbs (read env absolute 0 (-1)).val (read env absolute 2 (-1)).val
    (read env absolute 0 0).val (read env absolute 2 0).val

theorem a_bounded {env : Environment F} {absolute : Int}
    (lookups : ALookups env absolute) : Bounded (aValues env absolute) := by
  have h₀ := lookup_values (width := 10) (by norm_num [BLS12_381.scalarFieldSize]) lookups.1
  have h₁ := lookup_values (width := 9) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.1
  have h₂ := lookup_values (width := 11) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2.1
  have h₃ := lookup_values (width := 2) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2.2
  intro limb member
  simp only [aValues, aLimbs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact h₀.1
  · exact h₁.1
  · exact h₂.1
  · exact h₃.1

theorem a_spread_cast {env : Environment F} {absolute : Int}
    (lookups : ALookups env absolute) :
    (packSpread (aValues env absolute) : F) =
      (2 ^ 44 : F) * read env absolute 1 (-1) + 2 ^ 26 * read env absolute 3 (-1) +
      2 ^ 4 * read env absolute 1 0 + read env absolute 3 0 := by
  have h₀ := lookup_values (width := 10) (by norm_num [BLS12_381.scalarFieldSize]) lookups.1
  have h₁ := lookup_values (width := 9) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.1
  have h₂ := lookup_values (width := 11) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2.1
  have h₃ := lookup_values (width := 2) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2.2
  rw [h₀.2, h₁.2, h₂.2, h₃.2]
  norm_num [aValues, aLimbs, packSpread, width]
  ring

/-- Native gate12 and its actual limb memberships force a bounded word and
its precise spread value, for arbitrary satisfying advice assignments. -/
theorem a_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (gate : RegionOperations.Constraints place self env (activation 12 row))
    (lookups : ALookups env (place self + row : Nat)) :
    (read env (place self + row : Nat) 4 (-1)).val =
      pack (aValues env (place self + row : Nat)) ∧
    (read env (place self + row : Nat) 4 (-1)).val < 2 ^ 32 ∧
    (read env (place self + row : Nat) 4 0).val =
      spread (read env (place self + row : Nat) 4 (-1)).val := by
  have bounded := a_bounded (env := env) (absolute := (place self + row : Nat)) lookups
  have hwidth : width (aValues env (place self + row : Nat)) ≤ 32 := by
    norm_num [aValues, aLimbs, width]
  have equations := a_equations (place := place) (self := self) (env := env) (row := row) gate
  have plain : (pack (aValues env (place self + row : Nat)) : F) -
      read env (place self + row : Nat) 4 (-1) = 0 := by
    apply sub_eq_zero.mpr
    simpa only [aValues, pack_a, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, ZMod.natCast_zmod_val] using equations.1
  have expanded : (packSpread (aValues env (place self + row : Nat)) : F) -
      read env (place self + row : Nat) 4 0 = 0 := by
    rw [a_spread_cast (env := env) (absolute := (place self + row : Nat)) lookups, sub_eq_zero]
    exact equations.2
  exact ⟨(plain_gate_sound _ bounded hwidth plain).1,
    spread_gate_sound _ bounded hwidth plain expanded⟩

def ELookups (env : Environment F) (absolute : Int) : Prop :=
  SpreadLookup 7 (read env absolute 0 (-1)) (read env absolute 1 (-1)) ∧
  SpreadLookup 12 (read env absolute 2 (-1)) (read env absolute 3 (-1)) ∧
  SpreadLookup 2 (read env absolute 0 0) (read env absolute 1 0) ∧
  SpreadLookup 5 (read env absolute 2 0) (read env absolute 3 0) ∧
  SpreadLookup 6 (read env absolute 0 1) (read env absolute 1 1)

def eValues (env : Environment F) (absolute : Int) : List Limb :=
  eLimbs (read env absolute 0 (-1)).val (read env absolute 2 (-1)).val
    (read env absolute 0 0).val (read env absolute 2 0).val (read env absolute 0 1).val

theorem e_bounded {env : Environment F} {absolute : Int}
    (lookups : ELookups env absolute) : Bounded (eValues env absolute) := by
  have h₀ := lookup_values (width := 7) (by norm_num [BLS12_381.scalarFieldSize]) lookups.1
  have h₁ := lookup_values (width := 12) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.1
  have h₂ := lookup_values (width := 2) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2.1
  have h₃ := lookup_values (width := 5) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2.2.1
  have h₄ := lookup_values (width := 6) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2.2.2
  intro limb member
  simp only [eValues, eLimbs, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact h₀.1
  · exact h₁.1
  · exact h₂.1
  · exact h₃.1
  · exact h₄.1

theorem e_spread_cast {env : Environment F} {absolute : Int}
    (lookups : ELookups env absolute) :
    (packSpread (eValues env absolute) : F) =
      (2 ^ 50 : F) * read env absolute 1 (-1) + 2 ^ 26 * read env absolute 3 (-1) +
      2 ^ 22 * read env absolute 1 0 + 2 ^ 12 * read env absolute 3 0 + read env absolute 1 1 := by
  have h₀ := lookup_values (width := 7) (by norm_num [BLS12_381.scalarFieldSize]) lookups.1
  have h₁ := lookup_values (width := 12) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.1
  have h₂ := lookup_values (width := 2) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2.1
  have h₃ := lookup_values (width := 5) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2.2.1
  have h₄ := lookup_values (width := 6) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2.2.2
  rw [h₀.2, h₁.2, h₂.2, h₃.2, h₄.2]
  norm_num [eValues, eLimbs, packSpread, width]
  ring

theorem e_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (gate : RegionOperations.Constraints place self env (activation 13 row))
    (lookups : ELookups env (place self + row : Nat)) :
    (read env (place self + row : Nat) 4 (-1)).val =
      pack (eValues env (place self + row : Nat)) ∧
    (read env (place self + row : Nat) 4 (-1)).val < 2 ^ 32 ∧
    (read env (place self + row : Nat) 4 0).val =
      spread (read env (place self + row : Nat) 4 (-1)).val := by
  have bounded := e_bounded (env := env) (absolute := (place self + row : Nat)) lookups
  have hwidth : width (eValues env (place self + row : Nat)) ≤ 32 := by
    norm_num [eValues, eLimbs, width]
  have equations := e_equations (place := place) (self := self) (env := env) (row := row) gate
  have plain : (pack (eValues env (place self + row : Nat)) : F) -
      read env (place self + row : Nat) 4 (-1) = 0 := by
    apply sub_eq_zero.mpr
    simpa only [eValues, pack_e, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, ZMod.natCast_zmod_val] using equations.1
  have expanded : (packSpread (eValues env (place self + row : Nat)) : F) -
      read env (place self + row : Nat) 4 0 = 0 := by
    rw [e_spread_cast (env := env) (absolute := (place self + row : Nat)) lookups, sub_eq_zero]
    exact equations.2
  exact ⟨(plain_gate_sound _ bounded hwidth plain).1,
    spread_gate_sound _ bounded hwidth plain expanded⟩

def MessageLookups (env : Environment F) (absolute : Int) : Prop :=
  SpreadLookup 12 (read env absolute 0 (-1)) (read env absolute 1 (-1)) ∧
  SpreadLookup 7 (read env absolute 2 (-1)) (read env absolute 3 (-1)) ∧
  SpreadLookup 3 (read env absolute 0 0) (read env absolute 1 0) ∧
  SpreadLookup 4 (read env absolute 2 0) (read env absolute 3 0) ∧
  SpreadLookup 3 (read env absolute 0 1) (read env absolute 1 1)

def messageValues (env : Environment F) (absolute : Int) : List Limb :=
  messageLimbs (read env absolute 0 (-1)).val (read env absolute 7 (-1)).val
    (read env absolute 7 0).val (read env absolute 7 1).val
    (read env absolute 2 (-1)).val (read env absolute 0 0).val
    (read env absolute 2 0).val (read env absolute 0 1).val

theorem message_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (gate : RegionOperations.Constraints place self env (activation 14 row))
    (lookups : MessageLookups env (place self + row : Nat)) :
    Bounded (messageValues env (place self + row : Nat)) ∧
    (read env (place self + row : Nat) 4 (-1)).val =
      pack (messageValues env (place self + row : Nat)) ∧
    (read env (place self + row : Nat) 4 (-1)).val < 2 ^ 32 := by
  have h₀ := lookup_values (width := 12) (by norm_num [BLS12_381.scalarFieldSize]) lookups.1
  have h₁ := lookup_values (width := 7) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.1
  have h₂ := lookup_values (width := 3) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2.1
  have h₃ := lookup_values (width := 4) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2.2.1
  have h₄ := lookup_values (width := 3) (by norm_num [BLS12_381.scalarFieldSize]) lookups.2.2.2.2
  have equations := message_equations (place := place) (self := self) (env := env) (row := row) gate
  have bounded : Bounded (messageValues env (place self + row : Nat)) := by
    intro limb member
    simp only [messageValues, messageLimbs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h₀.1
    · exact bool_val_lt_two equations.2.1
    · exact bool_val_lt_two equations.2.2.1
    · exact bool_val_lt_two equations.2.2.2
    · exact h₁.1
    · exact h₂.1
    · exact h₃.1
    · exact h₄.1
  refine ⟨bounded, plain_gate_sound _ bounded ?_ ?_⟩
  · norm_num [messageValues, messageLimbs, width]
  · apply sub_eq_zero.mpr
    simpa only [messageValues, pack_message, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat, ZMod.natCast_zmod_val] using equations.1

def summandValues (env : Environment F) (absolute : Int) : List Nat :=
  [(read env absolute 5 (-1)).val, (read env absolute 6 (-1)).val,
   (read env absolute 5 0).val, (read env absolute 6 0).val,
   (read env absolute 4 1).val, (read env absolute 5 1).val, (read env absolute 6 1).val]

private theorem sum_bound (values : List Nat) (count : values.length ≤ 7)
    (bounded : ∀ value ∈ values, value < 2 ^ 32) : values.sum < 7 * 2 ^ 32 := by
  have h := List.sum_le_length_nsmul values (2 ^ 32 - 1) (by
    intro value member
    have hv := bounded value member
    omega)
  simp only [nsmul_eq_mul] at h
  norm_num at h ⊢
  omega

/-- The addition result is determined by the actual native gate. Its 32-bit
bound comes from the accompanying decomposition; the carry bound comes from
the real three-bit lookup, not an honest-witness assumption. -/
theorem addMod_sound {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} {row : Nat}
    (gate : RegionOperations.Constraints place self env (activation 15 row))
    (inputs : ∀ value ∈ summandValues env (place self + row : Nat), value < 2 ^ 32)
    (output : (read env (place self + row : Nat) 4 (-1)).val < 2 ^ 32)
    (carry : SpreadLookup 3 (read env (place self + row : Nat) 2 1)
      (read env (place self + row : Nat) 3 1)) :
    (read env (place self + row : Nat) 4 (-1)).val =
      (summandValues env (place self + row : Nat)).sum % 2 ^ 32 ∧
    (read env (place self + row : Nat) 2 1).val =
      (summandValues env (place self + row : Nat)).sum / 2 ^ 32 := by
  have hsum := sum_bound _ (by simp [summandValues]) inputs
  have hcarry := lookup_values (width := 3) (by norm_num [BLS12_381.scalarFieldSize]) carry
  apply add32_gate_sound hsum output hcarry.1
  have h := addMod_equation (place := place) (self := self) (env := env) (row := row) gate
  simp only [Nat.cast_add] at h
  simp only [summandValues, List.sum_cons, List.sum_nil, Nat.cast_add,
    ZMod.natCast_zmod_val, add_zero]
  linear_combination (norm := ring_nf) h

end Midnight.SHA256.Semantics.PrepareGates
