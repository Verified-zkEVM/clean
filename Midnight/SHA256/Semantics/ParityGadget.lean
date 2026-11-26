import Midnight.SHA256.Semantics.Gates
import Midnight.SHA256.WitnessCircuit
import Midnight.SHA256.WitnessSemantics

/-! Contracts for the actual plain/spread and 11/11/10 source gadgets. The
soundness direction uses constraints and the loaded table, never honest advice. -/
namespace Midnight.SHA256.Semantics.ParityGadget
open Halo2 Gates WitnessCircuit

attribute [local irreducible] SpreadLookup Midnight.SHA256.activation
attribute [local cbv_opaque] WitnessCircuit.enable WitnessCircuit.sa
  WitnessCircuit.plainAndSpread WitnessIR.limbs WitnessIR.evenBits WitnessIR.oddBits
attribute [local cbv_opaque] HAppend.hAppend
attribute [local cbv_opaque] BLS12_381.instFieldScalarField ZMod.instField ZMod.commRing

@[circuit_norm] theorem enable_operations (selector row : Nat) (self : RegionIndex) :
    (WitnessCircuit.enable selector row).operations self = activation selector row := rfl

@[circuit_norm] theorem enable_output (selector row : Nat) (self : RegionIndex) :
    (WitnessCircuit.enable selector row).output self = () := rfl

@[circuit_norm] theorem sa_output (index row : Nat) (value : U64Expr F) (self : RegionIndex) :
    (sa index row value).output self = .of self row (⟨Synthesis.shaAdvice[index]!⟩ : Column .advice) := rfl

@[circuit_norm] theorem sa_operations (index row : Nat) (value : U64Expr F) (self : RegionIndex) :
    (sa index row value).operations self =
      [.assignAdvice ⟨Synthesis.shaAdvice[index]!⟩ row (WitnessIR.program value)] := rfl

@[circuit_norm] theorem plainAndSpread_output (width offset index : Nat)
    (value : U64Expr F) (self : RegionIndex) :
    (plainAndSpread width offset index value).output self =
      ⟨.of self offset (⟨Synthesis.shaAdvice[2*index]!⟩ : Column .advice),
       .of self offset (⟨Synthesis.shaAdvice[2*index+1]!⟩ : Column .advice)⟩ := by
  simp only [plainAndSpread, circuit_norm]

/-- Complete constraint view of the source helper. Both native lookup tuples
are enabled; this helper fixes just its own tuple's tag. -/
theorem plainAndSpread_constraints (place : RegionIndex → Nat) (self : RegionIndex)
    (env : Environment F) (width offset index : Nat) (value : U64Expr F) :
    RegionOperations.Constraints place self env
      ((plainAndSpread width offset index value).operations self) ↔
    RegionOperations.Constraints place self env (activation 4 offset) ∧
      env.fixed ⟨index⟩ (place self + offset : Nat) = (width : F) := by
  simp only [plainAndSpread, circuit_norm, and_true]

/-- Width-tagged table meaning of the actual helper's returned cells. -/
theorem plainAndSpread_lookup {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env) (width offset : Nat) (index : Fin 2)
    (value : U64Expr F)
    (satisfied : RegionOperations.Constraints place self env
      ((plainAndSpread width offset index.val value).operations self)) :
    SpreadLookup (width : F)
      (((plainAndSpread width offset index.val value).output self).plain.eval place env)
      (((plainAndSpread width offset index.val value).output self).spread.eval place env) := by
  have facts := (plainAndSpread_constraints place self env width offset index value).mp satisfied
  have tuples := activation_spread_sound (place := place) (self := self) (env := env)
    (row := offset) table facts.1
  fin_cases index
  · simpa [plainAndSpread_output, Synthesis.shaAdvice, circuit_norm] using facts.2 ▸ tuples.1
  · simpa [plainAndSpread_output, Synthesis.shaAdvice, circuit_norm] using facts.2 ▸ tuples.2

/-- A finite expansion of the source's two three-iteration loops. -/
def expanded (odd : Bool) (offset : Nat) (value : U64Expr F) : Region (AssignedCell F) := do
  enable 11 (offset+1)
  let index := if odd then 1 else 0
  let evens := WitnessIR.limbs Witness.parityLayout (WitnessIR.evenBits value)
  let odds := WitnessIR.limbs Witness.parityLayout (WitnessIR.oddBits value)
  let _ ← plainAndSpread 11 offset index evens[0]!
  let _ ← plainAndSpread 11 (offset+1) index evens[1]!
  let _ ← plainAndSpread 10 (offset+2) index evens[2]!
  let _ ← plainAndSpread 11 offset (1-index) odds[0]!
  let _ ← plainAndSpread 11 (offset+1) (1-index) odds[1]!
  let _ ← plainAndSpread 10 (offset+2) (1-index) odds[2]!
  sa 4 offset (if odd then WitnessIR.oddBits value else WitnessIR.evenBits value)

theorem spread111110_expanded (odd : Bool) (offset : Nat) (value : U64Expr F) :
    spread111110 odd offset value = expanded odd offset value := by
  funext self
  unfold spread111110 expanded
  cbv
  simp only [List.append_assoc, List.append_nil]

@[circuit_norm] theorem spread111110_output (odd : Bool) (offset : Nat)
    (value : U64Expr F) (self : RegionIndex) :
    (spread111110 odd offset value).output self = .of self offset (⟨2⟩ : Column .advice) := by
  rw [spread111110_expanded]
  simp only [expanded, circuit_norm]
  rfl

/-- Both parity planes and the selected output gate follow from the actual
six assignments, including the case where the odd plane is returned first. -/
theorem spread111110_facts {place : RegionIndex → Nat} {self : RegionIndex}
    {env : Environment F} (table : SpreadTable env) (odd : Bool) (offset : Nat)
    (value : U64Expr F)
    (satisfied : RegionOperations.Constraints place self env
      ((spread111110 odd offset value).operations self)) :
    RegionOperations.Constraints place self env (activation 11 (offset+1)) ∧
      ParityLookups env (place self + (offset+1) : Nat) 0 1 ∧
      ParityLookups env (place self + (offset+1) : Nat) 2 3 := by
  rw [spread111110_expanded] at satisfied
  cases odd
  all_goals
    simp only [expanded, Bool.false_eq_true, ↓reduceIte, Nat.sub_zero, Nat.sub_self,
      circuit_norm, and_true] at satisfied
    obtain ⟨gate, h₀, h₁, h₂, h₃, h₄, h₅⟩ := satisfied
    have l₀ := plainAndSpread_lookup (place := place) (self := self) (env := env)
      table 11 offset ⟨_, by decide +kernel⟩ _ h₀
    have l₁ := plainAndSpread_lookup (place := place) (self := self) (env := env)
      table 11 (offset+1) ⟨_, by decide +kernel⟩ _ h₁
    have l₂ := plainAndSpread_lookup (place := place) (self := self) (env := env)
      table 10 (offset+2) ⟨_, by decide +kernel⟩ _ h₂
    have l₃ := plainAndSpread_lookup (place := place) (self := self) (env := env)
      table 11 offset ⟨_, by decide +kernel⟩ _ h₃
    have l₄ := plainAndSpread_lookup (place := place) (self := self) (env := env)
      table 11 (offset+1) ⟨_, by decide +kernel⟩ _ h₄
    have l₅ := plainAndSpread_lookup (place := place) (self := self) (env := env)
      table 10 (offset+2) ⟨_, by decide +kernel⟩ _ h₅
    refine ⟨gate, ?_⟩
    norm_num [plainAndSpread_output, Synthesis.shaAdvice, circuit_norm] at l₀ l₁ l₂ l₃ l₄ l₅
    norm_num [ParityLookups, Gates.read, Synthesis.shaAdvice, Nat.cast_add, Int.add_assoc] at l₀ l₁ l₂ l₃ l₄ l₅ ⊢
  · exact ⟨⟨l₀, l₁, l₂⟩, l₃, l₄, l₅⟩
  · exact ⟨⟨l₃, l₄, l₅⟩, l₀, l₁, l₂⟩

end Midnight.SHA256.Semantics.ParityGadget
