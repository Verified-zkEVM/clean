import Clean.Utils.Tactics
import Clean.Circuit
import Clean.Utils.Field

namespace TestCircuitProofStart

open Circuit

section BasicTests
-- Simple example to test the circuit_proof_start tactic
-- This section verifies that the tactic correctly:
-- 1. Introduces parameters until reaching Soundness/Completeness
-- 2. Applies provable_struct_simp
-- 3. Unfolds circuit definitions

-- Test that the tactic works for simple soundness proofs
example {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} (order : SentenceOrder sentences)
    (circuit : ElaboratedCircuit F sentences Input Output) (Assumptions : Input F → Prop)
    (Spec : CheckedYields sentences → Input F → Output F → Prop) :
    Soundness F circuit order Assumptions Spec := by
  circuit_proof_start
  -- At this point:
  -- - All standard soundness parameters have been introduced
  -- - provable_struct_simp has been applied
  -- - circuit_norm has been applied
  sorry

-- Test that the tactic works for simple completeness proofs
example {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} (order : SentenceOrder sentences)
    (circuit : ElaboratedCircuit F sentences Input Output) (Assumptions : Input F → Prop) :
    Completeness F sentences circuit Assumptions := by
  circuit_proof_start
  -- At this point:
  -- - All standard completeness parameters have been introduced
  -- - provable_struct_simp has been applied
  -- - circuit_norm has been applied
  sorry

-- Test parametrized soundness
example {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} (order : SentenceOrder sentences)
    (offset : Fin 8) (circuit : Fin 8 → ElaboratedCircuit F sentences Input Output)
    (Assumptions : Input F → Prop)
    (Spec : Fin 8 → CheckedYields sentences → Input F → Output F → Prop) :
    Soundness F (circuit offset) order Assumptions (Spec offset) := by
  circuit_proof_start
  -- offset is introduced first, then standard parameters
  sorry

-- Test parametrized completeness
example {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} (order : SentenceOrder sentences)
    (offset : Fin 8) (circuit : Fin 8 → ElaboratedCircuit F sentences Input Output)
    (Assumptions : Input F → Prop) :
    Completeness F sentences (circuit offset) Assumptions := by
  circuit_proof_start
  -- offset is introduced first, then standard parameters
  sorry

-- Test multiple parameters
example {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} (order : SentenceOrder sentences)
    (n : ℕ) (k : Fin n) (circuit : ℕ → Fin n → ElaboratedCircuit F sentences Input Output)
    (Assumptions : Input F → Prop)
    (Spec : ℕ → Fin n → CheckedYields sentences → Input F → Output F → Prop) :
    Soundness F (circuit n k) order Assumptions (Spec n k) := by
  circuit_proof_start
  -- n and k are introduced first, then standard parameters
  sorry

end BasicTests

section NamePreservationTests
-- Test that parameter names are preserved correctly

example {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} (order : SentenceOrder sentences)
    (circuit : ElaboratedCircuit F sentences Input Output)
    (Assumptions : Input F → Prop)
    (Spec : CheckedYields sentences → Input F → Output F → Prop) :
    Soundness F circuit order Assumptions Spec := by
  circuit_proof_start
  -- At this point we should have: offset, env, input_var, input, h_input, h_normalized, h_holds
  -- Check that these names exist by using them
  have : ℕ := i₀
  have : Environment F := env
  have : Input (Expression F) := input_var
  have : Input F := input
  have : eval env input_var = input := h_input
  have : Assumptions input := h_assumptions
  have : ConstraintsHold.Soundness env yields checked ((circuit.main input_var).operations i₀) := h_holds
  sorry

example {F : Type} [Field F] {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    {sentences : PropertySet F} (order : SentenceOrder sentences)
    (circuit : ElaboratedCircuit F sentences Input Output)
     (Assumptions : Input F → Prop) :
    Completeness F sentences circuit Assumptions := by
  circuit_proof_start
  -- At this point we should have: i₀, env, input_var, h_env
  -- Note: provable_struct_simp eliminates input and h_input by substituting eval env input_var
  -- Check that these names exist by using them
  have : ℕ := i₀
  have : Environment F := env
  have : Input (Expression F) := input_var
  have : env.UsesLocalWitnessesCompleteness yields i₀ ((circuit.main input_var).operations i₀) := h_env
  -- After provable_struct_simp, we work with eval env input_var instead of input
  sorry

end NamePreservationTests

section LocalDefinitionUnfoldingTests
-- Test that local Assumptions and Spec definitions are unfolded
-- Using unit TypeMap for simplicity

variable {p : ℕ} [Fact p.Prime]

namespace UnfoldTest1
variable {sentences : PropertySet (F p)} (order : SentenceOrder sentences)
-- Simple local definitions
def TestAssumptions (_ : unit (F p)) : Prop := True
def TestSpec (_ : unit (F p)) (_ : unit (F p)) : Prop := True

def Assumptions (input : unit (F p)) : Prop :=
  TestAssumptions input

def Spec (_ : CheckedYields sentences) (input : unit (F p)) (output : unit (F p)) : Prop :=
  TestSpec input output

def testCircuit : ElaboratedCircuit (F p) sentences unit unit :=
  { main := fun _ => pure (), output := fun _ _ => (), localLength := 0, output_eq := by simp }

example : Soundness (F p) testCircuit order Assumptions Spec := by
  circuit_proof_start
  -- Assumptions and Spec should be unfolded to TestAssumptions and TestSpec
  -- Check that Assumptions was unfolded by pattern matching on h_assumptions
  guard_hyp h_assumptions : TestAssumptions input
  sorry
end UnfoldTest1

namespace UnfoldTest2
variable {sentences : PropertySet (F p)} (order : SentenceOrder sentences)
-- Local definitions that reference module definitions (like in Compress.lean)
def TestAssumptions (_ : unit (F p)) : Prop := True
def TestSpec (_ : unit (F p)) (_ : unit (F p)) : Prop := True

def Assumptions (input : unit (F p)) : Prop :=
  TestAssumptions input ∧
  TestAssumptions input

def Spec (_ : CheckedYields sentences) (input : unit (F p)) (output : unit (F p)) : Prop :=
  TestSpec input output ∧ TestSpec input output

def testCircuit : ElaboratedCircuit (F p) sentences unit unit :=
  { main := fun _ => pure (), output := fun _ _ => (), localLength := 0, output_eq := by simp }

example : Soundness (F p) testCircuit order Assumptions Spec := by
  circuit_proof_start
  -- Should unfold nested references
  -- Check that Assumptions was unfolded to reveal TestAssumptions
  guard_hyp h_assumptions : TestAssumptions input ∧ TestAssumptions input
  sorry
end UnfoldTest2

namespace UnfoldTest3
variable {sentences : PropertySet (F p)} (order : SentenceOrder sentences)
-- Test that elaborated definition is unfolded
def testCircuit : ElaboratedCircuit (F p) sentences unit unit :=
  { main := fun _ => pure (), output := fun _ _ => (), localLength := 0, output_eq := by simp }

def elaborated : ElaboratedCircuit (F p) sentences unit unit :=
  testCircuit

  def TestAssumptions (_ : unit (F p)) : Prop := True
  def TestSpec (_ : CheckedYields sentences) (_ : unit (F p)) (_ : unit (F p)) : Prop := True

example : Soundness (F p) elaborated order TestAssumptions TestSpec := by
  circuit_proof_start
  -- elaborated should be unfolded to testCircuit
  -- Check that h_holds now refers to testCircuit.main, not elaborated.main
  guard_hyp h_holds : ConstraintsHold.Soundness env yields checked ((testCircuit.main input_var).operations i₀)
  sorry
end UnfoldTest3

end LocalDefinitionUnfoldingTests

-- Removed section ProvableStructSimpTests that tested with fieldPair

end TestCircuitProofStart
