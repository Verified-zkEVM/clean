import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.PropertyLookup
import Clean.Circuit.Subcircuit
import Clean.Circuit.Expression
import Clean.Utils.Field
import Clean.Utils.Tactics.CircuitProofStart

/-!
# Fibonacci Example with Yield/Use Framework

This example demonstrates the yield/use framework by implementing a Fibonacci sequence generator
using two circuits:
- Base circuit: yields Fib(0,1) and Fib(1,1)
- Step circuit: uses Fib(n,a) and Fib(n+1,b), yields Fib(n+2,a+b)
-/

namespace Clean.Examples.FibonacciYield

/-- The Fibonacci sequence as a function from natural numbers to field elements -/
def fib {F : Type} [Field F] : ℕ → F
  | 0 => 1
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- Helper lemma: fib satisfies the recurrence relation -/
lemma fib_add_two {F : Type} [Field F] (n : ℕ) :
  fib (F:=F) (n + 2) = fib (F:=F) n + fib (F:=F) (n + 1) := by
  rfl

section FibProperty

variable {F : Type} [Field F]

/-- The Fib property that takes 2 arguments: index and value -/
def FibProperty : Property F := {
  name := "Fib"
  arity := 2
  Predicate := fun v =>
    -- v[0] is the index (as a field element), v[1] is the fibonacci value
    -- The predicate checks that v[1] equals fib of the natural number corresponding to v[0]
    ∃ n : ℕ, v[0] = (n : F) ∧ v[1] = fib n
}

/-- PropertySet containing only the Fib property -/
def FibPropertySet : PropertySet F := {
  properties := Std.HashMap.ofList [("Fib", FibProperty)]
  NameConsistency := by
    intro _ _
    simp only [Std.HashMap.ofList_singleton, Std.HashMap.getElem?_insert]
    aesop
}

/-- Helper function to create a Fibonacci sentence -/
def mkFibSentence
    (index : Expression F) (value : Expression F) : Sentence (FibPropertySet : PropertySet F) (Expression F) := {
  name := "Fib"
  property := FibProperty
  propertyFound := by
    simp only [FibPropertySet, Std.HashMap.ofList_singleton, Std.HashMap.getElem?_insert]
    aesop
  entry := #v[index, value]
}

/-- Dependency relation for Fib sentences based on index ordering -/
def FibCanDepend : Sentence (@FibPropertySet F _) F → Sentence (@FibPropertySet F _) F → Prop :=
  fun s t =>
    s.name = "Fib" ∧ t.name = "Fib" ∧
    ∃ (ns nt : ℕ),
      ∃ (h1 : s.property.arity = 2),
      ∃ (h2 : t.property.arity = 2),
      s.entry[0] = (ns : F) ∧ t.entry[0] = (nt : F) ∧ ns < nt

/-- Extract natural number index from a Fib sentence, default to 0 for non-Fib -/
def sentenceToNat (s : Sentence (@FibPropertySet F _) F) : ℕ :=
  if s.name = "Fib" then
    -- For Fib sentences, we need to extract the natural number from entry[0]
    -- This is safe because FibCanDepend only relates Fib sentences
    -- and the well-foundedness proof only needs consistency for those
    sorry  -- Will implement extraction logic
  else
    0

/-- The FibCanDepend relation is well-founded -/
theorem FibCanDepend_wf : WellFounded (@FibCanDepend F _) := by
  sorry  -- Will prove using InvImage.wf

/-- Simple order: Fib at smaller index can be used for Fib at larger index -/
def FibOrder : SentenceOrder (@FibPropertySet F _) := {
  CanDepend := FibCanDepend
  well_founded := FibCanDepend_wf
}

/-- Lemma: The Fib property correctly captures the Fibonacci sequence -/
lemma fib_property_correct (n : ℕ) :
  FibProperty.Predicate #v[(n : F), fib n] := by
  use n
  simp

end FibProperty

variable {p : ℕ} [Fact p.Prime]

/-- Base circuit that yields Fib(0,1) and Fib(1,1) -/
def FibBase.main (_input : Var unit (F p)) : Circuit (@FibPropertySet (F p) _) (Var unit (F p)) := do
  -- Yield Fib 0 1 (0th Fibonacci number is 1)
  Circuit.yield (mkFibSentence 0 1)

  -- Yield Fib 1 1 (1st Fibonacci number is 1)
  Circuit.yield (mkFibSentence 1 1)

  return ()

def FibBase.circuit : FormalCircuit (@FibOrder (F p) _) unit unit where
  main := FibBase.main
  localLength _ := 0
  localLength_eq := by
    intro _
    simp [FibBase.main, Circuit.localLength, circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    -- Unfold the main function and operations
    simp only [FibBase.main, Circuit.operations, Operations.SubcircuitsConsistent]
    -- Expand the forAll for yield operations
    simp only [bind]
    -- All conditions are trivial (True) for yield operations
    trivial
  Assumptions _ := True
  CompletenessAssumptions _ _ := True
  completenessAssumptions_implies_assumptions _ _ h := h
  Spec _ _ _ := True  -- Base circuit doesn't produce output, just yields
  soundness := by
    circuit_proof_start
    intro s
    simp only [Set.union_empty, Set.union_singleton, Set.mem_insert_iff, Set.mem_singleton_iff]
    intro h_s
    rcases h_s
    · rename_i h_s
      intro _
      simp only [SentenceHolds]
      rw [h_s]
      simp only [Sentence.eval, mkFibSentence, FibProperty, circuit_norm]
      exists 1
      aesop
    · rename_i h_s
      intro _
      simp only [SentenceHolds]
      rw [h_s]
      simp only [Sentence.eval, mkFibSentence, FibProperty, circuit_norm]
      exists 0
      aesop
  completeness := by circuit_proof_start

/-- Step circuit parameterized by n, a, b that uses Fib(n,a) and Fib(n+1,b) and yields Fib(n+2,a+b) -/
def FibStep.main (n a b : F p) (_input : Var unit (F p)) : Circuit (@FibPropertySet (F p) _) (Var unit (F p)) := do
  -- Use Fib n a (assert that Fib(n) = a is available)
  use (mkFibSentence n a)

  -- Use Fib (n+1) b (assert that Fib(n+1) = b is available)
  use (mkFibSentence (n + 1) b)

  -- Yield Fib (n+2) (a+b)
  Circuit.yield (mkFibSentence (n + 2) (a + b))

  return ()

def FibStep.circuit (n a b : F p) : FormalCircuit (@FibOrder (F p) _) unit unit where
  main := FibStep.main n a b
  localLength _ := 0
  localLength_eq := by
    intro _
    simp [FibStep.main, Circuit.localLength, circuit_norm]
  subcircuitsConsistent := by
    intro input offset
    -- Unfold the main function and operations
    simp only [FibStep.main, Circuit.operations, Operations.SubcircuitsConsistent]
    -- Expand the forAll for use and yield operations
    simp only [bind]
    -- All conditions are trivial (True) for use and yield operations
    trivial
  Assumptions _ :=
    -- Assume the parameters correspond to actual Fibonacci values
    ∃ k : ℕ, k + 2 < p ∧ n = (k : F p) ∧
             a = fib k ∧
             b = fib (k + 1)
  CompletenessAssumptions yields _ :=
    -- Require that n+2 doesn't overflow in field arithmetic
    -- and that Fib(n) and Fib(n+1) are in the yields
    (∃ k : ℕ, k + 2 < p ∧ n = (k : F p) ∧
              a = fib k ∧
              b = fib (k + 1)) ∧
    let mkSent := @mkFibSentence (F p) _
    let env : Environment (F p) := Environment.mk (fun _ => 0)
    (mkSent n a).eval env ∈ yields.yielded ∧
    (mkSent (n + 1) b).eval env ∈ yields.yielded
  completenessAssumptions_implies_assumptions yields _ h := by
    obtain ⟨h_n, _, _⟩ := h
    exact h_n
  Spec _ _ _ := True  -- Step circuit doesn't produce output, just yields
  soundness := by
    circuit_proof_start
    intro s
    simp only [Operations.localYields]
    simp only [Set.union_empty, Set.mem_singleton_iff]
    intro s_eq
    simp only [s_eq, AllDependenciesChecked]
    intro h_dep
    rcases h_holds with ⟨ h_n_yielded, h_n_valid, h_s_n_yielded, h_s_n_valid ⟩
    obtain ⟨ k, h_assumptions ⟩ := h_assumptions
    specialize h_n_valid (by
      apply h_dep
      simp only [FibOrder, FibCanDepend, mkFibSentence, Sentence.eval, circuit_norm]
      use k, k + 2
      aesop)
    specialize h_s_n_valid (by
      apply h_dep
      simp only [FibOrder, FibCanDepend, mkFibSentence, Sentence.eval, circuit_norm]
      use k + 1, k + 2
      aesop)
    simp only [SentenceHolds, Sentence.eval, mkFibSentence, FibProperty] at h_n_valid h_s_n_valid ⊢
    obtain ⟨ n', h_n, h_n_valid ⟩ := h_n_valid
    obtain ⟨ s_n, h_s_n, h_s_n_valid ⟩ := h_s_n_valid
    simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at h_n h_s_n h_n_valid h_s_n_valid
    simp only [circuit_norm] at h_n h_s_n
    exists (k + 2)
    simp only [Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, Nat.cast_add, Nat.cast_ofNat,
      List.getElem_cons_succ, circuit_norm]
    aesop
  completeness := by
    circuit_proof_start
    rcases h_assumptions with ⟨ h_k, h_assumptions ⟩
    rcases h_k with ⟨ k, h_k ⟩
    and_intros
    · simp only [Sentence.eval, circuit_norm, mkFibSentence] at ⊢ h_assumptions
      aesop
    · intro _
      simp only [Sentence.eval, circuit_norm, mkFibSentence, SentenceHolds, FibProperty] at ⊢
      exists k
      aesop
    · simp only [Sentence.eval, circuit_norm, mkFibSentence] at ⊢ h_assumptions
      aesop
    · intro _
      simp only [Sentence.eval, circuit_norm, mkFibSentence, SentenceHolds, FibProperty] at ⊢
      exists k + 1
      aesop

/-- Example: Compose circuits to compute Fibonacci sequence up to index 4 -/
def computeFibUpTo4 : GeneralFormalCircuit (@FibOrder (F p) _) unit unit := by
  -- Start with base, then apply step twice
  -- Base yields Fib(0,1) and Fib(1,1)
  -- Step with (0,1,1) yields Fib(2,2)
  -- Step with (1,1,2) yields Fib(3,3)
  -- Step with (2,2,3) yields Fib(4,5)
  sorry

end Clean.Examples.FibonacciYield
