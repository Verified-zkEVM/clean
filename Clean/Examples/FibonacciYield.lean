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

variable {p : ℕ} [Fact p.Prime]

/-- The Fib property that takes 2 arguments: index and value -/
def FibProperty : Property (F p) := {
  name := "Fib"
  arity := 2
  Predicate := fun v =>
    -- v[0] is the index (as a field element), v[1] is the fibonacci value
    -- The predicate checks that v[1] equals fib of the natural number corresponding to v[0]
    ∃ n : ℕ, v[0] = (n : F p) ∧ v[1] = fib n
}

/-- PropertySet containing only the Fib property -/
def FibPropertySet : PropertySet (F p) := {
  properties := Std.HashMap.ofList [("Fib", FibProperty)]
  NameConsistency := by
    intro _ _
    simp only [Std.HashMap.ofList_singleton, Std.HashMap.getElem?_insert]
    aesop
}

/-- Helper function to create a Fibonacci sentence -/
def mkFibSentence
    (index : Expression (F p)) (value : Expression (F p)) : Sentence (FibPropertySet : PropertySet (F p)) (Expression (F p)) := {
  name := "Fib"
  property := FibProperty
  propertyFound := by
    simp only [FibPropertySet, Std.HashMap.ofList_singleton, Std.HashMap.getElem?_insert]
    aesop
  entry := #v[index, value]
}

/-- Helper function to create a Fibonacci sentence with field element values -/
def mkFibSentenceValue
    (index : F p) (value : F p) : Sentence (FibPropertySet : PropertySet (F p)) (F p) := {
  name := "Fib"
  property := FibProperty
  propertyFound := by
    simp only [FibPropertySet, Std.HashMap.ofList_singleton, Std.HashMap.getElem?_insert]
    aesop
  entry := #v[index, value]
}

/-- Dependency relation for Fib sentences based on index ordering -/
def FibCanDepend : Sentence (@FibPropertySet p _) (F p) → Sentence (@FibPropertySet p _) (F p) → Prop :=
  fun s t =>
    s.name = "Fib" ∧ t.name = "Fib" ∧
    ∃ (ns nt : ℕ),
      ∃ (h1 : s.property.arity = 2),
      ∃ (h2 : t.property.arity = 2),
      s.entry[0]'(by omega) = (ns : F p) ∧ t.entry[0]'(by omega) = (nt : F p) ∧ ns < nt ∧ nt < p

/-- Extract natural number index from a Fib sentence, default to 0 for non-Fib -/
def sentenceToNat (s : Sentence (@FibPropertySet p _) (F p)) : ℕ := by
  -- Check if this is a Fib sentence
  if h : s.name = "Fib" then
    -- For a Fib sentence, we know from FibProperty.Predicate that
    -- there exists n : ℕ such that s.entry[0] = (n : F)
    -- We need to extract this n
    have h_prop : s.property = FibProperty := by
      rcases s
      rename_i name prop h_prop entry
      simp only at h
      simp only [FibPropertySet, h] at h_prop
      simp only [Std.HashMap.ofList_singleton, Std.HashMap.mem_insert, BEq.rfl,
        Std.HashMap.not_mem_empty, or_false, getElem?_pos, Std.HashMap.getElem_insert_self,
        Option.some.injEq] at h_prop
      simp_all
    rcases s
    rename_i name prop h_prop entry
    simp only at h_prop
    have : 0 < prop.arity := by
      simp only [h_prop, FibProperty]
      omega
    exact entry[0].val
  else
    -- Not a Fib sentence, return 0
    exact 0

/-- Helper lemma: FibCanDepend implies ordering on extracted natural numbers -/
lemma FibCanDepend_implies_nat_lt {p : ℕ} [Fact p.Prime] :
    ∀ s t, @FibCanDepend p _ s t → @sentenceToNat p _ s < @sentenceToNat p _ t := by
  intro s t h_dep
  -- Unpack the FibCanDepend relation
  obtain ⟨h_s_fib, h_t_fib, ns, nt, h1, h2, h_s_entry, h_t_entry, h_lt, h_nt_lt_p⟩ := h_dep

  -- Now we need to show sentenceToNat s < sentenceToNat t
  -- By definition of sentenceToNat and the fact that both are Fib sentences
  unfold sentenceToNat
  -- Both have name "Fib", so the if branches are taken
  simp only [h_s_fib, h_t_fib]

  -- The goal now has if h : True then ... else 0 for both sides
  -- Since True is always true, we can simplify
  split
  · -- Now we're in the case where both conditions are true
    -- The goal is about (cast).mp s.entry[0].val < (cast).mp t.entry[0].val
    -- We need to convert using our knowledge that s.entry[0] = (ns : F p) and ns < nt < p
    have h_ns_lt_p : ns < p := Nat.lt_trans h_lt h_nt_lt_p
    convert h_lt
    · simp only [h_s_entry]
      rw [ZMod.val_cast_of_lt]
      assumption
    · simp only [h_t_entry]
      rw [ZMod.val_cast_of_lt]
      assumption
  · -- This case is impossible since we have ¬True
    contradiction

/-- The FibCanDepend relation is well-founded -/
theorem FibCanDepend_wf : WellFounded (@FibCanDepend p _) := by
  -- Use Subrelation.wf to show FibCanDepend is well-founded
  apply Subrelation.wf
  · -- Prove FibCanDepend ⊆ InvImage (· < ·) sentenceToNat
    intro s t h_dep
    -- InvImage (· < ·) sentenceToNat s t unfolds to sentenceToNat s < sentenceToNat t
    exact FibCanDepend_implies_nat_lt s t h_dep
  · -- Prove WellFounded (InvImage (· < ·) sentenceToNat)
    exact InvImage.wf sentenceToNat Nat.lt_wfRel.wf

/-- Simple order: Fib at smaller index can be used for Fib at larger index -/
def FibOrder : SentenceOrder (@FibPropertySet p _) := {
  CanDepend := FibCanDepend
  well_founded := FibCanDepend_wf
}

/-- Lemma: The Fib property correctly captures the Fibonacci sequence -/
lemma fib_property_correct (n : ℕ) :
  FibProperty.Predicate #v[(n : F p), fib n] := by
  use n
  simp

end FibProperty

variable {p : ℕ} [Fact p.Prime]

/-- Base circuit that yields Fib(0,1) and Fib(1,1) -/
def FibBase.main (_input : Var unit (F p)) : Circuit (@FibPropertySet p _) (Var unit (F p)) := do
  -- Yield Fib 0 1 (0th Fibonacci number is 1)
  Circuit.yield (mkFibSentence 0 1)

  -- Yield Fib 1 1 (1st Fibonacci number is 1)
  Circuit.yield (mkFibSentence 1 1)

  return ()

def FibBase.circuit : FormalCircuit (@FibOrder p _) unit unit where
  main := FibBase.main
  localLength _ := 0
  yields _ _ _ :={
      mkFibSentenceValue 0 1,
      mkFibSentenceValue 1 1 }
  yields_eq := by
    intros _ _ _
    simp only [main, circuit_norm, Sentence.eval, mkFibSentence, mkFibSentenceValue]
    aesop
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
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    intro h_s
    rcases h_s
    · rename_i h_s
      intro _
      simp only [SentenceHolds]
      rw [h_s]
      simp only [FibProperty, circuit_norm, mkFibSentenceValue]
      exists 0
      aesop
    · rename_i h_s
      intro _
      simp only [SentenceHolds]
      rw [h_s]
      simp only [FibProperty, circuit_norm, mkFibSentenceValue]
      exists 1
      aesop
  completeness := by circuit_proof_start

/-- Step circuit parameterized by n, a, b that uses Fib(n,a) and Fib(n+1,b) and yields Fib(n+2,a+b) -/
def FibStep.main (n a b : F p) (_input : Var unit (F p)) : Circuit (@FibPropertySet p _) (Var unit (F p)) := do
  -- Use Fib n a (assert that Fib(n) = a is available)
  use (mkFibSentence n a)

  -- Use Fib (n+1) b (assert that Fib(n+1) = b is available)
  use (mkFibSentence (n + 1) b)

  -- Yield Fib (n+2) (a+b)
  Circuit.yield (mkFibSentence (n + 2) (a + b))

  return ()

def FibStep.circuit (n a b : F p) : FormalCircuit (@FibOrder p _) unit unit where
  main := FibStep.main n a b
  localLength _ := 0
  yields _ _ _ := { mkFibSentenceValue (n + 2) (a + b) }
  localLength_eq := by
    intro _
    simp [FibStep.main, Circuit.localLength, circuit_norm]
  yields_eq := by
    intros _ _ _
    simp [main, circuit_norm, mkFibSentence, Operations.localYields, Sentence.eval, mkFibSentenceValue]
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
    let mkSent := @mkFibSentence p _
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
    simp only [Set.mem_singleton_iff]
    intro s_eq
    simp only [s_eq, AllDependenciesChecked]
    intro h_dep
    rcases h_holds with ⟨ h_n_yielded, h_n_valid, h_s_n_yielded, h_s_n_valid ⟩
    obtain ⟨ k, h_assumptions ⟩ := h_assumptions
    specialize h_n_valid (by
      apply h_dep
      simp only [FibOrder, FibCanDepend, mkFibSentence, Sentence.eval, circuit_norm, mkFibSentenceValue]
      use k, k + 2
      aesop
    )
    specialize h_s_n_valid (by
      apply h_dep
      simp only [FibOrder, FibCanDepend, mkFibSentence, Sentence.eval, circuit_norm, mkFibSentenceValue]
      use k + 1, k + 2
      aesop
    )
    simp only [SentenceHolds, Sentence.eval, mkFibSentence, FibProperty] at h_n_valid h_s_n_valid ⊢
    obtain ⟨ n', h_n, h_n_valid ⟩ := h_n_valid
    obtain ⟨ s_n, h_s_n, h_s_n_valid ⟩ := h_s_n_valid
    simp only [Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] at h_n h_s_n h_n_valid h_s_n_valid
    simp only [circuit_norm] at h_n h_s_n
    exists (k + 2)
    simp only [Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, Nat.cast_add, Nat.cast_ofNat,
      List.getElem_cons_succ, circuit_norm, mkFibSentenceValue]
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
def computeFibUpTo4 : FormalCircuit (@FibOrder p _) unit unit where
  main := fun (_input : Var unit (F p)) => do
    -- Base yields Fib(0,1) and Fib(1,1)
    subcircuit FibBase.circuit ()

    -- Step with (0,1,1) yields Fib(2,2)
    subcircuit (FibStep.circuit 0 1 1) ()

    -- Step with (1,1,2) yields Fib(3,3)
    subcircuit (FibStep.circuit 1 1 2) ()

    -- Step with (2,2,3) yields Fib(4,5)
    subcircuit (FibStep.circuit 2 2 3) ()

    return ()

  localLength _ := 0

  yields _ _ _ :=
    -- Concrete set of all Fibonacci sentences from 0 to 4
    { mkFibSentenceValue 0 1,
      mkFibSentenceValue 1 1,
      mkFibSentenceValue 2 2,
      mkFibSentenceValue 3 3,
      mkFibSentenceValue 4 5 }

  yields_eq := by
    intros env input offset
    simp only [circuit_norm, ElaboratedCircuit.yields_eq]
    sorry -- Will implement this proof

  localLength_eq := by
    intro _
    simp only [Circuit.localLength, circuit_norm]
    aesop

  subcircuitsConsistent := by
    intro input offset
    simp only [circuit_norm, FibBase.circuit, FibStep.circuit]
    omega

  Assumptions _ := 4 < p

  CompletenessAssumptions _ _ := 4 < p

  completenessAssumptions_implies_assumptions _ _ h := h

  Spec _ _ _ := True

  soundness := by
    circuit_proof_start
    intro s hs h_dep
    -- The circuit yields the concrete set of Fibonacci values
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with (rfl | rfl | rfl | rfl | rfl)
    · -- Fib(0,1)
      simp only [SentenceHolds, mkFibSentenceValue, FibProperty, circuit_norm]
      use 0
      simp [fib]
    · -- Fib(1,1)
      simp only [SentenceHolds, mkFibSentenceValue, FibProperty, circuit_norm]
      use 1
      simp [fib]
    · -- Fib(2,2)
      simp only [SentenceHolds, mkFibSentenceValue, FibProperty, circuit_norm]
      use 2
      simp [fib]
      norm_num
    · -- Fib(3,3)
      simp only [SentenceHolds, mkFibSentenceValue, FibProperty, circuit_norm]
      use 3
      simp [fib]
      norm_num
    · -- Fib(4,5)
      simp only [SentenceHolds, mkFibSentenceValue, FibProperty, circuit_norm]
      use 4
      simp [fib]
      norm_num

  completeness := by
    circuit_proof_start
    obtain ⟨ h0, h1, h2, h3 ⟩ := h_env
    specialize h0 (by simp [FibBase.circuit])
    simp only [FibBase.circuit, mkFibSentenceValue] at h0
    specialize h1 (by
      simp only [FibStep.circuit, circuit_norm]
      and_intros
      · use 0
        simp [fib]; omega
      · simp only [Sentence.eval, mkFibSentence]
        aesop
      · simp only [circuit_norm, mkFibSentence, Sentence.eval]
        aesop
      )
    -- Need to satisfy the assumptions of each subcircuit
    and_intros
    · -- FibBase assumptions (True)
      trivial
    · -- FibStep (0,1,1) assumptions
      use 0
      simp only [fib]
      and_intros <;> norm_num
      omega
    · -- For the second use of FibBase yielded sentences
      sorry -- Will complete this
    · -- For the first use of FibStep yielded sentences
      sorry -- Will complete this
    · -- FibStep (1,1,2) assumptions
      use 1
      simp only [fib]
      and_intros <;> norm_num
      omega
    · -- For FibStep (1,1,2) yielded sentences
      sorry -- Will complete this
    · -- For FibStep (1,1,2) yielded sentences
      sorry -- Will complete this
    · -- FibStep (2,2,3) assumptions
      use 2
      simp only [fib]
      and_intros <;> norm_num
      omega
    · -- For FibStep (2,2,3) yielded sentences
      sorry -- Will complete this
    · -- For FibStep (2,2,3) yielded sentences
      sorry -- Will complete this

end Clean.Examples.FibonacciYield
