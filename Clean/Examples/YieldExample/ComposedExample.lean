import Clean.Examples.YieldExample.ByteRangeYielder
import Clean.Examples.YieldExample.U32NormalizedAssertion
import Clean.Circuit.Basic
import Clean.Types.U32
import Clean.Utils.Tactics

namespace Examples.YieldExample.ComposedExample

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/--
Main circuit that composes ByteRangeYielder and U32NormalizedAssertion.
First yields all bytes 0-255, then checks that the input U32 is normalized.
-/
def main (input : Var U32 (F p)) : Circuit (F p) Unit := do
  -- First yield all bytes 0-255
  ByteRangeYielder.circuit ()
  -- Then check the input is normalized using those yields
  U32NormalizedAssertion.circuit input

def elaborated : ElaboratedCircuit (F p) U32 unit where
  main
  localLength _ := 0
  localLength_eq := by
    intro _
    simp only [circuit_norm, main, ByteRangeYielder.circuit, ByteRangeYielder.elaborated, U32NormalizedAssertion.circuit, U32NormalizedAssertion.elaborated]
  yields input env offset :=
    ByteRangeYielder.elaborated.yields () env offset ∪
    U32NormalizedAssertion.elaborated.yields input env offset
  yields_eq := by
    intro input env offset
    simp [circuit_norm, main, ByteRangeYielder.circuit, ByteRangeYielder.elaborated, U32NormalizedAssertion.circuit, U32NormalizedAssertion.elaborated]
  subcircuitsConsistent := by
    simp [circuit_norm, main, ByteRangeYielder.circuit, ByteRangeYielder.elaborated, U32NormalizedAssertion.circuit, U32NormalizedAssertion.elaborated]

/--
Assumptions:
1. The input must be normalized (needed for completeness)
2. The global yielded set equals the local yields (needed for completeness)
-/
def Assumptions (input : U32 (F p)) (yielded : Set (NamedList (F p))) : Prop :=
  input.Normalized ∧
  ∀ env offset input_var, eval env input_var = input →
    yielded = elaborated.yields input_var env offset

/--
Spec: If the yielded set equals the localYields (preventing unsound entries),
then the input is normalized.
-/
def Spec (input : U32 (F p)) (yielded : Set (NamedList (F p)))
         (_ : unit (F p)) (localYields : Set (NamedList (F p))) : Prop :=
  yielded = localYields → input.Normalized

omit [Fact (p > 512)] in
/--
Helper lemma: ByteRangeYielder yields exactly the bytes 0-255
-/
lemma byteRangeYielder_yields_exactly (env : Environment (F p)) (offset : ℕ) :
    ByteRangeYielder.elaborated.yields () env offset =
    { nl | ∃ (n : Nat), n < 256 ∧ nl = NamedList.mk "byte" [(n : F p)] } := by
  simp [ByteRangeYielder.elaborated]

/--
Key lemma: If yielded equals the localYields from our composed circuit,
then U32NormalizedAssertion.Assumptions is satisfied.
-/
lemma yielded_equals_local_satisfies_assumptions
    (input : U32 (F p)) (env : Environment (F p)) (offset : ℕ)
    (input_var : Var U32 (F p)) :
  U32NormalizedAssertion.Assumptions input (elaborated.yields input_var env offset) := by
  simp only [elaborated, U32NormalizedAssertion.Assumptions]
  constructor
  · -- All values in yielded are < 256
    intro v hv
    simp only [U32NormalizedAssertion.elaborated] at hv
    cases hv with
    | inl h =>
      -- From ByteRangeYielder
      rw [byteRangeYielder_yields_exactly] at h
      obtain ⟨n, hn, h_eq⟩ := h
      injection h_eq with _ h_list
      injection h_list with h_v
      subst h_v
      rw [ZMod.val_cast_of_lt]
      · exact hn
      · -- n < p follows from n < 256 and p > 512
        have hp : p > 512 := Fact.out
        trans 256
        · exact hn
        · linarith [hp]
    | inr h =>
      -- From U32NormalizedAssertion (which yields nothing)
      simp at h
  · -- All bytes 0-255 are in yielded
    intro n hn
    left
    rw [byteRangeYielder_yields_exactly]
    use n, hn

theorem soundness : GeneralFormalCircuit.Soundness (F p) elaborated Spec := by
  circuit_proof_start
  -- After circuit_proof_start, we need to prove Spec input yielded output localYields
  intro h_yielded_eq
  -- We have h_holds which contains the constraints from both circuits
  obtain ⟨h_byte_range, h_normalized⟩ := h_holds
  -- h_yielded_eq tells us yielded = localYields (which is elaborated.yields)
  -- Since yielded = elaborated.yields, we know U32NormalizedAssertion.Assumptions holds
  have h_u32_assumptions : U32NormalizedAssertion.Assumptions input yielded := by
    rw [h_yielded_eq]
    exact yielded_equals_local_satisfies_assumptions input env i₀ input_var
  -- Apply h_normalized with the assumptions to get the spec
  exact h_normalized h_u32_assumptions

theorem completeness : GeneralFormalCircuit.Completeness (F p) elaborated Assumptions := by
  circuit_proof_start
  -- h_local_yields gives us elaborated.yields input_var env i₀ ⊆ yielded
  -- h_assumptions gives us input.Normalized and that yielded = elaborated.yields for matching inputs
  obtain ⟨h_normalized, h_yielded_eq⟩ := h_assumptions
  -- Apply h_yielded_eq to get that yielded = elaborated.yields input_var env i₀
  have h_eq := h_yielded_eq env i₀ input_var h_input
  -- Now we can proceed with the proof
  constructor
  · exact trivial  -- ByteRangeYielder.Assumptions is True
  specialize h_env trivial
  simp only [ByteRangeYielder.circuit, ByteRangeYielder.Spec] at h_env
  constructor
  · -- U32NormalizedAssertion.circuit.Assumptions
    simp only [U32NormalizedAssertion.circuit, U32NormalizedAssertion.Assumptions]
    constructor
    · -- All values in yielded are < 256
      intro v hv
      -- Since yielded = elaborated.yields by h_eq, and elaborated.yields is the union of
      -- ByteRangeYielder.yields (which only has bytes 0-255) and U32NormalizedAssertion.yields (which is empty),
      -- all values in yielded must be < 256
      simp only [h_eq, U32NormalizedAssertion.elaborated, ByteRangeYielder.elaborated] at hv
      cases hv with
      | inl h =>
        -- h says the NamedList is in ByteRangeYielder's yields, which are exactly bytes 0-255
        simp only [Set.mem_setOf_eq] at h
        obtain ⟨n, hn, h_eq⟩ := h
        injection h_eq with _ h_list
        injection h_list with h_v
        subst h_v
        rw [ZMod.val_cast_of_lt]
        · exact hn
        · have hp : p > 512 := Fact.out
          trans 256
          · exact hn
          · linarith [hp]
      | inr h =>
        simp at h
    · -- All bytes 0-255 are in yielded
      intro n hn
      -- Since yielded = elaborated.yields by h_eq, we just need to show the byte is in elaborated.yields
      rw [h_eq]
      left
      -- The byte is in ByteRangeYielder.elaborated.yields
      simp only [ByteRangeYielder.elaborated, Set.mem_setOf_eq]
      use n, hn
  · -- U32NormalizedAssertion.circuit.Spec
    -- This follows from h_normalized which says input.Normalized
    exact h_normalized

def circuit : GeneralFormalCircuit (F p) U32 unit where
  elaborated
  Assumptions
  Spec
  soundness
  completeness

end Examples.YieldExample.ComposedExample
