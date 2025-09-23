import Clean.Circuit.Loops
import Clean.Gadgets.Addition8.Addition8FullCarry
import Clean.Types.U64
import Clean.Gadgets.Addition32.Theorems
import Clean.Gadgets.Xor.Xor64
import Clean.Gadgets.Keccak.KeccakState
import Clean.Specs.Keccak256

namespace Gadgets.Keccak256.ThetaC
variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

def main {sentences : PropertySet (F p)} (order : SentenceOrder sentences) (state : Var KeccakState (F p)) : Circuit sentences (Var KeccakRow (F p)) :=
  .mapFinRange 5 fun i => do
    let c ← Xor64.circuit order ⟨state[5*i.val], state[5*i.val + 1]⟩
    let c ← Xor64.circuit order ⟨c, state[5*i.val + 2]⟩
    let c ← Xor64.circuit order ⟨c, state[5*i.val + 3]⟩
    let c ← Xor64.circuit order ⟨c, state[5*i.val + 4]⟩
    return c

def Assumptions (state : KeccakState (F p)) := state.Normalized

def CompletenessAssumptions {sentences : PropertySet (F p)} (yields : YieldContext sentences) (state : KeccakState (F p)) := state.Normalized

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (state : KeccakState (F p)) (out : KeccakRow (F p)) :=
  out.Normalized
  ∧ out.value = Specs.Keccak256.thetaC state.value

-- #eval! theta_c (p:=p_babybear) default |>.localLength
instance elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences KeccakState KeccakRow where
  main := main order
  localLength _ := 160
  yields _ _ _ := ∅
  yields_eq := by
    intro env input offset
    simp only [main, circuit_norm, Circuit.mapFinRange.localYields]
    simp only [Set.iUnion_eq_empty]
    intro i
    simp only [ElaboratedCircuit.yields_eq]
    simp [Xor64.circuit, Xor64.elaborated]
  localLength_eq _ _ := by simp only [main, circuit_norm, Xor64.circuit, Xor64.elaborated]
  subcircuitsConsistent _ _ := by simp only [main, circuit_norm]; intro; and_intros <;> ac_rfl

-- rewrite thetaC as a loop
lemma thetaC_loop (state : Vector ℕ 25) :
    Specs.Keccak256.thetaC state = .mapFinRange 5 fun i =>
      state[5*i.val] ^^^ state[5*i.val + 1] ^^^ state[5*i.val + 2] ^^^ state[5*i.val + 3] ^^^ state[5*i.val + 4] := by
  rw [Specs.Keccak256.thetaC, Vector.mapFinRange, Vector.finRange, Vector.map_mk, Vector.eq_mk, List.map_toArray]
  rfl

theorem soundness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Soundness (F p) (elaborated order) order Assumptions Spec := by
  intro i0 env yields checked state_var state h_input state_norm h_holds

  constructor
  · -- Prove yielded sentences hold (vacuous - yields is empty)
    simp [elaborated]

  -- rewrite goal
  apply KeccakRow.normalized_value_ext
  simp only [main, thetaC_loop, circuit_norm, eval_vector, KeccakState.value, Xor64.circuit,
    Xor64.elaborated]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [circuit_norm, h_input, main, Xor64.circuit, Xor64.elaborated, Xor64.Assumptions,
    Xor64.Spec] at h_holds
  simp only [Nat.reduceAdd] at h_holds
  have state_norm : ∀ {i : ℕ} (hi : i < 25), state[i].Normalized :=
    fun hi => state_norm ⟨ _, hi ⟩
  simp only [state_norm, and_self, forall_const, and_true] at h_holds

  intro i
  specialize h_holds i
  have ⟨_, h_spec⟩ := h_holds
  aesop

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Completeness (F p) sentences (elaborated order) CompletenessAssumptions := by
  intro i0 env yields state_var h_env state h_input state_norm
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [h_input, circuit_norm, main, Xor64.circuit, Xor64.elaborated,
    Xor64.CompletenessAssumptions, Xor64.Assumptions, Xor64.Spec] at h_env ⊢
  have state_norm : ∀ (i : ℕ) (hi : i < 25), state[i].Normalized := fun i hi => state_norm ⟨ i, hi ⟩
  simp_all

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order KeccakState KeccakRow :=
 { elaborated := elaborated order
   Assumptions
   CompletenessAssumptions
   Spec
   soundness := soundness order
   completeness := completeness order
   completenessAssumptions_implies_assumptions := fun _ _ h => h }

end Gadgets.Keccak256.ThetaC
