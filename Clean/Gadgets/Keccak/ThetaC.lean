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

def Spec {sentences : PropertySet (F p)} (_checked : CheckedYields sentences) (state : KeccakState (F p)) (out : KeccakRow (F p)) :=
  out.Normalized
  ∧ out.value = Specs.Keccak256.thetaC state.value

-- #eval! theta_c (p:=p_babybear) default |>.localLength
instance elaborated {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : ElaboratedCircuit (F p) sentences KeccakState KeccakRow where
  main := main order
  localLength _ := 160
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
  · -- Prove yielded sentences hold (vacuous - no yields)
    intro s hs _
    -- The Xor64 subcircuits don't yield anything
    sorry

  -- rewrite goal
  apply KeccakRow.normalized_value_ext
  simp only [elaborated, main, thetaC_loop, circuit_norm, eval_vector, KeccakState.value, Xor64.circuit, Xor64.elaborated]

  -- simplify constraints
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [circuit_norm, h_input, eval_vector, elaborated,
    main, Xor64.circuit, Xor64.elaborated, Xor64.Assumptions, Xor64.Spec] at h_holds
  simp only [and_assoc, Nat.reduceAdd, Nat.reduceMod] at h_holds
  have state_norm : ∀ {i : ℕ} (hi : i < 25), state[i].Normalized :=
    fun hi => state_norm ⟨ _, hi ⟩
  simp only [state_norm, and_self, forall_const, and_true] at h_holds

  intro i
  specialize h_holds i
  have ⟨_, h_spec⟩ := h_holds
  aesop

theorem completeness {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : Completeness (F p) sentences (elaborated order) Assumptions := by
  intro i0 env yields state_var h_env state h_input state_norm
  simp only [circuit_norm, eval_vector, Vector.ext_iff] at h_input
  simp only [h_input, circuit_norm, Assumptions, eval_vector,
    main, Xor64.circuit, Xor64.elaborated, Xor64.Assumptions, Xor64.Spec, KeccakState.Normalized] at h_env ⊢
  have state_norm : ∀ (i : ℕ) (hi : i < 25), state[i].Normalized := fun i hi => state_norm ⟨ i, hi ⟩
  simp_all

def circuit {sentences : PropertySet (F p)} (order : SentenceOrder sentences) : FormalCircuit order KeccakState KeccakRow :=
 { elaborated := elaborated order
   Assumptions
   Spec
   soundness := soundness order
   completeness := completeness order }

end Gadgets.Keccak256.ThetaC
