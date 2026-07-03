import Clean.Gadgets.SHA256.Add32
import Clean.Gadgets.SHA256.Ch32
import Clean.Gadgets.SHA256.Maj32
import Clean.Gadgets.SHA256.UpperSigma0
import Clean.Gadgets.SHA256.UpperSigma1
import Clean.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.SHA256

variable [Fact (p > 2^33)]

/-!
# SHA-256 Round Function

Implements one round of the SHA-256 compression function at the bit level,
using only R1CS constraints (no lookup tables).

State convention: `Vector (Var (fields 32) (F p)) 8` holds [a, b, c, d, e, f, g, h],
where each word is a 32-bit vector with LSB at index 0.

Witness count per round:
  upperSigma1 = 64, ch32 = 32, 4×add32 = 4×33 = 132 for t1 chain
  upperSigma0 = 64, maj32 = 64, add32 = 33 for t2
  2×add32 = 2×33 = 66 for new_a, new_e
  Total: 64 + 32 + 132 + 64 + 64 + 33 + 66 = 455
-/

/-- One round of SHA-256 compression.

    state = [a, b, c, d, e, f, g, h], each a 32-bit word (fields 32).
    k: round constant as a 32-bit word.
    w: message schedule word as a 32-bit word.
-/

def sha256Round
    (state : Vector (Var (fields 32) (F p)) 8)
    (k w : Var (fields 32) (F p))
    : Circuit (F p) (Vector (Var (fields 32) (F p)) 8) := do
  let a := state[0]; let b := state[1]; let c := state[2]; let d := state[3]
  let e := state[4]; let f := state[5]; let g := state[6]; let h := state[7]
  -- t1 = h + Σ₁(e) + Ch(e,f,g) + k + w
  let sig1  ← UpperSigma1.circuit e
  let ch    ← Ch32.circuit ⟨e, f, g⟩
  let t1_0  ← Add32.circuit ⟨h, sig1⟩
  let t1_1  ← Add32.circuit ⟨t1_0, ch⟩
  let t1_2  ← Add32.circuit ⟨t1_1, k⟩
  let t1    ← Add32.circuit ⟨t1_2, w⟩
  -- t2 = Σ₀(a) + Maj(a,b,c)
  let sig0  ← UpperSigma0.circuit a
  let maj   ← Maj32.circuit ⟨a, b, c⟩
  let t2    ← Add32.circuit ⟨sig0, maj⟩
  -- new state
  let new_a ← Add32.circuit ⟨t1, t2⟩
  let new_e ← Add32.circuit ⟨d, t1⟩
  return #v[new_a, a, b, c, new_e, e, f, g]

namespace SHA256Round

structure Inputs (F : Type) where
  state : SHA256State F
  k : fields 32 F
  w : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) :=
  sha256Round input.state input.k input.w

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧ Normalized input.k ∧ Normalized input.w

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.sha256Round (input.state.map valueBits) (valueBits input.k) (valueBits input.w)
  ∧ ∀ i : Fin 8, Normalized out[i]

instance elaborated : ElaboratedCircuit (F p) _ _ main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [sha256Round, UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit, Add32.circuit]
  obtain ⟨h_state_norm, h_k_norm, h_w_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_k, h_input_w⟩ := h_input
  have h_eval (i : ℕ) (hi : i < 8) :
      Vector.map (Expression.eval env) (input_var_state[i]'hi) = input_state[i]'hi := by
    have h := getElem_eval_vector env input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env (input_var_state[i]'hi)]
    exact h
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions,
    Ch32.Assumptions, Maj32.Assumptions, Add32.Assumptions,
    UpperSigma1.Spec, UpperSigma0.Spec,
    Ch32.Spec, Maj32.Spec, Add32.Spec, h_eval, and_imp] at h_holds
  obtain ⟨c_sig1, c_ch, c_t10, c_t11, c_t12, c_t1, c_sig0, c_maj, c_t2, c_newa, c_newe⟩ := h_holds
  have h_a : Normalized input_state[0] := h_state_norm 0
  have h_b : Normalized input_state[1] := h_state_norm 1
  have h_c : Normalized input_state[2] := h_state_norm 2
  have h_d : Normalized input_state[3] := h_state_norm 3
  have h_e : Normalized input_state[4] := h_state_norm 4
  have h_f : Normalized input_state[5] := h_state_norm 5
  have h_g : Normalized input_state[6] := h_state_norm 6
  have h_h : Normalized input_state[7] := h_state_norm 7
  -- Chain the spec applications.
  have s_sig1 := c_sig1 h_e; clear c_sig1
  have s_ch := c_ch h_e h_f h_g; clear c_ch
  have s_t10 := c_t10 h_h s_sig1.2; clear c_t10
  have s_t11 := c_t11 s_t10.2 s_ch.2; clear c_t11
  have s_t12 := c_t12 s_t11.2 h_k_norm; clear c_t12
  have s_t1 := c_t1 s_t12.2 h_w_norm; clear c_t1
  have s_sig0 := c_sig0 h_a; clear c_sig0
  have s_maj := c_maj h_a h_b h_c; clear c_maj
  have s_t2 := c_t2 s_sig0.2 s_maj.2; clear c_t2
  have s_newa := c_newa s_t1.2 s_t2.2; clear c_newa
  have s_newe := c_newe h_d s_t1.2; clear c_newe
  refine ⟨?_, ?_⟩
  · -- Vector equality: out.map valueBits = sha256Round-spec
    -- Compose the eight element-wise equations: v_newa / v_newe from the Add32 subcircuits
    -- (after chaining in the upstream values) and h_eval for the pass-through positions.
    have v_newa := s_newa.1
    have v_newe := s_newe.1
    rw [s_t1.1, s_t12.1, s_t11.1, s_t10.1, s_sig1.1, s_ch.1, s_t2.1, s_sig0.1, s_maj.1] at v_newa
    rw [s_t1.1, s_t12.1, s_t11.1, s_t10.1, s_sig1.1, s_ch.1] at v_newe
    clear s_sig1 s_ch s_t10 s_t11 s_t12 s_t1 s_sig0 s_maj s_t2 s_newa s_newe
    have e (i : ℕ) (hi : i < 8) :
        valueBits (Vector.map (Expression.eval env) input_var_state[i]) = valueBits input_state[i] :=
      congrArg valueBits (h_eval i hi)
    -- Reduce `(a + b) % 2^32` to `_root_.add32 a b` in v_newa/v_newe so they match the spec literal.
    simp only [show ∀ a b : ℕ, (a + b) % 2 ^ 32 = _root_.add32 a b from fun _ _ => rfl] at v_newa v_newe
    -- Push the outer `Vector.map valueBits ∘ eval env` inside the literal #v[...] and unfold the
    -- spec, so both sides become explicit 8-element vectors with matching slot shapes.
    simp only [eval_vector, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      circuit_norm]
    simp only [Specs.SHA256.sha256Round, Vector.getElem_map]
    rw [v_newa, v_newe, e 0 (by omega), e 1 (by omega), e 2 (by omega),
      e 4 (by omega), e 5 (by omega), e 6 (by omega)]
  · -- Normalized for each position
    intro i
    fin_cases i
    · convert s_newa.2 using 1
      rw [← getElem_eval_vector, CircuitType.eval_var_fields]; congr 1
    · convert (h_eval 0 (by omega)).symm ▸ h_a using 1
      rw [← getElem_eval_vector, CircuitType.eval_var_fields]; congr 1
    · convert (h_eval 1 (by omega)).symm ▸ h_b using 1
      rw [← getElem_eval_vector, CircuitType.eval_var_fields]; congr 1
    · convert (h_eval 2 (by omega)).symm ▸ h_c using 1
      rw [← getElem_eval_vector, CircuitType.eval_var_fields]; congr 1
    · convert s_newe.2 using 1
      rw [← getElem_eval_vector, CircuitType.eval_var_fields]; congr 1
    · convert (h_eval 4 (by omega)).symm ▸ h_e using 1
      rw [← getElem_eval_vector, CircuitType.eval_var_fields]; congr 1
    · convert (h_eval 5 (by omega)).symm ▸ h_f using 1
      rw [← getElem_eval_vector, CircuitType.eval_var_fields]; congr 1
    · convert (h_eval 6 (by omega)).symm ▸ h_g using 1
      rw [← getElem_eval_vector, CircuitType.eval_var_fields]; congr 1

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [sha256Round, UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit, Add32.circuit]
  obtain ⟨h_state_norm, h_k_norm, h_w_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_k, h_input_w⟩ := h_input
  have h_eval (i : ℕ) (hi : i < 8) :
      Vector.map (Expression.eval env.toEnvironment) (input_var_state[i]'hi) = input_state[i]'hi := by
    have h := getElem_eval_vector env.toEnvironment input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env.toEnvironment (input_var_state[i]'hi)]
    exact h
  have h_a := h_state_norm 0; have h_b := h_state_norm 1
  have h_c := h_state_norm 2; have h_d := h_state_norm 3
  have h_e := h_state_norm 4; have h_f := h_state_norm 5
  have h_g := h_state_norm 6; have h_h := h_state_norm 7
  -- Spec implications for the subcircuits (after circuit_norm) come paired with
  -- the assumptions we must supply.
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions,
    Ch32.Assumptions, Maj32.Assumptions, Add32.Assumptions,
    UpperSigma1.Spec, UpperSigma0.Spec,
    Ch32.Spec, Maj32.Spec, Add32.Spec, and_imp] at h_env ⊢
  obtain ⟨e_sig1, e_ch, e_t10, e_t11, e_t12, e_t1, e_sig0, e_maj, e_t2, e_newa, e_newe⟩ := h_env
  rw [h_eval 4 (by omega)] at e_sig1
  obtain ⟨v_sig1, n_sig1⟩ := e_sig1 h_e
  rw [h_eval 4 (by omega), h_eval 5 (by omega), h_eval 6 (by omega)] at e_ch
  obtain ⟨v_ch, n_ch⟩ := e_ch h_e h_f h_g
  rw [h_eval 7 (by omega)] at e_t10
  obtain ⟨v_t10, n_t10⟩ := e_t10 h_h n_sig1
  obtain ⟨v_t11, n_t11⟩ := e_t11 n_t10 n_ch
  obtain ⟨v_t12, n_t12⟩ := e_t12 n_t11 h_k_norm
  obtain ⟨_, n_t1⟩ := e_t1 n_t12 h_w_norm
  rw [h_eval 0 (by omega)] at e_sig0
  obtain ⟨v_sig0, n_sig0⟩ := e_sig0 h_a
  rw [h_eval 0 (by omega), h_eval 1 (by omega), h_eval 2 (by omega)] at e_maj
  obtain ⟨_, n_maj⟩ := e_maj h_a h_b h_c
  -- Goal: the chain of assumptions for the subcircuits
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_eval 4 (by omega)]; exact h_e
  · rw [h_eval 4 (by omega), h_eval 5 (by omega), h_eval 6 (by omega)]; exact ⟨h_e, h_f, h_g⟩
  · rw [h_eval 7 (by omega)]; exact ⟨h_h, n_sig1⟩
  · exact ⟨n_t10, n_ch⟩
  · exact ⟨n_t11, h_k_norm⟩
  · exact ⟨n_t12, h_w_norm⟩
  · rw [h_eval 0 (by omega)]; exact h_a
  · rw [h_eval 0 (by omega), h_eval 1 (by omega), h_eval 2 (by omega)]; exact ⟨h_a, h_b, h_c⟩
  · exact ⟨n_sig0, n_maj⟩
  · exact ⟨n_t1, by simp_all⟩
  · rw [h_eval 3 (by omega)]; exact ⟨h_d, n_t1⟩

def circuit : FormalCircuit (F p) Inputs SHA256State where
  main; elaborated; Assumptions; Spec; soundness; completeness

end SHA256Round
end Gadgets.SHA256
end
