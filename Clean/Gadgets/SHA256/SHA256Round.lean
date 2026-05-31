import Clean.Gadgets.SHA256.Add32
import Clean.Gadgets.SHA256.AddMod32
import Clean.Gadgets.SHA256.Ch32
import Clean.Gadgets.SHA256.Maj32
import Clean.Gadgets.SHA256.UpperSigma0
import Clean.Gadgets.SHA256.UpperSigma1
import Clean.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime]

namespace Gadgets.SHA256

variable [Fact (p > 2^35)]

private instance fact_six_le_eight : Fact ((6 : ℕ) ≤ 8) := ⟨by norm_num⟩
private instance fact_seven_le_eight : Fact ((7 : ℕ) ≤ 8) := ⟨by norm_num⟩

/-!
# SHA-256 Round Function

Implements one round of the SHA-256 compression function at the bit level,
using only R1CS constraints (no lookup tables).

State convention: `Vector (Var (fields 32) (F p)) 8` holds [a, b, c, d, e, f, g, h],
where each word is a 32-bit vector with LSB at index 0.

Witness count per round:
  upperSigma1 = 32, ch32 = 32, upperSigma0 = 32, maj32 = 32,
  2 × addMod32 = 2 × 35 = 70
  Total: 32 + 32 + 32 + 32 + 70 = 198
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
  let sig1  ← subcircuit UpperSigma1.circuit e
  let ch    ← subcircuit Ch32.circuit ⟨e, f, g⟩
  let sig0  ← subcircuit UpperSigma0.circuit a
  let maj   ← subcircuit Maj32.circuit ⟨a, b, c⟩
  -- new_e = (d + h + Σ₁(e) + Ch + k + w) mod 2^32
  let new_e ← AddMod32.circuit (n := 6) #v[d, h, sig1, ch, k, w]
  -- new_a = (h + Σ₁(e) + Ch + k + w + Σ₀(a) + Maj) mod 2^32
  let new_a ← AddMod32.circuit (n := 7) #v[h, sig1, ch, k, w, sig0, maj]
  return #v[new_a, a, b, c, new_e, e, f, g]

namespace SHA256Round

structure Inputs (F : Type) where
  state : SHA256State F
  k : fields 32 F
  w : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) :=
  sha256Round input.state input.k input.w

instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State where
  main := main
  localLength _ := 198
  -- Explicit output: new_a/new_e are the output `z` vectors of the corresponding AddMod32
  -- subcircuits at their starting offsets; the other six positions are inputs passed through.
  -- Offsets are written additively (matching the subcircuit-length chain) so they unify
  -- cheaply with the constraint-derived terms in the soundness proof.
  output input i0 := #v[
    varFromOffset (fields 32) (i0 + 32 + 32 + 32 + 32 + 35),  -- new_a (offset 163)
    input.state[0], input.state[1], input.state[2],
    varFromOffset (fields 32) (i0 + 32 + 32 + 32 + 32),  -- new_e (offset 128)
    input.state[4], input.state[5], input.state[6]
  ]
  localLength_eq := by intro input offset; simp [circuit_norm, main, sha256Round, AddMod32.circuit, AddMod32.elaborated, UpperSigma0.circuit, UpperSigma1.circuit, Ch32.circuit, Maj32.circuit]
  output_eq := by
    intro input offset
    simp only [circuit_norm, main, sha256Round,
      AddMod32.circuit, AddMod32.elaborated, UpperSigma0.circuit, UpperSigma0.elaborated,
      UpperSigma1.circuit, UpperSigma1.elaborated, Ch32.circuit, Ch32.elaborated,
      Maj32.circuit, Maj32.elaborated]
  channelsLawful := by intro input offset; simp [circuit_norm, main, sha256Round, AddMod32.circuit, AddMod32.elaborated, UpperSigma0.circuit, UpperSigma1.circuit, Ch32.circuit, Maj32.circuit]

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧ Normalized input.k ∧ Normalized input.w

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.sha256Round (input.state.map valueBits) (valueBits input.k) (valueBits input.w)
  ∧ ∀ i : Fin 8, Normalized out[i]

/-! ## Flatten lemmas: nested binary `add32` ↔ a single multi-operand modular sum -/

/-- The inner 5-term nested `add32` chain is `ModEq` to the flat sum (`add32`-form). -/
private lemma chain5_modEq (h s1 ch k w : ℕ) :
    _root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 h s1) ch) k) w
      ≡ h + s1 + ch + k + w [MOD 2 ^ 32] := by
  unfold _root_.add32
  have e1 : (h + s1) % 2 ^ 32 ≡ h + s1 [MOD 2 ^ 32] := Nat.mod_modEq _ _
  have e2 : ((h + s1) % 2 ^ 32 + ch) % 2 ^ 32 ≡ h + s1 + ch [MOD 2 ^ 32] :=
    (Nat.mod_modEq _ _).trans (e1.add_right ch)
  have e3 : (((h + s1) % 2 ^ 32 + ch) % 2 ^ 32 + k) % 2 ^ 32 ≡ h + s1 + ch + k [MOD 2 ^ 32] :=
    (Nat.mod_modEq _ _).trans (e2.add_right k)
  exact (Nat.mod_modEq _ _).trans (e3.add_right w)

/-- new_e: opsValueSum of #v[d,h,Σ₁,Ch,k,w] reduces to the spec's nested add32. -/
private lemma newe_flatten (d h s1 ch k w : ℕ) :
    (d + h + s1 + ch + k + w) % 2 ^ 32
      = _root_.add32 d (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 h s1) ch) k) w) := by
  show (d + h + s1 + ch + k + w) % 2 ^ 32
      = (d + _root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 h s1) ch) k) w) % 2 ^ 32
  have key : d + h + s1 + ch + k + w
      ≡ d + _root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 h s1) ch) k) w [MOD 2 ^ 32] := by
    have hr : d + h + s1 + ch + k + w = d + (h + s1 + ch + k + w) := by ring
    rw [hr]
    exact Nat.ModEq.add_left d (chain5_modEq h s1 ch k w).symm
  exact key

/-- new_a: opsValueSum of #v[h,Σ₁,Ch,k,w,Σ₀,Maj] reduces to the spec's nested add32. -/
private lemma newa_flatten (h s1 ch k w s0 maj : ℕ) :
    (h + s1 + ch + k + w + s0 + maj) % 2 ^ 32
      = _root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 h s1) ch) k) w)
          (_root_.add32 s0 maj) := by
  show (h + s1 + ch + k + w + s0 + maj) % 2 ^ 32
      = (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 h s1) ch) k) w
          + _root_.add32 s0 maj) % 2 ^ 32
  have hR : _root_.add32 s0 maj ≡ s0 + maj [MOD 2 ^ 32] := Nat.mod_modEq _ _
  have key : h + s1 + ch + k + w + s0 + maj
      ≡ _root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 h s1) ch) k) w
          + _root_.add32 s0 maj [MOD 2 ^ 32] := by
    have hr : h + s1 + ch + k + w + s0 + maj = (h + s1 + ch + k + w) + (s0 + maj) := by ring
    rw [hr]
    exact Nat.ModEq.add (chain5_modEq h s1 ch k w).symm hR.symm
  exact key

/-! ## Helper lemmas to unfold the explicit n=6 / n=7 operand vectors -/

omit [Fact (p > 2 ^ 35)] in
/-- Elementwise evaluation of a 6-element variable vector. -/
private lemma eval_v6 (env : Environment (F p)) (a b c d e f : Var (fields 32) (F p)) :
    (eval env (#v[a, b, c, d, e, f] : Var (ProvableVector (fields 32) 6) (F p)) :
      ProvableVector (fields 32) 6 (F p)) =
      #v[Vector.map (Expression.eval env) a, Vector.map (Expression.eval env) b,
         Vector.map (Expression.eval env) c, Vector.map (Expression.eval env) d,
         Vector.map (Expression.eval env) e, Vector.map (Expression.eval env) f] := by
  rw [eval_vector]
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
    · rename_i hi
      simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      exact (ProvableType.getElem_eval_fields env _ _ hi).symm

omit [Fact (p > 2 ^ 35)] in
/-- Elementwise evaluation of a 7-element variable vector. -/
private lemma eval_v7 (env : Environment (F p)) (a b c d e f g : Var (fields 32) (F p)) :
    (eval env (#v[a, b, c, d, e, f, g] : Var (ProvableVector (fields 32) 7) (F p)) :
      ProvableVector (fields 32) 7 (F p)) =
      #v[Vector.map (Expression.eval env) a, Vector.map (Expression.eval env) b,
         Vector.map (Expression.eval env) c, Vector.map (Expression.eval env) d,
         Vector.map (Expression.eval env) e, Vector.map (Expression.eval env) f,
         Vector.map (Expression.eval env) g] := by
  rw [eval_vector]
  ext j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · rename_i hi
      simp only [Vector.getElem_map, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      exact (ProvableType.getElem_eval_fields env _ _ hi).symm

omit [Fact (p > 2 ^ 35)] in
/-- `AddMod32.Assumptions` of a 6-operand vector unfolds to six `Normalized` facts. -/
private lemma addMod32_assum6_iff (env : Environment (F p))
    (a b c d e f : Var (fields 32) (F p)) :
    (∀ j : Fin 6, Normalized ((eval env (#v[a, b, c, d, e, f] :
        Var (ProvableVector (fields 32) 6) (F p)) :
        ProvableVector (fields 32) 6 (F p))[j])) ↔
      Normalized (Vector.map (Expression.eval env) a) ∧
      Normalized (Vector.map (Expression.eval env) b) ∧
      Normalized (Vector.map (Expression.eval env) c) ∧
      Normalized (Vector.map (Expression.eval env) d) ∧
      Normalized (Vector.map (Expression.eval env) e) ∧
      Normalized (Vector.map (Expression.eval env) f) := by
  rw [eval_v6]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5⟩
  · rintro ⟨ha, hb, hc, hd, he, hf⟩ j
    fin_cases j <;> assumption

omit [Fact (p > 2 ^ 35)] in
/-- `AddMod32.Assumptions` of a 7-operand vector unfolds to seven `Normalized` facts. -/
private lemma addMod32_assum7_iff (env : Environment (F p))
    (a b c d e f g : Var (fields 32) (F p)) :
    (∀ j : Fin 7, Normalized ((eval env (#v[a, b, c, d, e, f, g] :
        Var (ProvableVector (fields 32) 7) (F p)) :
        ProvableVector (fields 32) 7 (F p))[j])) ↔
      Normalized (Vector.map (Expression.eval env) a) ∧
      Normalized (Vector.map (Expression.eval env) b) ∧
      Normalized (Vector.map (Expression.eval env) c) ∧
      Normalized (Vector.map (Expression.eval env) d) ∧
      Normalized (Vector.map (Expression.eval env) e) ∧
      Normalized (Vector.map (Expression.eval env) f) ∧
      Normalized (Vector.map (Expression.eval env) g) := by
  rw [eval_v7]
  constructor
  · intro h
    exact ⟨h 0, h 1, h 2, h 3, h 4, h 5, h 6⟩
  · rintro ⟨ha, hb, hc, hd, he, hf, hg⟩ j
    fin_cases j <;> assumption

omit [Fact (p > 2 ^ 35)] in
/-- `opsValueSum` of a 6-operand vector expands to six `valueBits` summands. -/
private lemma addMod32_opsValueSum6 (env : Environment (F p))
    (a b c d e f : Var (fields 32) (F p)) :
    opsValueSum (eval env (#v[a, b, c, d, e, f] :
        Var (ProvableVector (fields 32) 6) (F p)) :
        ProvableVector (fields 32) 6 (F p)) =
      valueBits (Vector.map (Expression.eval env) a) +
      valueBits (Vector.map (Expression.eval env) b) +
      valueBits (Vector.map (Expression.eval env) c) +
      valueBits (Vector.map (Expression.eval env) d) +
      valueBits (Vector.map (Expression.eval env) e) +
      valueBits (Vector.map (Expression.eval env) f) := by
  unfold opsValueSum
  rw [eval_v6, Fin.sum_univ_six]
  norm_num [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]

omit [Fact (p > 2 ^ 35)] in
/-- `opsValueSum` of a 7-operand vector expands to seven `valueBits` summands. -/
private lemma addMod32_opsValueSum7 (env : Environment (F p))
    (a b c d e f g : Var (fields 32) (F p)) :
    opsValueSum (eval env (#v[a, b, c, d, e, f, g] :
        Var (ProvableVector (fields 32) 7) (F p)) :
        ProvableVector (fields 32) 7 (F p)) =
      valueBits (Vector.map (Expression.eval env) a) +
      valueBits (Vector.map (Expression.eval env) b) +
      valueBits (Vector.map (Expression.eval env) c) +
      valueBits (Vector.map (Expression.eval env) d) +
      valueBits (Vector.map (Expression.eval env) e) +
      valueBits (Vector.map (Expression.eval env) f) +
      valueBits (Vector.map (Expression.eval env) g) := by
  unfold opsValueSum
  rw [eval_v7, Fin.sum_univ_seven]
  norm_num [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]

omit [Fact (p > 2 ^ 35)] in
/-- The eight output positions are normalized: pass-throughs come from `hnd` (the input-state
    words, in mapped form), `new_a`/`new_e` from the two `AddMod32` outputs. Factored out as
    its own declaration so the `fin_cases` over the (large) output vector gets a fresh
    heartbeat budget, keeping the main soundness proof within the limit. -/
private lemma output_normalized (i₀ : ℕ) (env : Environment (F p))
    (state_var : SHA256State (Expression (F p)))
    (hnd : ∀ (i : ℕ) (hi : i < 8),
      Normalized (Vector.map (Expression.eval env) (state_var[i]'hi)))
    (n_newa : Normalized (Vector.map (Expression.eval env)
      (varFromOffset (fields 32) (i₀ + 32 + 32 + 32 + 32 + 35))))
    (n_newe : Normalized (Vector.map (Expression.eval env)
      (varFromOffset (fields 32) (i₀ + 32 + 32 + 32 + 32)))) :
    ∀ i : Fin 8, Normalized (eval env
      (#v[varFromOffset (fields 32) (i₀ + 32 + 32 + 32 + 32 + 35),
        state_var[0], state_var[1], state_var[2],
        varFromOffset (fields 32) (i₀ + 32 + 32 + 32 + 32),
        state_var[4], state_var[5], state_var[6]] :
        Var SHA256State (F p)))[i] := by
  intro i
  fin_cases i <;>
    simp only [Fin.getElem_fin, eval_vector, Vector.getElem_map, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] <;>
    rw [CircuitType.eval_var_fields]
  · exact n_newa
  · exact hnd 0 (by omega)
  · exact hnd 1 (by omega)
  · exact hnd 2 (by omega)
  · exact n_newe
  · exact hnd 4 (by omega)
  · exact hnd 5 (by omega)
  · exact hnd 6 (by omega)

theorem soundness : Soundness (F p) elaborated Assumptions Spec := by
  circuit_proof_start [sha256Round, UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit]
  obtain ⟨h_state_norm, h_k_norm, h_w_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_k, h_input_w⟩ := h_input
  have h_eval (i : ℕ) (hi : i < 8) :
      Vector.map (Expression.eval env) (input_var_state[i]'hi) = input_state[i]'hi := by
    have h := getElem_eval_vector env input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env (input_var_state[i]'hi)]
    exact h
  -- Normalized facts in the mapped (`Vector.map eval`) form the subcircuit specs expect.
  have hnd (i : ℕ) (hi : i < 8) :
      Normalized (Vector.map (Expression.eval env) (input_var_state[i]'hi)) := by
    rw [h_eval i hi]; exact h_state_norm ⟨i, hi⟩
  have n_k : Normalized (Vector.map (Expression.eval env) input_var_k) := by
    rw [h_input_k]; exact h_k_norm
  have n_w : Normalized (Vector.map (Expression.eval env) input_var_w) := by
    rw [h_input_w]; exact h_w_norm
  -- Split the round's constraints into the six subcircuit obligations, unfolding the four cheap
  -- subcircuits and supplying their assumptions (`hnd` gives each input word as normalized).
  obtain ⟨c_sig1, c_ch, c_sig0, c_maj, c_newe, c_newa⟩ := h_holds
  simp only [UpperSigma1.Assumptions, UpperSigma1.Spec] at c_sig1
  have s_sig1 := c_sig1 (hnd 4 (by omega)); clear c_sig1
  simp only [Ch32.Assumptions, Ch32.Spec, and_imp] at c_ch
  have s_ch := c_ch (hnd 4 (by omega)) (hnd 5 (by omega)) (hnd 6 (by omega)); clear c_ch
  simp only [UpperSigma0.Assumptions, UpperSigma0.Spec] at c_sig0
  have s_sig0 := c_sig0 (hnd 0 (by omega)); clear c_sig0
  simp only [Maj32.Assumptions, Maj32.Spec, and_imp] at c_maj
  have s_maj := c_maj (hnd 0 (by omega)) (hnd 1 (by omega)) (hnd 2 (by omega)); clear c_maj
  simp only [AddMod32.circuit, AddMod32.Assumptions, AddMod32.Spec, addMod32_assum6_iff] at c_newe
  obtain ⟨v_newe, n_newe⟩ :=
    c_newe ⟨hnd 3 (by omega), hnd 7 (by omega), s_sig1.2, s_ch.2, n_k, n_w⟩
  clear c_newe
  simp only [AddMod32.circuit, AddMod32.Assumptions, AddMod32.Spec, addMod32_assum7_iff] at c_newa
  obtain ⟨v_newa, n_newa⟩ :=
    c_newa ⟨hnd 7 (by omega), s_sig1.2, s_ch.2, n_k, n_w, s_sig0.2, s_maj.2⟩
  clear c_newa
  rw [addMod32_opsValueSum6] at v_newe
  rw [addMod32_opsValueSum7] at v_newa
  -- Reduce the AddMod32 outputs (`ElaboratedCircuit.output`) to the `varFromOffset`/`mapRange`
  -- form used by the explicit `output` field, so the `v_newa`/`v_newe` rewrites unify below.
  simp only [circuit_norm] at v_newe v_newa
  refine ⟨⟨?_, ?_⟩, Or.inl rfl, Or.inl rfl⟩
  · clear n_newe n_newa
    rw [newe_flatten] at v_newe
    rw [newa_flatten] at v_newa
    rw [s_sig1.1, s_ch.1] at v_newe
    rw [s_sig1.1, s_ch.1, s_sig0.1, s_maj.1] at v_newa
    clear s_sig1 s_ch s_sig0 s_maj
    -- Move all operand values to the spec's `valueBits input_*` form.
    have ek : valueBits (Vector.map (Expression.eval env) input_var_k) = valueBits input_k :=
      congrArg valueBits h_input_k
    have ew : valueBits (Vector.map (Expression.eval env) input_var_w) = valueBits input_w :=
      congrArg valueBits h_input_w
    have e (i : ℕ) (hi : i < 8) :
        valueBits (Vector.map (Expression.eval env) input_var_state[i]) = valueBits input_state[i] :=
      congrArg valueBits (h_eval i hi)
    simp only [ek, ew, e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega),
      e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega)] at v_newe v_newa
    simp only [eval_vector, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil,
      circuit_norm]
    simp only [Specs.SHA256.sha256Round, Vector.getElem_map,
      e 0 (by omega), e 1 (by omega), e 2 (by omega),
      e 4 (by omega), e 5 (by omega), e 6 (by omega), v_newa, v_newe]
  · -- Normalized for each output position, via the factored-out lemma (own heartbeat budget).
    exact output_normalized i₀ env input_var_state hnd n_newa n_newe

theorem completeness : Completeness (F p) elaborated Assumptions := by
  circuit_proof_start [sha256Round, UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit]
  obtain ⟨h_state_norm, h_k_norm, h_w_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_k, h_input_w⟩ := h_input
  have h_eval (i : ℕ) (hi : i < 8) :
      Vector.map (Expression.eval env.toEnvironment) (input_var_state[i]'hi) = input_state[i]'hi := by
    have h := getElem_eval_vector env.toEnvironment input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env.toEnvironment (input_var_state[i]'hi)]
    exact h
  have hnd (i : ℕ) (hi : i < 8) :
      Normalized (Vector.map (Expression.eval env.toEnvironment) (input_var_state[i]'hi)) := by
    rw [h_eval i hi]; exact h_state_norm ⟨i, hi⟩
  have n_k : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_k) := by
    rw [h_input_k]; exact h_k_norm
  have n_w : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_w) := by
    rw [h_input_w]; exact h_w_norm
  -- Extract the (Σ₁/Ch/Σ₀/Maj) normalized outputs from the prover constraints.
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions,
    Ch32.Assumptions, Maj32.Assumptions, UpperSigma1.Spec, UpperSigma0.Spec,
    Ch32.Spec, Maj32.Spec, and_imp] at h_env
  obtain ⟨e_sig1, e_ch, e_sig0, e_maj, -, -⟩ := h_env
  obtain ⟨_, n_sig1⟩ := e_sig1 (hnd 4 (by omega))
  obtain ⟨_, n_ch⟩ := e_ch (hnd 4 (by omega)) (hnd 5 (by omega)) (hnd 6 (by omega))
  obtain ⟨_, n_sig0⟩ := e_sig0 (hnd 0 (by omega))
  obtain ⟨_, n_maj⟩ := e_maj (hnd 0 (by omega)) (hnd 1 (by omega)) (hnd 2 (by omega))
  -- Provide the assumptions each subcircuit needs (state words / k / w / subcircuit outputs).
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions,
    Ch32.Assumptions, Maj32.Assumptions, AddMod32.circuit, AddMod32.Assumptions,
    addMod32_assum6_iff, addMod32_assum7_iff]
  exact ⟨hnd 4 (by omega),
    ⟨hnd 4 (by omega), hnd 5 (by omega), hnd 6 (by omega)⟩,
    hnd 0 (by omega),
    ⟨hnd 0 (by omega), hnd 1 (by omega), hnd 2 (by omega)⟩,
    ⟨hnd 3 (by omega), hnd 7 (by omega), n_sig1, n_ch, n_k, n_w⟩,
    ⟨hnd 7 (by omega), n_sig1, n_ch, n_k, n_w, n_sig0, n_maj⟩⟩

def circuit : FormalCircuit (F p) Inputs SHA256State where
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

end SHA256Round
end Gadgets.SHA256
end
