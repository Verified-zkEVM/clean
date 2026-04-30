import Clean.Circomlib.Poseidon

namespace Circomlib.Poseidon
namespace Poseidon1

open Specs.Poseidon (BN254_PRIME C_t2 M_t2)
open Specs.PoseidonOptimized (P_t2 S_t2)
open Circuit

-- Bridge lemmas: state the localLength in the `subcircuit` form that simp can match
-- after `foldl.localLength_eq` beta-reduces `(body default default)` via CoeFun.
private lemma fullRound_body_localLength
    (st : Vector (Expression (F BN254_PRIME)) 2) (c0 c1 : F BN254_PRIME) (n : ℕ) :
    (subcircuit (FullRound_t2.circuit c0 c1 m00 m01 m10 m11) st).localLength n = 10 :=
  fullRound_constLen.localLength_eq (st, (c0, c1)) n

private lemma partialRound_body_localLength
    (st : Vector (Expression (F BN254_PRIME)) 2) (c0 s0 s1 s2 : F BN254_PRIME) (n : ℕ) :
    (subcircuit (PartialRoundOpt_t2.circuit c0 s0 s1 s2) st).localLength n = 6 :=
  partialRound_constLen.localLength_eq (st, (c0, s0, s1, s2)) n

private lemma fullRound_body_subcircuitsConsistent
    (st : Vector (Expression (F BN254_PRIME)) 2) (c0 c1 : F BN254_PRIME) (n : ℕ) :
    ((subcircuit (FullRound_t2.circuit c0 c1 m00 m01 m10 m11) st).operations n).SubcircuitsConsistent n := by
  simp only [Operations.SubcircuitsConsistent, subcircuit, Circuit.operations, Operations.forAll]
  trivial

private lemma partialRound_body_subcircuitsConsistent
    (st : Vector (Expression (F BN254_PRIME)) 2) (c0 s0 s1 s2 : F BN254_PRIME) (n : ℕ) :
    ((subcircuit (PartialRoundOpt_t2.circuit c0 s0 s1 s2) st).operations n).SubcircuitsConsistent n := by
  simp only [Operations.SubcircuitsConsistent, subcircuit, Circuit.operations, Operations.forAll]
  trivial

private lemma Ark_t2_main_subcircuitsConsistent
    (c0 c1 : F BN254_PRIME) (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (Ark_t2.main c0 c1 state).forAll n { subcircuit offset {n} _ := n = offset } := by
  simp +arith only [Ark_t2.main, circuit_norm]

-- First 3 full rounds using Circuit.foldl with FormalCircuit.CoeFun.
def applyFullRounds1 (state : Vector (Expression (F BN254_PRIME)) 2)
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) :=
  Circuit.foldl fullRoundConstants1 state
    (fun st (c0, c1) => FullRound_t2.circuit c0 c1 m00 m01 m10 m11 st)
    fullRound_constOut fullRound_constLen

-- Last 3 full rounds using Circuit.foldl
def applyFullRounds2 (state : Vector (Expression (F BN254_PRIME)) 2)
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) :=
  Circuit.foldl fullRoundConstants2 state
    (fun st (c0, c1) => FullRound_t2.circuit c0 c1 m00 m01 m10 m11 st)
    fullRound_constOut fullRound_constLen

-- 56 partial rounds using Circuit.foldl
def applyPartialRoundsOpt (state : Vector (Expression (F BN254_PRIME)) 2)
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) :=
  Circuit.foldl partialRoundConstants state
    (fun st (c0, s0, s1, s2) => PartialRoundOpt_t2.circuit c0 s0 s1 s2 st)
    partialRound_constOut partialRound_constLen

-- Transition round: SBOX → ARK → MIX(P)
def transitionRound (input : Vector (Expression (F BN254_PRIME)) 2)
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) := do
  let s0 ← Sigma.main input[0]
  let s1 ← Sigma.main input[1]
  let a0 <== s0 + Expression.const (C_t2[8]'(by omega) : F BN254_PRIME)
  let a1 <== s1 + Expression.const (C_t2[9]'(by omega) : F BN254_PRIME)
  let out0 <== Expression.const p00 * a0 + Expression.const p10 * a1
  let out1 <== Expression.const p01 * a0 + Expression.const p11 * a1
  return #v[out0, out1]

-- Final round: SBOX → MIX(M) (no ARK)
def finalRound (input : Vector (Expression (F BN254_PRIME)) 2)
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) := do
  let s0 ← Sigma.main input[0]
  let s1 ← Sigma.main input[1]
  let out0 <== Expression.const m00 * s0 + Expression.const m10 * s1
  let out1 <== Expression.const m01 * s0 + Expression.const m11 * s1
  return #v[out0, out1]

private lemma transitionRound_subcircuitsConsistent
    (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (transitionRound state).forAll n { subcircuit offset {n} _ := n = offset } := by
  simp +arith only [transitionRound, Sigma.main, circuit_norm]

private lemma finalRound_subcircuitsConsistent
    (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (finalRound state).forAll n { subcircuit offset {n} _ := n = offset } := by
  simp +arith only [finalRound, Sigma.main, circuit_norm]

-- Foldl subcircuitsConsistent lemmas: each iteration's subcircuit is trivially consistent
-- regardless of the accumulator value, so we pass _ and Lean never evaluates it.
private lemma applyFullRounds1_subcircuitsConsistent
    (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (applyFullRounds1 state).forAll n { subcircuit offset {k} _ := k = offset } := by
  simp only [applyFullRounds1, forAll_def, foldl.forAll]
  exact ⟨fullRound_body_subcircuitsConsistent _ _ _ _,
         fun _ _ => fullRound_body_subcircuitsConsistent _ _ _ _⟩

private lemma applyFullRounds2_subcircuitsConsistent
    (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (applyFullRounds2 state).forAll n { subcircuit offset {k} _ := k = offset } := by
  simp only [applyFullRounds2, forAll_def, foldl.forAll]
  exact ⟨fullRound_body_subcircuitsConsistent _ _ _ _,
         fun _ _ => fullRound_body_subcircuitsConsistent _ _ _ _⟩

private lemma applyPartialRoundsOpt_subcircuitsConsistent
    (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (applyPartialRoundsOpt state).forAll n { subcircuit offset {k} _ := k = offset } := by
  simp only [applyPartialRoundsOpt, forAll_def, foldl.forAll]
  exact ⟨partialRound_body_subcircuitsConsistent _ _ _ _ _ _,
         fun _ _ => partialRound_body_subcircuitsConsistent _ _ _ _ _ _⟩

-- Helper lemmas: local lengths of the foldl loops, proven without evaluating BN254 constants.
private lemma applyFullRounds1_localLength (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (applyFullRounds1 state).localLength n = 30 := by
  simp only [applyFullRounds1, foldl.localLength_eq, fullRound_body_localLength]

private lemma applyFullRounds2_localLength (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (applyFullRounds2 state).localLength n = 30 := by
  simp only [applyFullRounds2, foldl.localLength_eq, fullRound_body_localLength]

private lemma applyPartialRoundsOpt_localLength (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (applyPartialRoundsOpt state).localLength n = 336 := by
  simp only [applyPartialRoundsOpt, foldl.localLength_eq, partialRound_body_localLength]

-- Local length lemmas for inline (non-foldl) phases. These let us reduce
-- offset chains in the bind decomposition without unfolding inner constraints.
private lemma Ark_t2_main_localLength_eq (c0 c1 : F BN254_PRIME)
    (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (Ark_t2.main c0 c1 state).localLength n = 2 := by
  simp [Ark_t2.main, circuit_norm]

private lemma transitionRound_localLength_eq
    (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (transitionRound state).localLength n = 10 := by
  simp [transitionRound, Sigma.main, circuit_norm]

-- Output lemmas for inline (non-foldl) phases. Concrete `var ⟨...⟩` form.
private lemma Ark_t2_main_output_eq (c0 c1 : F BN254_PRIME)
    (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (Ark_t2.main c0 c1 state).output n = #v[var ⟨n⟩, var ⟨n + 1⟩] := by
  simp [Ark_t2.main, circuit_norm]

private lemma transitionRound_output_eq
    (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (transitionRound state).output n = #v[var ⟨n + 8⟩, var ⟨n + 9⟩] := by
  simp [transitionRound, Sigma.main, circuit_norm]

private lemma finalRound_output_eq
    (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (finalRound state).output n = #v[var ⟨n + 6⟩, var ⟨n + 7⟩] := by
  simp [finalRound, Sigma.main, circuit_norm]

-- Output lemmas for foldl phases (needed for bind_soundness decomposition)
private lemma applyFullRounds1_output (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (applyFullRounds1 state).output n =
      (FullRound_t2.main fullRoundConstants1[2].1 fullRoundConstants1[2].2 m00 m01 m10 m11
        default (n + 20)).1 := by
  simp only [applyFullRounds1, circuit_norm, FullRound_t2.circuit]

private lemma applyFullRounds2_output (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (applyFullRounds2 state).output n =
      (FullRound_t2.main fullRoundConstants2[2].1 fullRoundConstants2[2].2 m00 m01 m10 m11
        default (n + 20)).1 := by
  simp only [applyFullRounds2, circuit_norm, FullRound_t2.circuit]

private lemma applyPartialRoundsOpt_output (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (applyPartialRoundsOpt state).output n =
      (PartialRoundOpt_t2.main partialRoundConstants[55].1 partialRoundConstants[55].2.1
        partialRoundConstants[55].2.2.1 partialRoundConstants[55].2.2.2
        default (n + 330)).1 := by
  simp only [applyPartialRoundsOpt, circuit_norm,
             PartialRoundOpt_t2.circuit]

-- Round body output normalization: reduce (main ... default n).1 to concrete var indices.
-- This resolves the ConstantOutput default-accumulator terms left by foldl.soundness.
@[simp] private lemma fullRound_main_output
    (c0 c1 : F BN254_PRIME) (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (FullRound_t2.main c0 c1 m00 m01 m10 m11 state n).1 =
      #v[var ⟨n + 8⟩, var ⟨n + 9⟩] := by
  simp only [FullRound_t2.main, Sigma.main, circuit_norm]

@[simp] private lemma partialRound_main_output
    (c0 s0 s1 s2 : F BN254_PRIME) (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (PartialRoundOpt_t2.main c0 s0 s1 s2 state n).1 =
      #v[var ⟨n + 4⟩, var ⟨n + 5⟩] := by
  simp only [PartialRoundOpt_t2.main, Sigma.main, circuit_norm]

-- Symbolic unfolding of mix for t=2: avoids evaluating BN254 matrix entries.
-- Instead, matches M_t2[i][j] with the named constants m00/m01/m10/m11.
private lemma mix_t2_eq (state : Vector (F BN254_PRIME) 2) :
    Specs.Poseidon.mix M_t2 state =
      #v[m00 * state[0] + m10 * state[1], m01 * state[0] + m11 * state[1]] := by
  ext i hi
  simp only [Specs.Poseidon.mix, m00, m01, m10, m11, getM, Vector.getElem_ofFn]
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · -- i = 0
    simp +decide [List.range, List.range.loop, List.foldl]
    rfl
  · simp +decide [List.range, List.range.loop, List.foldl]
    rfl

private lemma mix_P_t2_eq (state : Vector (F BN254_PRIME) 2) :
    Specs.Poseidon.mix P_t2 state =
      #v[p00 * state[0] + p10 * state[1], p01 * state[0] + p11 * state[1]] := by
  ext i hi
  simp only [Specs.Poseidon.mix, p00, p01, p10, p11, getP, Vector.getElem_ofFn]
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> (simp +decide [List.range, List.range.loop, List.foldl]; rfl)

-- Symbolic unfolding of ark for t=2
private lemma ark_t2_eq (offset : ℕ) (ho : offset + 1 < 72) (state : Vector (F BN254_PRIME) 2) :
    Specs.Poseidon.ark C_t2 offset state =
      #v[state[0] + (C_t2[offset]'(by omega) : F BN254_PRIME),
         state[1] + (C_t2[offset + 1]'ho : F BN254_PRIME)] := by
  rw [Vector.ext_iff]; intro i hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · simp [Specs.Poseidon.ark, Vector.getElem_ofFn,
      dif_pos (show offset < 72 by omega)]
    rfl
  · simp [Specs.Poseidon.ark, Vector.getElem_ofFn, dif_pos ho]
    rfl

-- Bridge: one full round's circuit Spec implies output = fullRoundOpt_t2
private lemma fullRound_spec_to_fullRoundOpt
    (offset : ℕ) (ho : offset + 1 < 72)
    (input output : Vector (F BN254_PRIME) 2)
    (h0 : output[0] = m00 * (input[0] ^ 5 + (C_t2[offset] : F BN254_PRIME)) +
                       m10 * (input[1] ^ 5 + (C_t2[offset + 1]'ho : F BN254_PRIME)))
    (h1 : output[1] = m01 * (input[0] ^ 5 + (C_t2[offset] : F BN254_PRIME)) +
                       m11 * (input[1] ^ 5 + (C_t2[offset + 1]'ho : F BN254_PRIME))) :
    output = Specs.PoseidonOptimized.fullRoundOpt_t2 C_t2 M_t2 offset input := by
  rw [Vector.ext_iff]; intro i hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · simp only [Specs.PoseidonOptimized.fullRoundOpt_t2, Specs.Poseidon.sboxFull,
               Specs.Poseidon.sigma, ark_t2_eq offset ho, mix_t2_eq, Vector.getElem_map]
    change output[0] = m00 * (input[0] ^ 5 + ↑C_t2[offset]) + m10 * (input[1] ^ 5 + (C_t2[offset + 1]'ho : F BN254_PRIME))
    exact h0
  · simp only [Specs.PoseidonOptimized.fullRoundOpt_t2, Specs.Poseidon.sboxFull,
               Specs.Poseidon.sigma, ark_t2_eq offset ho, mix_t2_eq, Vector.getElem_map]
    change output[1] = m01 * (input[0] ^ 5 + ↑C_t2[offset]) + m11 * (input[1] ^ 5 + (C_t2[offset + 1]'ho : F BN254_PRIME))
    exact h1

-- Vector access normalization: #v[a,b][0] = a is rfl but simp doesn't see it
@[simp] private lemma vec2_get0 {α : Type*} (a b : α) (h : 0 < 2 := by omega) :
    #v[a, b][0] = a := rfl
@[simp] private lemma vec2_get1 {α : Type*} (a b : α) (h : 1 < 2 := by omega) :
    #v[a, b][1] = b := rfl

-- Map normalization: pushes Vector.map through a 2-element vector literal.
private lemma vec2_map {α β : Type*} (f : α → β) (a b : α) :
    Vector.map f #v[a, b] = #v[f a, f b] := by
  apply Vector.ext
  intro i hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> simp

-- Symbolic unfolding of mixS_t2
private lemma mixS_t2_eq (sRound : ℕ) (hr : sRound < 56) (state : Vector (F BN254_PRIME) 2) :
    Specs.PoseidonOptimized.mixS_t2 S_t2 sRound state hr =
      #v[(S_t2[sRound * 3]'(by omega) : F BN254_PRIME) * state[0] +
         (S_t2[sRound * 3 + 1]'(by omega) : F BN254_PRIME) * state[1],
         state[1] + state[0] * (S_t2[sRound * 3 + 2]'(by omega) : F BN254_PRIME)] := by
  simp [Specs.PoseidonOptimized.mixS_t2]; exact ⟨rfl, rfl⟩

-- Bridge: one partial round's circuit Spec implies output = partialRoundOpt_t2
private lemma partialRound_spec_to_partialRoundOpt
    (cOffset sRound : ℕ) (hc : cOffset < 72) (hr : sRound < 56)
    (input output : Vector (F BN254_PRIME) 2)
    (h0 : output[0] = (S_t2[sRound * 3]'(by omega) : F BN254_PRIME) *
                       (input[0] ^ 5 + (C_t2[cOffset]'hc : F BN254_PRIME)) +
                       (S_t2[sRound * 3 + 1]'(by omega) : F BN254_PRIME) * input[1])
    (h1 : output[1] = input[1] +
                       (input[0] ^ 5 + (C_t2[cOffset]'hc : F BN254_PRIME)) *
                       (S_t2[sRound * 3 + 2]'(by omega) : F BN254_PRIME)) :
    output = Specs.PoseidonOptimized.partialRoundOpt_t2 C_t2 S_t2 cOffset sRound input hr := by
  simp only [Specs.PoseidonOptimized.partialRoundOpt_t2, Specs.Poseidon.sigma,
             dif_pos hc, mixS_t2_eq, vec2_get0, vec2_get1]
  rw [Vector.ext_iff]; intro i hi
  have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl
  · change _ = _; exact h0
  · change _ = _; exact h1

-- Phase soundness lemmas for each foldl loop.
set_option maxRecDepth 512 in
set_option maxHeartbeats 800000 in
private lemma applyFullRounds1_spec
    (env : Environment (F BN254_PRIME))
    (state_vars : Vector (Expression (F BN254_PRIME)) 2)
    (n : ℕ)
    (h : ConstraintsHold.Soundness env ((applyFullRounds1 state_vars).operations n)) :
    ((applyFullRounds1 state_vars).output n).map (Expression.eval env) =
      Specs.PoseidonOptimized.fullRoundsOpt_t2 C_t2 M_t2 3 2
        (state_vars.map (Expression.eval env)) := by
  -- Expand circuit constraints to per-round specs
  simp only [applyFullRounds1, circuit_norm,
             FullRound_t2.circuit, FullRound_t2.main, Sigma.main,
             fullRoundConstants1] at h
  -- Destructure: init (round 0) ∧ ∀ i hi, step (rounds 1,2)
  obtain ⟨⟨h0a, h0b⟩, h_step⟩ := h
  -- Get step specs for rounds 1 and 2
  have h1 := h_step 0 (by omega)
  have h2 := h_step 1 (by omega)
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  -- Expand ONLY the circuit output on LHS and the foldl recursion on RHS.
  -- Keep fullRoundOpt_t2 folded to avoid BN254 evaluation.
  simp only [applyFullRounds1, circuit_norm,
             FullRound_t2.circuit, FullRound_t2.main, Sigma.main]
  -- Unfold fullRoundsOpt_t2 4 times (3 rounds + base case)
  unfold Specs.PoseidonOptimized.fullRoundsOpt_t2
  unfold Specs.PoseidonOptimized.fullRoundsOpt_t2
  unfold Specs.PoseidonOptimized.fullRoundsOpt_t2
  unfold Specs.PoseidonOptimized.fullRoundsOpt_t2
  -- RHS: fullRoundOpt_t2 6 (fullRoundOpt_t2 4 (fullRoundOpt_t2 2 (state.map eval)))
  -- Use fullRound_spec_to_fullRoundOpt to fold circuit specs INTO fullRoundOpt_t2
  -- Round 0: h0a/h0b say output[0,1] match fullRoundOpt_t2 at offset 2
  -- Round 1: h1a/h1b say output[0,1] match fullRoundOpt_t2 at offset 4
  -- Round 2: h2a/h2b say output[0,1] match fullRoundOpt_t2 at offset 6
  -- Unfold each fullRoundOpt_t2 using bridge lemmas + vec2 access
  simp only [Specs.PoseidonOptimized.fullRoundOpt_t2, Specs.Poseidon.sboxFull,
             Specs.Poseidon.sigma, Vector.getElem_map,
             ark_t2_eq 2 (by omega), ark_t2_eq 4 (by omega), ark_t2_eq 6 (by omega),
             mix_t2_eq, vec2_get0, vec2_get1]
  -- Specialize step hypotheses for rounds 1 and 2
  obtain ⟨h1a, h1b⟩ := h_step 0 (by omega)
  obtain ⟨h2a, h2b⟩ := h_step 1 (by omega)
  -- Normalize all the offset arithmetic and close
  simp +arith only [] at h0a h0b h1a h1b h2a h2b ⊢
  -- Rewrite env.get values using the round specs (circuit → spec substitution)
  rw [h2a, h2b, h1a, h1b, h0a, h0b]
  -- Clean up remaining list/pair access
  rfl

set_option maxRecDepth 512 in
set_option maxHeartbeats 800000 in
private lemma applyFullRounds2_spec
    (env : Environment (F BN254_PRIME))
    (state_vars : Vector (Expression (F BN254_PRIME)) 2)
    (n : ℕ)
    (h : ConstraintsHold.Soundness env ((applyFullRounds2 state_vars).operations n)) :
    ((applyFullRounds2 state_vars).output n).map (Expression.eval env) =
      Specs.PoseidonOptimized.fullRoundsOpt_t2 C_t2 M_t2 3 66
        (state_vars.map (Expression.eval env)) := by
  simp only [applyFullRounds2, circuit_norm,
             FullRound_t2.circuit, FullRound_t2.main, Sigma.main,
             fullRoundConstants2] at h
  obtain ⟨⟨h0a, h0b⟩, h_step⟩ := h
  simp only [applyFullRounds2, circuit_norm,
             FullRound_t2.circuit, FullRound_t2.main, Sigma.main]
  unfold Specs.PoseidonOptimized.fullRoundsOpt_t2
  unfold Specs.PoseidonOptimized.fullRoundsOpt_t2
  unfold Specs.PoseidonOptimized.fullRoundsOpt_t2
  unfold Specs.PoseidonOptimized.fullRoundsOpt_t2
  simp only [Specs.PoseidonOptimized.fullRoundOpt_t2, Specs.Poseidon.sboxFull,
             Specs.Poseidon.sigma, Vector.getElem_map,
             ark_t2_eq 66 (by omega), ark_t2_eq 68 (by omega), ark_t2_eq 70 (by omega),
             mix_t2_eq, vec2_get0, vec2_get1]
  obtain ⟨h1a, h1b⟩ := h_step 0 (by omega)
  obtain ⟨h2a, h2b⟩ := h_step 1 (by omega)
  simp +arith only [] at h0a h0b h1a h1b h2a h2b ⊢
  rw [h2a, h2b, h1a, h1b, h0a, h0b]
  rfl

-- Generalized induction matching the recursion of partialRoundsOpt_t2.
-- Given a sequence of states where each step matches partialRoundOpt_t2,
-- the final state matches partialRoundsOpt_t2.
private lemma partialRounds_induction
    (nRounds cOffset sRound : ℕ)
    (hr : sRound + nRounds ≤ 56) (hc : cOffset + nRounds ≤ 72)
    (states : ℕ → Vector (F BN254_PRIME) 2)
    (h_round : ∀ (i : ℕ) (_ : i < nRounds),
        states (i + 1) = Specs.PoseidonOptimized.partialRoundOpt_t2 C_t2 S_t2
          (cOffset + i) (sRound + i) (states i) (by omega)) :
    states nRounds = Specs.PoseidonOptimized.partialRoundsOpt_t2 C_t2 S_t2
      nRounds cOffset sRound (states 0) hr := by
  induction nRounds generalizing cOffset sRound states with
  | zero => simp [Specs.PoseidonOptimized.partialRoundsOpt_t2]
  | succ k ih =>
    simp only [Specs.PoseidonOptimized.partialRoundsOpt_t2]
    have h0 := h_round 0 (by omega)
    simp only [Nat.add_zero] at h0
    rw [← h0]
    apply ih (cOffset + 1) (sRound + 1) (by omega) (by omega) (fun j => states (j + 1))
    intro i hi
    have hi' := h_round (i + 1) (by omega)
    convert hi' using 2 <;> omega

-- Hoisted helpers for applyPartialRoundsOpt_spec
private lemma partialRoundConstants_eq (i : ℕ) (hi : i < 56) :
    partialRoundConstants[i] = ((C_t2[10+i]'(by omega) : F BN254_PRIME),
      (S_t2[3*i]'(by omega) : F BN254_PRIME),
      (S_t2[3*i+1]'(by omega) : F BN254_PRIME),
      (S_t2[3*i+2]'(by omega) : F BN254_PRIME)) := by
  simp [partialRoundConstants, Vector.getElem_ofFn]

private def partialRoundState
    (env : Environment (F BN254_PRIME))
    (state_vars : Vector (Expression (F BN254_PRIME)) 2)
    (n : ℕ) (k : ℕ) : Vector (F BN254_PRIME) 2 :=
  if k = 0 then state_vars.map (Expression.eval env)
  else #v[env.get (n + (k - 1) * 6 + 4), env.get (n + (k - 1) * 6 + 5)]

set_option maxRecDepth 1024 in
-- Bridge: circuit spec (using partialRoundConstants projections) → partialRoundOpt_t2
-- This avoids specializing partialRoundConstants_eq at concrete indices.
private lemma partialRound_circuit_spec_to_opt
    (i : ℕ) (hi : i < 56)
    (input output : Vector (F BN254_PRIME) 2)
    (h0 : output[0] = partialRoundConstants[i].2.1 * (input[0] ^ 5 + partialRoundConstants[i].1) +
                       partialRoundConstants[i].2.2.1 * input[1])
    (h1 : output[1] = input[1] + (input[0] ^ 5 + partialRoundConstants[i].1) *
                       partialRoundConstants[i].2.2.2) :
    output = Specs.PoseidonOptimized.partialRoundOpt_t2 C_t2 S_t2 (10 + i) i input hi := by
  -- Unfold spec side
  simp only [Specs.PoseidonOptimized.partialRoundOpt_t2, Specs.Poseidon.sigma,
             dif_pos (show 10 + i < 72 by omega), mixS_t2_eq, vec2_get0, vec2_get1]
  -- Fold C_t2/S_t2 back to partialRoundConstants projections (abstract i)
  rw [show (C_t2[10 + i]'(by omega) : F BN254_PRIME) = partialRoundConstants[i].1 from by
        rw [partialRoundConstants_eq i hi],
      show (S_t2[i * 3]'(by omega) : F BN254_PRIME) = partialRoundConstants[i].2.1 from by
        simp only [partialRoundConstants, Vector.getElem_ofFn, show i * 3 = 3 * i from by ring],
      show (S_t2[i * 3 + 1]'(by omega) : F BN254_PRIME) = partialRoundConstants[i].2.2.1 from by
        simp only [partialRoundConstants, Vector.getElem_ofFn, show i * 3 + 1 = 3 * i + 1 from by ring],
      show (S_t2[i * 3 + 2]'(by omega) : F BN254_PRIME) = partialRoundConstants[i].2.2.2 from by
        simp only [partialRoundConstants, Vector.getElem_ofFn, show i * 3 + 2 = 3 * i + 2 from by ring]]
  -- Both sides use partialRoundConstants[i] projections; close component-wise
  rw [Vector.ext_iff]
  intro j hj
  have hj01 : j = 0 ∨ j = 1 := by omega
  rcases hj01 with rfl | rfl
  · simp only [vec2_get0]; exact h0
  · simp only [vec2_get1]; exact h1

-- Make partialRoundConstants opaque so the kernel doesn't evaluate
-- the 56-element vector during type-checking in the proof below.
attribute [irreducible] partialRoundConstants

set_option linter.constructorNameAsVariable false in
set_option maxRecDepth 1024 in
set_option maxHeartbeats 1600000 in
private lemma applyPartialRoundsOpt_spec
    (env : Environment (F BN254_PRIME))
    (state_vars : Vector (Expression (F BN254_PRIME)) 2)
    (n : ℕ)
    (h : ConstraintsHold.Soundness env ((applyPartialRoundsOpt state_vars).operations n)) :
    ((applyPartialRoundsOpt state_vars).output n).map (Expression.eval env) =
      Specs.PoseidonOptimized.partialRoundsOpt_t2 C_t2 S_t2 56 10 0
        (state_vars.map (Expression.eval env)) (by omega) := by
  -- Expand circuit constraints
  simp only [applyPartialRoundsOpt, circuit_norm,
             PartialRoundOpt_t2.circuit, PartialRoundOpt_t2.main, Sigma.main] at h
  obtain ⟨⟨h0a, h0b⟩, h_step⟩ := h
  -- Expand circuit output on LHS
  simp only [applyPartialRoundsOpt, circuit_norm,
             PartialRoundOpt_t2.circuit, PartialRoundOpt_t2.main, Sigma.main]
  -- Normalize offset arithmetic
  simp +arith only [] at h0a h0b h_step ⊢
  -- Step 1: merge init/step into uniform circuit constraints (no partialRoundOpt_t2)
  let rs := partialRoundState env state_vars n
  have h_circuit : ∀ (i : ℕ) (_ : i < 56),
      (rs (i+1))[0] = partialRoundConstants[i].2.1 * ((rs i)[0] ^ 5 + partialRoundConstants[i].1) +
                       partialRoundConstants[i].2.2.1 * (rs i)[1] ∧
      (rs (i+1))[1] = (rs i)[1] + ((rs i)[0] ^ 5 + partialRoundConstants[i].1) *
                       partialRoundConstants[i].2.2.2 := by
    intro i hi
    simp only [rs, partialRoundState]
    rcases i with _ | k
    · -- i = 0
      simp only [show (0 + 1 : ℕ) ≠ 0 from by omega, ↓reduceIte,
                  show (0 + 1 - 1 : ℕ) = 0 from by omega, Nat.zero_mul, Nat.zero_add,
                  Vector.getElem_map, vec2_get0, vec2_get1]
      exact ⟨h0a, h0b⟩
    · -- i = k+1
      simp only [show k + 1 ≠ 0 from by omega, show k + 1 + 1 ≠ 0 from by omega,
                  ↓reduceIte, vec2_get0, vec2_get1]
      obtain ⟨ha, hb⟩ := h_step k (by omega)
      simp +arith only [] at ha hb ⊢
      exact ⟨ha, hb⟩
  -- Step 2: convert to partialRoundOpt_t2 with ABSTRACT i (no BN254 evaluation)
  have h_round : ∀ (i : ℕ) (hi : i < 56),
      rs (i + 1) = Specs.PoseidonOptimized.partialRoundOpt_t2 C_t2 S_t2
        (10 + i) i (rs i) hi := by
    intro i hi
    obtain ⟨ha, hb⟩ := h_circuit i hi
    exact partialRound_circuit_spec_to_opt i hi (rs i) (rs (i+1)) ha hb
  -- Step 3: apply the induction
  have h_round' : ∀ (i : ℕ) (_ : i < 56),
      rs (i + 1) = Specs.PoseidonOptimized.partialRoundOpt_t2 C_t2 S_t2
        (10 + i) (0 + i) (rs i) (by omega) := by
    intro i hi; convert h_round i hi using 3; omega
  have := partialRounds_induction 56 10 0 (by omega) (by omega) rs h_round'
  simp only [rs, partialRoundState, show (56 : ℕ) ≠ 0 from by omega, ↓reduceIte] at this
  simp +arith only [] at this ⊢
  -- `this` is Vector equality; goal is Array equality (.toArray)
  exact congr_arg Vector.toArray this

-- Main Poseidon1 circuit (OPTIMIZED - matches circomlib)
def main (input : Expression (F BN254_PRIME)) : Circuit (F BN254_PRIME) (Expression (F BN254_PRIME)) := do
  let state : Vector (Expression (F BN254_PRIME)) 2 := #v[Expression.const 0, input]
  -- 1. Initial ARK with C[0..1]
  let c0 : F BN254_PRIME := C_t2[0]'(by omega)
  let c1 : F BN254_PRIME := C_t2[1]'(by omega)
  let state ← Ark_t2.main c0 c1 state
  -- 2. First 3 full rounds with C[2..7]
  let state ← applyFullRounds1 state
  -- 3. Transition round with C[8..9] and P matrix
  let state ← transitionRound state
  -- 4. 56 partial rounds with C[10..65] and S sparse constants
  let state ← applyPartialRoundsOpt state
  -- 5. Last 3 full rounds with C[66..71]
  let state ← applyFullRounds2 state
  -- 6. Final round (SBOX → MIX, no ARK)
  let state ← finalRound state
  return state[0]

-- Inline phase bridges: connect circuit env.get values to spec-level function results.
-- These are proven from the inline circuit constraints (soundness of ARK/transition/final).

private lemma ark_bridge
    (env : Environment (F BN254_PRIME)) (input_var : Expression (F BN254_PRIME))
    (input : F BN254_PRIME) (i0 : ℕ)
    (h_input : Expression.eval env input_var = input)
    (h : ConstraintsHold.Soundness env
      ((Ark_t2.main (C_t2[0]'(by omega) : F BN254_PRIME) (C_t2[1]'(by omega) : F BN254_PRIME)
        #v[Expression.const 0, input_var]).operations i0)) :
    Specs.Poseidon.ark C_t2 0 #v[(0 : F BN254_PRIME), input] =
      #v[env.get i0, env.get (i0 + 1)] := by
  simp only [Ark_t2.main, circuit_norm] at h
  obtain ⟨ha0, ha1⟩ := h
  rw [h_input] at ha1
  rw [Vector.ext_iff]; intro j hj; have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · simp [Specs.Poseidon.ark]; exact ha0.symm
  · simp [Specs.Poseidon.ark]; exact ha1.symm

set_option maxHeartbeats 800000 in
private lemma transition_bridge
    (env : Environment (F BN254_PRIME)) (n : ℕ)
    (h : ConstraintsHold.Soundness env ((transitionRound
      #v[var ⟨n⟩, var ⟨n + 1⟩]).operations (n + 2))) :
    #v[env.get (n + 10), env.get (n + 11)] =
      Specs.Poseidon.mix P_t2 (Specs.Poseidon.ark C_t2 8 (Specs.Poseidon.sboxFull
        #v[env.get n, env.get (n + 1)])) := by
  simp only [transitionRound, Sigma.main, circuit_norm] at h
  simp +arith only [] at h
  rw [Vector.ext_iff]; intro j hj; have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · simp only [Specs.Poseidon.sboxFull,
               ark_t2_eq 8 (by omega), mix_P_t2_eq, vec2_get0, vec2_get1]
    obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := h
    simp only [h9, h7, h8, h3, h6, h2, h5, h1, h4]
    simp [Specs.Poseidon.sigma]
    ring_nf
  · simp only [Specs.Poseidon.sboxFull,
               ark_t2_eq 8 (by omega), mix_P_t2_eq, vec2_get0, vec2_get1]
    obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10⟩ := h
    simp only [h10, h7, h8, h3, h6, h2, h5, h1, h4]
    simp [Specs.Poseidon.sigma]
    ring_nf

set_option maxHeartbeats 800000 in
private lemma final_round_bridge
    (env : Environment (F BN254_PRIME)) (n : ℕ)
    (h : ConstraintsHold.Soundness env ((finalRound
      #v[var ⟨n⟩, var ⟨n + 1⟩]).operations (n + 2))) :
    #v[env.get (n + 8), env.get (n + 9)] =
      Specs.Poseidon.mix M_t2 (Specs.Poseidon.sboxFull
        #v[env.get n, env.get (n + 1)]) := by
  simp only [finalRound, Sigma.main, circuit_norm] at h
  simp +arith only [] at h
  rw [Vector.ext_iff]; intro j hj; have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · simp only [Specs.Poseidon.sboxFull,
               mix_t2_eq, vec2_get0]
    obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
    simp only [h7, h5, h6, h3, h4, h2, h1]
    simp [Specs.Poseidon.sigma]
    ring_nf
  · simp only [Specs.Poseidon.sboxFull,
               mix_t2_eq, vec2_get1]
    obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩ := h
    simp only [h8, h5, h6, h3, h4, h2, h1]
    simp [Specs.Poseidon.sigma]
    ring_nf

-- Specialized wrappers for poseidon1_soundness:
-- These take the full `(main input_var).operations i0` hypothesis and absorb
-- the bind decomposition + offset normalization that would otherwise blow up
-- in poseidon1_soundness. They give back the bridge equation in concrete
-- offset form, ready to be used in the rw chain.

set_option maxHeartbeats 4000000 in
private lemma transition_bridge_p1
    (env : Environment (F BN254_PRIME)) (input_var : Expression (F BN254_PRIME)) (i0 : ℕ)
    (h_holds : ConstraintsHold.Soundness env ((main input_var).operations i0)) :
    #v[env.get (i0 + 40), env.get (i0 + 41)] =
      Specs.Poseidon.mix P_t2 (Specs.Poseidon.ark C_t2 8 (Specs.Poseidon.sboxFull
        #v[env.get (i0 + 30), env.get (i0 + 31)])) := by
  simp only [main] at h_holds
  have ⟨_, h_holds⟩ := (ConstraintsHold.bind_soundness i0).mp h_holds
  have ⟨_, h_holds⟩ := (ConstraintsHold.bind_soundness _).mp h_holds
  have ⟨h_trans_s, _⟩ := (ConstraintsHold.bind_soundness _).mp h_holds
  -- Normalize h_trans_s: reduce localLength chain and applyFullRounds1.output
  simp only [Ark_t2_main_localLength_eq, applyFullRounds1_localLength,
             applyFullRounds1_output, fullRound_main_output] at h_trans_s
  simp +arith only [] at h_trans_s
  -- h_trans_s now has form:
  --   ConstraintsHold.Soundness env
  --     ((transitionRound #v[var ⟨i0+30⟩, var ⟨i0+31⟩]).operations (i0+32))
  -- Apply existing bridge with n := i0 + 30
  exact transition_bridge env (i0 + 30) h_trans_s

set_option maxHeartbeats 4000000 in
private lemma final_round_bridge_p1
    (env : Environment (F BN254_PRIME)) (input_var : Expression (F BN254_PRIME)) (i0 : ℕ)
    (h_holds : ConstraintsHold.Soundness env ((main input_var).operations i0)) :
    #v[env.get (i0 + 414), env.get (i0 + 415)] =
      Specs.Poseidon.mix M_t2 (Specs.Poseidon.sboxFull
        #v[env.get (i0 + 406), env.get (i0 + 407)]) := by
  simp only [main] at h_holds
  have ⟨_, h_holds⟩ := (ConstraintsHold.bind_soundness i0).mp h_holds
  have ⟨_, h_holds⟩ := (ConstraintsHold.bind_soundness _).mp h_holds
  have ⟨_, h_holds⟩ := (ConstraintsHold.bind_soundness _).mp h_holds
  have ⟨_, h_holds⟩ := (ConstraintsHold.bind_soundness _).mp h_holds
  have ⟨_, h_holds⟩ := (ConstraintsHold.bind_soundness _).mp h_holds
  have ⟨h_final_s, _⟩ := (ConstraintsHold.bind_soundness _).mp h_holds
  -- Normalize h_final_s: reduce localLength chain and applyFullRounds2.output
  simp only [Ark_t2_main_localLength_eq, applyFullRounds1_localLength,
             transitionRound_localLength_eq, applyPartialRoundsOpt_localLength,
             applyFullRounds2_localLength, applyFullRounds2_output,
             fullRound_main_output] at h_final_s
  simp +arith only [] at h_final_s
  -- h_final_s now has form:
  --   ConstraintsHold.Soundness env
  --     ((finalRound #v[var ⟨i0+406⟩, var ⟨i0+407⟩]).operations (i0+408))
  -- Apply existing bridge with n := i0 + 406
  exact final_round_bridge env (i0 + 406) h_final_s

-- Pre-packaged rewrite target: the output of main is the variable at offset i0 + 414.
-- Computes the output via the bind chain using only targeted output/localLength lemmas
-- (no circuit_norm), so the inner foldl bodies stay abstract.
set_option maxHeartbeats 4000000 in
private lemma main_output_eq (input_var : Expression (F BN254_PRIME)) (i0 : ℕ) :
    (main input_var).output i0 = var ⟨i0 + 414⟩ := by
  simp only [main, bind_output_eq, pure_output_eq,
             Ark_t2_main_output_eq, Ark_t2_main_localLength_eq,
             applyFullRounds1_output, applyFullRounds1_localLength,
             transitionRound_output_eq, transitionRound_localLength_eq,
             applyPartialRoundsOpt_output, applyPartialRoundsOpt_localLength,
             applyFullRounds2_output, applyFullRounds2_localLength,
             finalRound_output_eq,
             fullRound_main_output, partialRound_main_output,
             vec2_get0]

-- Standalone soundness theorem with its own heartbeat budget
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 4000000 in
private theorem poseidon1_soundness :
    ∀ (offset : ℕ) (env : Environment (F BN254_PRIME))
      (input_var : Var field (F BN254_PRIME)) (input : field (F BN254_PRIME)),
    eval env input_var = input →
    True →
    ConstraintsHold.Soundness env (main input_var |>.operations offset) →
    Expression.eval env ((main input_var).output offset) =
      Specs.PoseidonOptimized.poseidon1Opt input := by
  intro i0 env input_var input h_input _ h_holds
  -- Compute the inline-phase bridges from the raw h_holds (the wrappers
  -- absorb the offset/state normalization internally).
  have hb2 := transition_bridge_p1 env input_var i0 h_holds
  have hb5 := final_round_bridge_p1 env input_var i0 h_holds
  -- Stage 1: Bind decomposition for the remaining hypotheses.
  simp only [main] at h_holds
  have ⟨h_ark_s, h_holds⟩ := (ConstraintsHold.bind_soundness i0).mp h_holds
  have ⟨h_fr1, h_holds⟩ := (ConstraintsHold.bind_soundness _).mp h_holds
  have ⟨_, h_holds⟩ := (ConstraintsHold.bind_soundness _).mp h_holds
  have ⟨h_partial, h_holds⟩ := (ConstraintsHold.bind_soundness _).mp h_holds
  have ⟨h_fr2, _⟩ := (ConstraintsHold.bind_soundness _).mp h_holds
  clear h_holds
  -- Stage 2: Apply phase specs + ark bridge, clear as we go
  have hs1 := applyFullRounds1_spec env _ _ h_fr1; clear h_fr1
  have hs3 := applyPartialRoundsOpt_spec env _ _ h_partial; clear h_partial
  have hs4 := applyFullRounds2_spec env _ _ h_fr2; clear h_fr2
  simp only [circuit_norm] at h_input
  have hb0 := ark_bridge env input_var input i0 h_input h_ark_s; clear h_ark_s
  -- Narrow normalization: only the targeted output / localLength lemmas, NO circuit_norm.
  -- circuit_norm leaves the hypotheses with heavy proof terms that poison subsequent
  -- elaboration of vector-typed terms in this theorem.
  simp only [Ark_t2_main_output_eq, Ark_t2_main_localLength_eq,
             applyFullRounds1_output, applyFullRounds1_localLength,
             applyFullRounds2_output,
             applyPartialRoundsOpt_output, applyPartialRoundsOpt_localLength,
             transitionRound_output_eq, transitionRound_localLength_eq,
             fullRound_main_output, partialRound_main_output,
             vec2_map, Expression.eval] at hs1 hs3 hs4
  simp +arith only [] at hs1 hs3 hs4
  -- Reduce the goal LHS to env.get (i0 + 414) via the pre-packaged lemma.
  rw [main_output_eq]
  show env.get (i0 + 414) = _
  -- Convert to a vector projection so we can use the bridges and phase specs.
  show (#v[env.get (i0 + 414), env.get (i0 + 415)] : Vector (F BN254_PRIME) 2)[0] = _
  rw [hb5, hs4, hs3, hb2, hs1, ← hb0]
  -- Both sides should now match poseidon1Opt's structure.
  rfl

def elaborated : ElaboratedCircuit (F BN254_PRIME) field field where
  main
  localLength _ := 416
  localLength_eq input n := by
    simp only [main, applyFullRounds1_localLength, applyFullRounds2_localLength,
               applyPartialRoundsOpt_localLength,
               Ark_t2.main, transitionRound, finalRound, Sigma.main, circuit_norm]
  subcircuitsConsistent input i0 := by
    simp only [Operations.SubcircuitsConsistent, main, bind_forAll,
               Operations.forAll,
               Ark_t2_main_subcircuitsConsistent,
               transitionRound_subcircuitsConsistent,
               finalRound_subcircuitsConsistent,
               applyFullRounds1_subcircuitsConsistent,
               applyFullRounds2_subcircuitsConsistent,
               applyPartialRoundsOpt_subcircuitsConsistent,
               and_true]

-- THE KEY SPEC: circuit output equals the optimized Poseidon hash function
def Spec (input : F BN254_PRIME) (output : F BN254_PRIME) :=
  output = Specs.PoseidonOptimized.poseidon1Opt input

theorem soundness : Soundness (F BN254_PRIME) elaborated (fun _ => True) Spec := by
  intro i0 env input_var input h_input h_assumptions h_holds
  simp only [circuit_norm, Spec]
  exact poseidon1_soundness i0 env input_var input h_input h_assumptions h_holds

theorem completeness : Completeness (F BN254_PRIME) elaborated (fun _ => True) := by
  circuit_proof_start [main, applyFullRounds1, applyFullRounds2, applyPartialRoundsOpt,
    Ark_t2.main, transitionRound, finalRound, Sigma.main,
    FullRound_t2.circuit, PartialRoundOpt_t2.circuit]
  grind

-- The formal circuit with meaningful spec
set_option maxHeartbeats 800000 in
def circuit : FormalCircuit (F BN254_PRIME) field field where
  elaborated
  Spec
  soundness
  completeness



end Poseidon1

end Circomlib.Poseidon
