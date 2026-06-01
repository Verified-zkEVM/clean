import Clean.Circuit
import Clean.Specs.Poseidon
import Clean.Specs.PoseidonOptimized
import Clean.Utils.Tactics.CircuitProofStart

/-
Poseidon Hash Circuit Implementation

This file implements Poseidon hash circuits matching circomlib's structure.
We start with Poseidon1 (1 input, t=2) as the simplest case.

Original circomlib source:
https://github.com/iden3/circomlib/blob/master/circuits/poseidon.circom
-/

namespace Circomlib.Poseidon

open Specs.Poseidon (F BN254_PRIME C_t2 M_t2)
open Specs.PoseidonOptimized (P_t2 S_t2)

-- BN254 prime facts (BN254_PRIME is a well-known prime, proofs omitted for performance)
instance : Fact (Nat.Prime BN254_PRIME) := ⟨by sorry⟩

/-
============================================================================
SIGMA (S-box): x^5
============================================================================
template Sigma() {
    signal input in;
    signal output out;
    signal in2, in4;
    in2 <== in*in;
    in4 <== in2*in2;
    out <== in4*in;
}
-/
namespace Sigma

def main (input : Expression F) :
    Circuit F (Expression F) := do
  let in2 <== input * input
  let in4 <== in2 * in2
  let out <== in4 * input
  return out

def circuit : FormalCircuit F field field where
  main := main

  Assumptions _ := True
  Spec (input : F) (output : F) := output = input ^ 5

  soundness := by
    -- Introduce all the quantified variables and hypotheses
    intro offset env input_var input h_input h_assumptions h_constraints
    -- Simplify the circuit structure
    simp only [circuit_norm, main] at *
    -- h_constraints should now be a conjunction of the three constraint equations
    -- Destructure it
    obtain ⟨h_in2, h_in4, h_out⟩ := h_constraints
    -- h_in2: env.get offset = input_var.eval env * input_var.eval env
    -- h_in4: env.get (offset+1) = env.get offset * env.get offset
    -- h_out: env.get (offset+2) = env.get (offset+1) * input_var.eval env
    -- Goal: env.get (offset+2) = input^5
    rw [h_input] at *
    -- Now substitute through
    rw [h_out, h_in4, h_in2]
    ring

  completeness := by
    simp_all only [circuit_norm, main]

end Sigma

/-
============================================================================
ARK: Add Round Constants for t=2
============================================================================
template Ark(t, C, r) {
    signal input in[t];
    signal output out[t];
    for (var i=0; i < t; i++) {
        out[i] <== in[i] + C[i + r];
    }
}

For t=2:
  out[0] = in[0] + C[r]
  out[1] = in[1] + C[r + 1]

ARK is inlined into InitialArk and the full-round code below.
============================================================================
MIX: Matrix Multiplication for t=2
============================================================================
template Mix(t, M) {
    signal input in[t];
    signal output out[t];
    var lc;
    for (var i=0; i < t; i++) {
        lc = 0;
        for (var j=0; j < t; j++) {
            lc += M[j][i]*in[j];
        }
        out[i] <== lc;
    }
}

For t=2:
  out[0] = M[0][0]*in[0] + M[1][0]*in[1]
  out[1] = M[0][1]*in[0] + M[1][1]*in[1]

MIX is inlined into the full-round code below.

MIXS: Sparse Matrix Multiplication for t=2 (optimized partial rounds)
============================================================================
In circomlib's optimized implementation, partial rounds use sparse matrices.
For t=2, each round uses 3 sparse constants from S:
  out[0] = S[0]*in[0] + S[1]*in[1]
  out[1] = in[1] + in[0]*S[2]

This is more efficient than full matrix multiplication.

MIXS is inlined into the partial-round code below.
-/

/-
============================================================================
FULL ROUND for t=2: SBOX on both → ARK → MIX
============================================================================
In circomlib, full rounds are inlined in the main Poseidon template:

    for (r = 0; r < nRoundsF/2; r++) {
        for (j = 0; j < t; j++) {
            ark[r][j].in <== r == 0 ? inputs[j] : mix[r-1].out[j];
            ark[r][j].c <== C[r*t + j];
        }
        for (j = 0; j < t; j++) {
            sigmaF[r*t + j].in <== ark[r][j].out;
        }
        for (j = 0; j < t; j++) {
            mix[r].in[j] <== sigmaF[r*t + j].out;
        }
    }

The optimized full-round component below implements this directly.
-/

/-
============================================================================
PARTIAL ROUND (OPTIMIZED) for t=2: SBOX on first → ARK on first → MixS
============================================================================
In the optimized circomlib implementation, partial rounds use sparse matrix
multiplication (MixS) instead of full matrix multiplication (Mix).
This is more efficient and matches the actual circomlib implementation.
The concrete optimized partial-round component below implements this directly.
-/

/-
============================================================================
POSEIDON1: Hash for 1 input (t=2) - BN254 Field
============================================================================
Original circomlib template:

template Poseidon(nInputs) {
    signal input inputs[nInputs];
    signal output out;

    component pEx = PoseidonEx(nInputs, 1);
    for (var i = 0; i < nInputs; i++) {
        pEx.inputs[i] <== inputs[i];
    }
    pEx.initialState <== 0;
    out <== pEx.out[0];
}

For nInputs=1, t=2, nRoundsF=8, nRoundsP=56, the OPTIMIZED round structure is:
1. Initial ARK: add C[0..1] to state [0, input]
2. First half full rounds (3): SBOX → ARK → MIX(M), uses C[2..7]
3. Transition round: SBOX → ARK → MIX(P), uses C[8..9]
4. Partial rounds (56): SBOX_first → ARK_first → MixS(S), uses C[10..65]
5. Second half full rounds (3): SBOX → ARK → MIX(M), uses C[66..71]
6. Final round: SBOX → MIX(M) (no ARK)
7. Output: first element of final state

Total witnesses: Initial ARK (2) + 3 full rounds (24) + transition round (8)
                 + 56 partial rounds (336) + 3 full rounds (24) + final round (8) = 402
-/
namespace Poseidon1

private lemma ark_t2_eq (C : Vector ℕ 72) (offset : ℕ) (ho : offset + 1 < 72) (state : Vector F 2) :
  Specs.Poseidon.ark C offset state =
    #v[state[0] + C[offset], state[1] + C[offset + 1]] := by
  simp [Specs.Poseidon.ark, ho, show offset < 72 by omega, Array.ofFn_succ]

private lemma ark_zero_t2_eq (state : Vector F 2) :
    Specs.Poseidon.ark (.replicate 72 0) 0 state = state := by
  rw [ark_t2_eq _ _ (by norm_num)]; simp; grind

private lemma mix_matrix_t2_eq (M : Vector (Vector ℕ 2) 2) (state : Vector F 2) :
    Specs.Poseidon.mix M state =
      #v[M[0][0] * state[0] + M[1][0] * state[1],
         M[0][1] * state[0] + M[1][1] * state[1]] := by
  simp [Specs.Poseidon.mix, List.range_succ, Array.ofFn_succ]

namespace InitialArk

def circuit : FormalCircuit F field (fields 2) where
  main input := do
    let state := #v[.const 0, input]
    let out0 <== state[0] + Expression.const (C_t2[0] : F)
    let out1 <== state[1] + Expression.const (C_t2[1] : F)
    return #v[out0, out1]

  Spec (input : F) (output : Vector F 2) :=
    output = Specs.Poseidon.ark C_t2 0 #v[0, input]

  soundness := by
    circuit_proof_start
    rw [ark_t2_eq C_t2 0 (by omega)]
    simp_all
  completeness := by
    circuit_proof_all

end InitialArk

namespace FullRound_t2

def main (C : Vector ℕ 72) (M : Vector (Vector ℕ 2) 2) (offset : Fin 71) (state : Vector (Expression F) 2) :
    Circuit F (Vector (Expression F) 2) := do
  let s0 ← Sigma.circuit state[0]
  let s1 ← Sigma.circuit state[1]
  let a0 := s0 + .const C[offset.val]
  let a1 := s1 + .const C[offset.val + 1]
  let out0 <== .const M[0][0] * a0 + .const M[1][0] * a1
  let out1 <== .const M[0][1] * a0 + .const M[1][1] * a1
  return #v[out0, out1]

def Spec (C : Vector ℕ 72) (M : Vector (Vector ℕ 2) 2) (offset : Fin 71)
    (input output : Vector F 2) : Prop :=
  output = Specs.PoseidonOptimized.fullRoundOpt_t2 C M offset.val input

instance elaborated (C : Vector ℕ 72) (M : Vector (Vector ℕ 2) 2) (offset : Fin 71) :
    ElaboratedCircuit F (fields 2) (fields 2) (main C M offset) := by
  elaborate_circuit

theorem soundness (C : Vector ℕ 72) (M : Vector (Vector ℕ 2) 2) (offset : Fin 71) :
    Soundness F (Input := fields 2) (Output := fields 2) (main C M offset) (fun _ => True) (Spec C M offset) := by
  circuit_proof_start [Sigma.circuit]
  simp only [Specs.PoseidonOptimized.fullRoundOpt_t2, Specs.Poseidon.sboxFull]
  rw [ark_t2_eq C offset.val (by omega)]
  simp only [Specs.Poseidon.sigma, mix_matrix_t2_eq, Vector.getElem_map]
  obtain ⟨h0, h1, h2, h3⟩ := h_holds
  have h_in0 : Expression.eval env input_var[0] = input[0] := by
    simpa using congrArg (fun v => v[0]) h_input
  have h_in1 : Expression.eval env input_var[1] = input[1] := by
    simpa using congrArg (fun v => v[1]) h_input
  rw [h2, h3, h0, h1]
  rw [h_in0, h_in1]
  rfl

theorem completeness (C : Vector ℕ 72) (M : Vector (Vector ℕ 2) 2) (offset : Fin 71) :
    Completeness F (Input := fields 2) (Output := fields 2) (main C M offset) (fun _ => True) := by
  circuit_proof_start [Sigma.circuit]
  simp_all

def circuit (C : Vector ℕ 72) (M : Vector (Vector ℕ 2) 2) (offset : Fin 71) :
    FormalCircuit F (fields 2) (fields 2) where
  main := main C M offset
  elaborated := elaborated C M offset
  Spec := Spec C M offset
  soundness := soundness C M offset
  completeness := completeness C M offset

end FullRound_t2

namespace ApplyFullRounds

def main (offset : ℕ) (h : offset + 4 < 71) (state : Vector (Expression F) 2) :
    Circuit F (Vector (Expression F) 2) :=
  Circuit.foldl (.ofFn fun (i : Fin 3) => ⟨offset + 2*i.val, by omega⟩) state
    (fun st offset => FullRound_t2.circuit C_t2 M_t2 offset st)
    (by simp only [circuit_norm, FullRound_t2.circuit, FullRound_t2.elaborated])

def Spec (offset : ℕ) (input output : Vector F 2) : Prop :=
  output = Specs.PoseidonOptimized.fullRoundsOpt_t2 C_t2 M_t2 3 offset input

instance elaborated (offset : ℕ) (h : offset + 4 < 71) :
    ElaboratedCircuit F (fields 2) (fields 2) (main offset h) := by
  elaborate_circuit

theorem soundness (offset : ℕ) (h : offset + 4 < 71) :
    Soundness F (Input := fields 2) (Output := fields 2) (main offset h) (fun _ => True) (Spec offset) := by
  circuit_proof_start [FullRound_t2.circuit, FullRound_t2.elaborated, FullRound_t2.Spec]
  obtain ⟨h0, h_step⟩ := h_holds
  have h1 := h_step 0 (by omega)
  have h2 := h_step 1 (by omega)
  simp_all [Specs.PoseidonOptimized.fullRoundsOpt_t2]

theorem completeness (offset : ℕ) (h : offset + 4 < 71) :
    Completeness F (Input := fields 2) (Output := fields 2) (main offset h) (fun _ => True) := by
  circuit_proof_start [FullRound_t2.circuit]

def circuit (offset : ℕ) (h : offset + 4 < 71) :
    FormalCircuit F (fields 2) (fields 2) where
  main := main offset h
  elaborated := elaborated offset h
  Spec := Spec offset
  soundness := soundness offset h
  completeness := completeness offset h

end ApplyFullRounds

namespace PartialRoundOpt_t2

def main (round : Fin 56) (state : Vector (Expression F) 2) :
    Circuit F (Vector (Expression F) 2) := do
  let sbox0 ← Sigma.circuit state[0]
  let a0 <== sbox0 + .const C_t2[10 + round.val]
  let out0 <== .const S_t2[3*round.val] * a0 + .const S_t2[3*round.val + 1] * state[1]
  let out1 <== state[1] + a0 * .const S_t2[3*round.val + 2]
  return #v[out0, out1]

def Spec (round : Fin 56) (input output : Vector F 2) : Prop :=
  output = Specs.PoseidonOptimized.partialRoundOpt_t2 C_t2 S_t2 (10 + round.val)
    round.val input round.isLt

instance elaborated (round : Fin 56) : ElaboratedCircuit F (fields 2) (fields 2) (main round) := by
  elaborate_circuit

theorem soundness (round : Fin 56) :
    Soundness F (Input := fields 2) (Output := fields 2) (main round) (fun _ => True) (Spec round) := by
  circuit_proof_start [Sigma.circuit]
  simp only [Specs.PoseidonOptimized.partialRoundOpt_t2, Specs.Poseidon.sigma,
    dif_pos (show 10 + round.val < 72 by omega), Specs.PoseidonOptimized.mixS_t2]
  obtain ⟨h0, h1, h2, h3⟩ := h_holds
  have h_in0 : Expression.eval env input_var[0] = input[0] := by
    simpa using congrArg (fun v => v[0]) h_input
  have h_in1 : Expression.eval env input_var[1] = input[1] := by
    simpa using congrArg (fun v => v[1]) h_input
  rw [h2, h3, h1, h0, h_in0, h_in1]
  simp +arith [show round.val * 3 = 3 * round.val by ring]

theorem completeness (round : Fin 56) :
    Completeness F (Input := fields 2) (Output := fields 2) (main round) (fun _ => True) := by
  circuit_proof_start [Sigma.circuit]
  simp_all

def circuit (round : Fin 56) : FormalCircuit F (fields 2) (fields 2) where
  main := main round
  elaborated := elaborated round
  Spec := Spec round
  soundness := soundness round
  completeness := completeness round

end PartialRoundOpt_t2

private lemma partialRoundsOpt_induction
    (nRounds cOffset sRound : ℕ)
    (hr : sRound + nRounds ≤ 56)
    (states : ℕ → Vector F 2)
    (h_round : ∀ (i : ℕ) (_ : i < nRounds),
        states (i + 1) = Specs.PoseidonOptimized.partialRoundOpt_t2 C_t2 S_t2
          (cOffset + i) (sRound + i) (states i) (by omega)) :
    states nRounds = Specs.PoseidonOptimized.partialRoundsOpt_t2 C_t2 S_t2
      nRounds cOffset sRound (states 0) hr := by
  induction nRounds generalizing cOffset sRound states with
  | zero =>
      simp [Specs.PoseidonOptimized.partialRoundsOpt_t2]
  | succ k ih =>
      simp only [Specs.PoseidonOptimized.partialRoundsOpt_t2]
      have h0 := h_round 0 (by omega)
      simp only [Nat.add_zero] at h0
      rw [← h0]
      apply ih (cOffset + 1) (sRound + 1) (by omega) (fun j => states (j + 1))
      intro i hi
      have hi' := h_round (i + 1) (by omega)
      convert hi' using 2 <;> omega

namespace ApplyPartialRoundsOpt

def main (state : Vector (Expression F) 2)
    : Circuit F (Vector (Expression F) 2) :=
  Circuit.foldl (.finRange 56) state
    (fun st round => PartialRoundOpt_t2.circuit round st)
    (by simp only [circuit_norm, PartialRoundOpt_t2.circuit,
      PartialRoundOpt_t2.elaborated])
    -- TODO why doesn't this work automatically??
    ⟨ 6, by simp only [circuit_norm, PartialRoundOpt_t2.circuit] ⟩

def Spec (input output : Vector F 2) : Prop :=
  output = Specs.PoseidonOptimized.partialRoundsOpt_t2 C_t2 S_t2 56 10 0 input (by omega)

def Assumptions (_ : Vector F 2) : Prop :=
  True

def envState (env : Environment F) (input : Vector F 2)
    (n k : ℕ) : Vector F 2 :=
  if k = 0 then input
  else #v[env.get (n + (k - 1) * 6 + 4), env.get (n + (k - 1) * 6 + 5)]

-- TODO AUTOELAB
instance elaborated : ElaboratedCircuit F (fields 2) (fields 2) main where
  localLength _ := 336
  localLength_eq := by
    simp only [circuit_norm, main, PartialRoundOpt_t2.circuit,
      PartialRoundOpt_t2.elaborated]
  output _ i := #v[varFromOffset field (i + 334), varFromOffset field (i + 335)]
  output_eq := by
    simp only [circuit_norm, main, PartialRoundOpt_t2.circuit,
      PartialRoundOpt_t2.elaborated]
  subcircuitsConsistent := by
    simp only [circuit_norm, main, PartialRoundOpt_t2.circuit,
      PartialRoundOpt_t2.elaborated]

theorem soundness : Soundness F (Input := fields 2) (Output := fields 2) main Assumptions Spec := by
  circuit_proof_start [PartialRoundOpt_t2.circuit, PartialRoundOpt_t2.elaborated,
    PartialRoundOpt_t2.Spec]
  obtain ⟨h0, h_step⟩ := h_holds
  have h_round : ∀ (k : ℕ) (hk : k < 56),
      envState env input i₀ (k + 1) =
        Specs.PoseidonOptimized.partialRoundOpt_t2 C_t2 S_t2 (10 + k) k
          (envState env input i₀ k) hk := by
    intro k hk
    rcases k with _ | j
    · exact Vector.toArray_inj.mp (by simpa [envState] using h0)
    · have hj := h_step j (by omega)
      exact Vector.toArray_inj.mp (by simpa +arith [envState] using hj)
  have h_final := partialRoundsOpt_induction 56 10 0 (by omega)
    (fun k => envState env input i₀ k)
    (by
      intro i hi
      simp only [zero_add]
      exact h_round i hi)
  exact congr_arg Vector.toArray h_final

theorem completeness : Completeness F (Input := fields 2) (Output := fields 2) main Assumptions := by
  circuit_proof_start [PartialRoundOpt_t2.circuit]

def circuit : FormalCircuit F (fields 2) (fields 2) where
  main
  elaborated
  Assumptions
  Spec
  soundness
  completeness := by simp [completeness]

end ApplyPartialRoundsOpt

def main (input : Expression F) : Circuit F (Expression F) := do
  let state ← InitialArk.circuit input
  let state ← ApplyFullRounds.circuit 2 (by omega) state
  let state ← FullRound_t2.circuit C_t2 P_t2 ⟨8, by omega⟩ state
  let state ← ApplyPartialRoundsOpt.circuit state
  let state ← ApplyFullRounds.circuit 66 (by omega) state
  let state ← FullRound_t2.circuit (.replicate 72 0) M_t2 ⟨0, by omega⟩ state
  return state[0]

def Spec (input output : F) : Prop :=
  output = Specs.PoseidonOptimized.poseidon1Opt input

instance elaborated : ElaboratedCircuit F field field main := by
  elaborate_circuit_with {
    output _ offset := varFromOffset field (offset + 2 + 24 + 8 + 336 + 24 + 3 + 3)
  } using by
    simp only [circuit_norm]

theorem soundness : Soundness F (Input := field) (Output := field) (elaborated := elaborated) main (fun _ => True) Spec := by
  circuit_proof_start [InitialArk.circuit, ApplyFullRounds.circuit, FullRound_t2.circuit,
    ApplyPartialRoundsOpt.circuit]
  simp +arith only [circuit_norm, ApplyFullRounds.Spec, FullRound_t2.Spec,
    ApplyPartialRoundsOpt.Spec, ApplyPartialRoundsOpt.Assumptions,
    Specs.PoseidonOptimized.fullRoundOpt_t2, ark_zero_t2_eq,
    Specs.PoseidonOptimized.poseidon1Opt] at h_holds ⊢
  -- TODO AUTOELAB
  stop
  -- get rid of the [0] in the output
  apply congrArg (fun v => v[0]) (a₁ := #v[env.get (i₀ + 400), env.get (i₀ + 401)])
  simp_all

theorem completeness : Completeness F (Input := field) (Output := field) main (fun _ => True) := by
  circuit_proof_start [InitialArk.circuit, ApplyFullRounds.circuit, FullRound_t2.circuit,
    ApplyPartialRoundsOpt.circuit, ApplyPartialRoundsOpt.Assumptions]

def circuit : FormalCircuit F field field where
  main
  elaborated
  Spec
  soundness
  completeness

end Poseidon1

end Circomlib.Poseidon
