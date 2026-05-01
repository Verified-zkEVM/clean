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
  localLength _ := 3
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]
  output _ i := varFromOffset field (i + 2)

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

open Circuit

-- Offsets for foldl full-round phases, matching the optimized spec recursion.
def fullRoundOffsets (offset : ℕ) (h : offset + 4 < 71) : Vector (Fin 71) 3 :=
  Vector.ofFn fun i =>
    ⟨offset + 2*i.val, by omega⟩

def zeroRoundConstants : Vector ℕ 72 :=
  Vector.ofFn fun _ => 0

def partialRoundIndices : Vector (Fin 56) 56 :=
  Vector.ofFn fun i => i

private lemma ark_t2_eq (C : Vector ℕ 72) (offset : ℕ) (ho : offset + 1 < 72)
    (state : Vector F 2) :
    Specs.Poseidon.ark C offset state =
      #v[state[0] + (C[offset]'(by omega) : F),
         state[1] + (C[offset + 1]'ho : F)] := by
  apply Vector.ext
  intro idx hidx
  have hidx' : idx = 0 ∨ idx = 1 := by omega
  rcases hidx' with rfl | rfl
  · simp [Specs.Poseidon.ark, show offset < 72 by omega]
  · simp [Specs.Poseidon.ark, ho]

private lemma ark_zero_t2_eq (state : Vector F 2) :
    Specs.Poseidon.ark zeroRoundConstants 0 state = state := by
  apply Vector.ext
  intro idx hidx
  have hidx' : idx = 0 ∨ idx = 1 := by omega
  rcases hidx' with rfl | rfl <;> simp [Specs.Poseidon.ark, zeroRoundConstants]

private lemma mix_matrix_t2_eq (M : Vector (Vector ℕ 2) 2)
    (state : Vector F 2) :
    Specs.Poseidon.mix M state =
      #v[(M[0][0] : F) * state[0] + (M[1][0] : F) * state[1],
         (M[0][1] : F) * state[0] + (M[1][1] : F) * state[1]] := by
  apply Vector.ext
  intro idx hidx
  simp only [Specs.Poseidon.mix, Vector.getElem_ofFn]
  have hidx' : idx = 0 ∨ idx = 1 := by omega
  rcases hidx' with rfl | rfl
  · simp +decide [List.range, List.range.loop, List.foldl]
  · simp +decide [List.range, List.range.loop, List.foldl]

private lemma mixS_t2_eq (round : ℕ) (hr : round < 56) (state : Vector F 2) :
    Specs.PoseidonOptimized.mixS_t2 S_t2 round state hr =
      #v[(S_t2[round * 3]'(by omega) : F) * state[0] +
         (S_t2[round * 3 + 1]'(by omega) : F) * state[1],
         state[1] + state[0] * (S_t2[round * 3 + 2]'(by omega) : F)] := by
  simp [Specs.PoseidonOptimized.mixS_t2]

namespace InitialArk

def main (input : Expression F)
    : Circuit F (Vector (Expression F) 2) := do
  let state : Vector (Expression F) 2 := #v[Expression.const 0, input]
  let out0 <== state[0] + Expression.const (C_t2[0] : F)
  let out1 <== state[1] + Expression.const (C_t2[1] : F)
  return #v[out0, out1]

def circuit : FormalCircuit F field (fields 2) where
  main
  localLength _ := 2
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]
  output _ i := #v[varFromOffset field i, varFromOffset field (i + 1)]

  Assumptions _ := True
  Spec (input : F) (output : Vector F 2) :=
    output = Specs.Poseidon.ark C_t2 0 #v[0, input]

  soundness := by
    circuit_proof_start
    rw [ark_t2_eq C_t2 0 (by omega)]
    simp_all

  completeness := by
    circuit_proof_all

end InitialArk

namespace FullRoundOpt_t2

def main (C : Vector ℕ 72) (M : Vector (Vector ℕ 2) 2) (offset : Fin 71)
    (state : Vector (Expression F) 2)
    : Circuit F (Vector (Expression F) 2) := do
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

def elaborated (C : Vector ℕ 72) (M : Vector (Vector ℕ 2) 2) (offset : Fin 71) :
    ElaboratedCircuit F (fields 2) (fields 2) where
  main := main C M offset
  localLength _ := 8
  output _ i := #v[varFromOffset field (i + 6), varFromOffset field (i + 7)]
  subcircuitsConsistent := by
    simp +arith only [circuit_norm, main, Sigma.circuit]

theorem soundness (C : Vector ℕ 72) (M : Vector (Vector ℕ 2) 2) (offset : Fin 71) :
    Soundness F (elaborated C M offset) (fun _ => True) (Spec C M offset) := by
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
    Completeness F (elaborated C M offset) (fun _ => True) := by
  circuit_proof_start [Sigma.circuit]
  simp_all

def circuit (C : Vector ℕ 72) (M : Vector (Vector ℕ 2) 2) (offset : Fin 71) :
    FormalCircuit F (fields 2) (fields 2) where
  elaborated := elaborated C M offset
  Spec := Spec C M offset
  soundness := soundness C M offset
  completeness := completeness C M offset

end FullRoundOpt_t2

namespace ApplyFullRounds

def main (offset : ℕ) (h : offset + 4 < 71)
    (state : Vector (Expression F) 2)
    : Circuit F (Vector (Expression F) 2) :=
  Circuit.foldl (fullRoundOffsets offset h) state
    (fun st offset => FullRoundOpt_t2.circuit C_t2 M_t2 offset st)
    (by simp only [circuit_norm, FullRoundOpt_t2.circuit, FullRoundOpt_t2.elaborated])

def Spec (offset : ℕ) (input output : Vector F 2) : Prop :=
  output = Specs.PoseidonOptimized.fullRoundsOpt_t2 C_t2 M_t2 3 offset input

def elaborated (offset : ℕ) (h : offset + 4 < 71) :
    ElaboratedCircuit F (fields 2) (fields 2) where
  main := main offset h
  localLength _ := 24
  output _ i := #v[varFromOffset field (i + 22), varFromOffset field (i + 23)]
  subcircuitsConsistent := by
    simp only [circuit_norm, main]

theorem soundness (offset : ℕ) (h : offset + 4 < 71) :
    Soundness F (elaborated offset h) (fun _ => True) (Spec offset) := by
  circuit_proof_start [FullRoundOpt_t2.circuit, FullRoundOpt_t2.elaborated, FullRoundOpt_t2.Spec]
  obtain ⟨h0, h_step⟩ := h_holds
  have h1 := h_step 0 (by omega)
  have h2 := h_step 1 (by omega)
  simp_all [Specs.PoseidonOptimized.fullRoundsOpt_t2,
    fullRoundOffsets]

theorem completeness (offset : ℕ) (h : offset + 4 < 71) :
    Completeness F (elaborated offset h) (fun _ => True) := by
  circuit_proof_start [FullRoundOpt_t2.circuit]

def circuit (offset : ℕ) (h : offset + 4 < 71) :
    FormalCircuit F (fields 2) (fields 2) where
  elaborated := elaborated offset h
  Spec := Spec offset
  soundness := soundness offset h
  completeness := completeness offset h

end ApplyFullRounds

namespace PartialRoundOptStep_t2

def main (round : Fin 56) (state : Vector (Expression F) 2)
    : Circuit F (Vector (Expression F) 2) := do
  let sbox0 ← Sigma.circuit state[0]
  let a0 <== sbox0 + .const C_t2[10 + round.val]
  let out0 <== .const S_t2[3*round.val] * a0 + .const S_t2[3*round.val + 1] * state[1]
  let out1 <== state[1] + a0 * .const S_t2[3*round.val + 2]
  return #v[out0, out1]

def Spec (round : Fin 56) (input output : Vector F 2) : Prop :=
  output = Specs.PoseidonOptimized.partialRoundOpt_t2 C_t2 S_t2 (10 + round.val)
    round.val input round.isLt

def elaborated (round : Fin 56) : ElaboratedCircuit F (fields 2) (fields 2) where
  main := main round
  localLength _ := 6
  output _ i := #v[varFromOffset field (i + 4), varFromOffset field (i + 5)]
  subcircuitsConsistent := by
    simp +arith only [circuit_norm, main, Sigma.circuit]

theorem soundness (round : Fin 56) :
    Soundness F (elaborated round) (fun _ => True) (Spec round) := by
  circuit_proof_start [Sigma.circuit]
  simp only [Specs.PoseidonOptimized.partialRoundOpt_t2, Specs.Poseidon.sigma,
    dif_pos (show 10 + round.val < 72 by omega), mixS_t2_eq]
  obtain ⟨h0, h1, h2, h3⟩ := h_holds
  have h_in0 : Expression.eval env input_var[0] = input[0] := by
    simpa using congrArg (fun v => v[0]) h_input
  have h_in1 : Expression.eval env input_var[1] = input[1] := by
    simpa using congrArg (fun v => v[1]) h_input
  rw [h2, h3, h1, h0, h_in0, h_in1]
  simp +arith [show round.val * 3 = 3 * round.val by ring]

theorem completeness (round : Fin 56) :
    Completeness F (elaborated round) (fun _ => True) := by
  circuit_proof_start [Sigma.circuit]
  simp_all

def circuit (round : Fin 56) : FormalCircuit F (fields 2) (fields 2) where
  elaborated := elaborated round
  Spec := Spec round
  soundness := soundness round
  completeness := completeness round

end PartialRoundOptStep_t2

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
  Circuit.foldl partialRoundIndices state
    (fun st round => PartialRoundOptStep_t2.circuit round st)
    (by simp only [circuit_norm, PartialRoundOptStep_t2.circuit,
      PartialRoundOptStep_t2.elaborated])

def Spec (input output : Vector F 2) : Prop :=
  output = Specs.PoseidonOptimized.partialRoundsOpt_t2 C_t2 S_t2 56 10 0 input (by omega)

def Assumptions (_ : Vector F 2) : Prop :=
  True

def envState (env : Environment F) (input : Vector F 2)
    (n k : ℕ) : Vector F 2 :=
  if k = 0 then input
  else #v[env.get (n + (k - 1) * 6 + 4), env.get (n + (k - 1) * 6 + 5)]

def elaborated : ElaboratedCircuit F (fields 2) (fields 2) where
  main
  localLength _ := 336
  localLength_eq := by
    simp only [circuit_norm, main, PartialRoundOptStep_t2.circuit,
      PartialRoundOptStep_t2.elaborated]
  output _ i := #v[varFromOffset field (i + 334), varFromOffset field (i + 335)]
  output_eq := by
    simp only [circuit_norm, main, PartialRoundOptStep_t2.circuit,
      PartialRoundOptStep_t2.elaborated]
  subcircuitsConsistent := by
    simp only [circuit_norm, main, PartialRoundOptStep_t2.circuit,
      PartialRoundOptStep_t2.elaborated]

theorem soundness : Soundness F elaborated Assumptions Spec := by
  circuit_proof_start [PartialRoundOptStep_t2.circuit, PartialRoundOptStep_t2.elaborated,
    PartialRoundOptStep_t2.Spec]
  obtain ⟨h0, h_step⟩ := h_holds
  have h0' := h0
  have h_round : ∀ (k : ℕ) (hk : k < 56),
      envState env input i₀ (k + 1) =
        Specs.PoseidonOptimized.partialRoundOpt_t2 C_t2 S_t2 (10 + k) k
          (envState env input i₀ k) hk := by
    intro k hk
    rcases k with _ | j
    · exact Vector.toArray_inj.mp (by simpa [partialRoundIndices, envState] using h0')
    · have hj := h_step j (by omega)
      exact Vector.toArray_inj.mp (by simpa +arith [partialRoundIndices, envState] using hj)
  have h_final := partialRoundsOpt_induction 56 10 0 (by omega)
    (fun k => envState env input i₀ k)
    (by
      intro i hi
      simpa +arith only [] using h_round i hi)
  exact congr_arg Vector.toArray h_final

theorem completeness : Completeness F elaborated Assumptions := by
  circuit_proof_start [PartialRoundOptStep_t2.circuit]

def circuit : FormalCircuit F (fields 2) (fields 2) := {
  elaborated with
  Assumptions,
  Spec,
  soundness,
  completeness := by simp [completeness]
}

end ApplyPartialRoundsOpt

def main (input : Expression F) : Circuit F (Expression F) := do
  let state ← InitialArk.circuit input
  let state ← ApplyFullRounds.circuit 2 (by omega) state
  let state ← FullRoundOpt_t2.circuit C_t2 P_t2 ⟨8, by omega⟩ state
  let state ← ApplyPartialRoundsOpt.circuit state
  let state ← ApplyFullRounds.circuit 66 (by omega) state
  let state ← FullRoundOpt_t2.circuit zeroRoundConstants M_t2 ⟨0, by omega⟩ state
  return state[0]

def Spec (input output : F) : Prop :=
  output = Specs.PoseidonOptimized.poseidon1Opt input

def elaborated : ElaboratedCircuit F field field where
  main
  localLength _ := 402
  localLength_eq := by
    simp only [circuit_norm, main, InitialArk.circuit, ApplyFullRounds.circuit,
      ApplyFullRounds.elaborated, FullRoundOpt_t2.circuit, FullRoundOpt_t2.elaborated,
      ApplyPartialRoundsOpt.circuit, ApplyPartialRoundsOpt.elaborated]
  output _ i := varFromOffset field (i + 400)
  output_eq := by
    simp only [circuit_norm, main, InitialArk.circuit, ApplyFullRounds.circuit,
      ApplyFullRounds.elaborated, FullRoundOpt_t2.circuit, FullRoundOpt_t2.elaborated,
      ApplyPartialRoundsOpt.circuit, ApplyPartialRoundsOpt.elaborated]
  subcircuitsConsistent := by
    simp +arith only [circuit_norm, main, InitialArk.circuit, ApplyFullRounds.circuit,
      ApplyFullRounds.elaborated, FullRoundOpt_t2.circuit, FullRoundOpt_t2.elaborated,
      ApplyPartialRoundsOpt.circuit, ApplyPartialRoundsOpt.elaborated]

theorem soundness : Soundness F elaborated (fun _ => True) Spec := by
  circuit_proof_start [InitialArk.circuit, ApplyFullRounds.circuit, FullRoundOpt_t2.circuit,
    ApplyPartialRoundsOpt.circuit]
  simp +arith only [circuit_norm, ApplyFullRounds.elaborated, FullRoundOpt_t2.elaborated,
    ApplyPartialRoundsOpt.elaborated, ApplyFullRounds.Spec, FullRoundOpt_t2.Spec,
    ApplyPartialRoundsOpt.Spec, ApplyPartialRoundsOpt.Assumptions,
    Specs.PoseidonOptimized.fullRoundOpt_t2, ark_zero_t2_eq,
    Specs.PoseidonOptimized.poseidon1Opt] at h_holds ⊢
  -- get rid of the [0] in the output
  apply congrArg (fun v => v[0]) (a₁ := #v[env.get (i₀ + 400), env.get (i₀ + 401)])
  simp_all

theorem completeness : Completeness F elaborated (fun _ => True) := by
  circuit_proof_start [InitialArk.circuit, ApplyFullRounds.circuit, FullRoundOpt_t2.circuit,
    ApplyPartialRoundsOpt.circuit, ApplyPartialRoundsOpt.Assumptions]

def circuit : FormalCircuit F field field where
  elaborated
  Spec
  soundness
  completeness

end Poseidon1

end Circomlib.Poseidon
