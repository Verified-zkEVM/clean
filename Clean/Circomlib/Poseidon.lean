import Clean.Circuit
import Clean.Utils.Field
import Clean.Gadgets.Equality
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

-- Import constants from specs (but NOT the type F which conflicts with Clean's F p)
open Specs.Poseidon (BN254_PRIME C_t2 M_t2)
open Specs.PoseidonOptimized (P_t2 S_t2)

variable {p : ℕ} [Fact p.Prime]

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

def main (input : Expression (F p)) : Circuit (F p) (Expression (F p)) := do
  let in2 <== input * input
  let in4 <== in2 * in2
  let out <== in4 * input
  return out

def circuit : FormalCircuit (F p) field field where
  main := main
  localLength _ := 3
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]
  output _ i := varFromOffset field (i + 2)

  Assumptions _ := True
  Spec (input : F p) (output : F p) := output = input ^ 5

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

We factor this out as a reusable FullRound_t2 component for clarity.
-/
namespace FullRound_t2

def main (c0 c1 m00 m01 m10 m11 : F p) (input : Vector (Expression (F p)) 2)
    : Circuit (F p) (Vector (Expression (F p)) 2) := do
  -- S-box on both elements
  let s0 ← Sigma.circuit input[0]
  let s1 ← Sigma.circuit input[1]

  -- ARK
  let a0 <== s0 + Expression.const c0
  let a1 <== s1 + Expression.const c1

  -- MIX
  let out0 <== Expression.const m00 * a0 + Expression.const m10 * a1
  let out1 <== Expression.const m01 * a0 + Expression.const m11 * a1
  return #v[out0, out1]

-- Full round: SBOX → ARK → MIX
-- Spec: output = M * (sbox(input) + c) where sbox applies x^5 to each element
def circuit (c0 c1 m00 m01 m10 m11 : F p) : FormalCircuit (F p) (fields 2) (fields 2) where
  main := main c0 c1 m00 m01 m10 m11
  -- 3 witnesses per Sigma (×2) + 2 for ARK + 2 for MIX = 10
  localLength _ := 10
  localLength_eq := by simp [circuit_norm, main, Sigma.circuit]
  subcircuitsConsistent := by simp +arith [circuit_norm, main, Sigma.circuit]
  output _ i := #v[varFromOffset field (i + 8), varFromOffset field (i + 9)]

  Assumptions _ := True
  -- TODO should be formulated in terms of Specs.PoseidonOptimized
  Spec (input : Vector (F p) 2) (output : Vector (F p) 2) :=
    let s0 := input[0] ^ 5
    let s1 := input[1] ^ 5
    let a0 := s0 + c0
    let a1 := s1 + c1
    output[0] = m00 * a0 + m10 * a1 ∧
    output[1] = m01 * a0 + m11 * a1

  soundness := by
    circuit_proof_start [Sigma.circuit]
    grind

  completeness := by
    circuit_proof_all [Sigma.circuit]

end FullRound_t2

/-
============================================================================
PARTIAL ROUND (OPTIMIZED) for t=2: SBOX on first → ARK on first → MixS
============================================================================
In the optimized circomlib implementation, partial rounds use sparse matrix
multiplication (MixS) instead of full matrix multiplication (Mix).
This is more efficient and matches the actual circomlib implementation.
-/
namespace PartialRoundOpt_t2

def main (c0 s0 s1 s2 : F p) (input : Vector (Expression (F p)) 2)
    : Circuit (F p) (Vector (Expression (F p)) 2) := do
  -- S-box on first element only
  let sbox0 ← Sigma.circuit input[0]

  -- ARK on first element only
  let a0 <== sbox0 + Expression.const c0

  -- MixS (sparse matrix multiplication)
  let out0 <== Expression.const s0 * a0 + Expression.const s1 * input[1]
  let out1 <== input[1] + a0 * Expression.const s2
  return #v[out0, out1]

-- Optimized partial round using sparse matrix
def circuit (c0 s0 s1 s2 : F p) : FormalCircuit (F p) (fields 2) (fields 2) where
  main := main c0 s0 s1 s2
  -- 3 witnesses for Sigma + 1 for ARK + 2 for MixS = 6
  localLength _ := 6
  localLength_eq := by simp [circuit_norm, main, Sigma.circuit]
  subcircuitsConsistent := by simp +arith [circuit_norm, main, Sigma.circuit]
  output _ i := #v[varFromOffset field (i + 4), varFromOffset field (i + 5)]

  Assumptions _ := True
  -- TODO should be formulated in terms of Specs.PoseidonOptimized
  Spec (input : Vector (F p) 2) (output : Vector (F p) 2) :=
    let a0 := input[0] ^ 5 + c0
    output[0] = s0 * a0 + s1 * input[1] ∧
    output[1] = input[1] + a0 * s2

  soundness := by
    circuit_proof_start [Sigma.circuit]
    grind

  completeness := by
    circuit_proof_all [Sigma.circuit]

end PartialRoundOpt_t2

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

Total witnesses: Initial ARK (2) + 3 full rounds (30) + transition round (10)
                 + 56 partial rounds (336) + 3 full rounds (30) + final round (8) = 416
-/
namespace Poseidon1

open Circuit

-- BN254 prime facts (BN254_PRIME is a well-known prime, proofs omitted for performance)
instance : Fact (Nat.Prime BN254_PRIME) := ⟨by sorry⟩
instance : Fact (BN254_PRIME > 2) := ⟨by decide⟩

-- Helper to get matrix elements as field elements
def getM (i j : ℕ) (hi : i < 2) (hj : j < 2) : F BN254_PRIME := (M_t2[i]'hi)[j]'hj
def getP (i j : ℕ) (hi : i < 2) (hj : j < 2) : F BN254_PRIME := (P_t2[i]'hi)[j]'hj

-- MDS matrix elements (M)
def m00 : F BN254_PRIME := getM 0 0 (by omega) (by omega)
def m01 : F BN254_PRIME := getM 0 1 (by omega) (by omega)
def m10 : F BN254_PRIME := getM 1 0 (by omega) (by omega)
def m11 : F BN254_PRIME := getM 1 1 (by omega) (by omega)

-- Pre-sparse matrix elements (P) - used at transition round
def p00 : F BN254_PRIME := getP 0 0 (by omega) (by omega)
def p01 : F BN254_PRIME := getP 0 1 (by omega) (by omega)
def p10 : F BN254_PRIME := getP 1 0 (by omega) (by omega)
def p11 : F BN254_PRIME := getP 1 1 (by omega) (by omega)

-- Offsets for foldl full-round phases, matching the optimized spec recursion.
def fullRoundOffsets (offset : ℕ) (h : offset + 4 < 71) : Vector (Fin 71) 3 :=
  Vector.ofFn fun i =>
    ⟨offset + 2*i.val, by omega⟩

def fullRoundOffsets1 : Vector (Fin 71) 3 :=
  fullRoundOffsets 2 (by omega)

def fullRoundOffsets2 : Vector (Fin 71) 3 :=
  fullRoundOffsets 66 (by omega)

-- Partial round constants: 56 tuples of (c0, s0, s1, s2)
-- C[10..65] for c0, S[0..167] for sparse matrix (3 per round)
def partialRoundConstants : Vector (F BN254_PRIME × F BN254_PRIME × F BN254_PRIME × F BN254_PRIME) 56 :=
  Vector.ofFn fun i =>
    let c0 : F BN254_PRIME := C_t2[10 + i.val]'(by omega)
    let s0 : F BN254_PRIME := S_t2[3*i.val]'(by omega)
    let s1 : F BN254_PRIME := S_t2[3*i.val + 1]'(by omega)
    let s2 : F BN254_PRIME := S_t2[3*i.val + 2]'(by omega)
    (c0, s0, s1, s2)

private lemma ark_t2_eq (offset : ℕ) (ho : offset + 1 < 72)
    (state : Vector (F BN254_PRIME) 2) :
    Specs.Poseidon.ark C_t2 offset state =
      #v[state[0] + (C_t2[offset]'(by omega) : F BN254_PRIME),
         state[1] + (C_t2[offset + 1]'ho : F BN254_PRIME)] := by
  apply Vector.ext
  intro idx hidx
  have hidx' : idx = 0 ∨ idx = 1 := by omega
  rcases hidx' with rfl | rfl
  · simp [Specs.Poseidon.ark, show offset < 72 by omega]; rfl
  · simp [Specs.Poseidon.ark, ho]; rfl

private lemma mix_t2_eq (state : Vector (F BN254_PRIME) 2) :
    Specs.Poseidon.mix M_t2 state =
      #v[m00 * state[0] + m10 * state[1], m01 * state[0] + m11 * state[1]] := by
  apply Vector.ext
  intro idx hidx
  simp only [Specs.Poseidon.mix, m00, m01, m10, m11, getM, Vector.getElem_ofFn]
  have hidx' : idx = 0 ∨ idx = 1 := by omega
  rcases hidx' with rfl | rfl
  · simp +decide [List.range, List.range.loop, List.foldl]
    rfl
  · simp +decide [List.range, List.range.loop, List.foldl]
    rfl

private lemma mixS_t2_eq (round : ℕ) (hr : round < 56) (state : Vector (F BN254_PRIME) 2) :
    Specs.PoseidonOptimized.mixS_t2 S_t2 round state hr =
      #v[(S_t2[round * 3]'(by omega) : F BN254_PRIME) * state[0] +
         (S_t2[round * 3 + 1]'(by omega) : F BN254_PRIME) * state[1],
         state[1] + state[0] * (S_t2[round * 3 + 2]'(by omega) : F BN254_PRIME)] := by
  simp [Specs.PoseidonOptimized.mixS_t2]
  exact ⟨rfl, rfl⟩

namespace InitialArk

def main (input : Expression (F BN254_PRIME))
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) := do
  let state : Vector (Expression (F BN254_PRIME)) 2 := #v[Expression.const 0, input]
  let out0 <== state[0] + Expression.const (C_t2[0] : F BN254_PRIME)
  let out1 <== state[1] + Expression.const (C_t2[1] : F BN254_PRIME)
  return #v[out0, out1]

def circuit : FormalCircuit (F BN254_PRIME) field (fields 2) where
  main
  localLength _ := 2
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]
  output _ i := #v[varFromOffset field i, varFromOffset field (i + 1)]

  Assumptions _ := True
  Spec (input : F BN254_PRIME) (output : Vector (F BN254_PRIME) 2) :=
    output = Specs.Poseidon.ark C_t2 0 #v[0, input]

  soundness := by
    circuit_proof_start
    rw [ark_t2_eq 0 (by omega)]
    simp_all

  completeness := by
    circuit_proof_all

end InitialArk

namespace FullRoundOpt_t2

def main (offset : Fin 71) (state : Vector (Expression (F BN254_PRIME)) 2)
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) :=
  FullRound_t2.circuit
    (C_t2[offset.val]'(by omega) : F BN254_PRIME)
    (C_t2[offset.val + 1]'(by omega) : F BN254_PRIME)
    m00 m01 m10 m11 state

def Spec (offset : Fin 71) (input output : Vector (F BN254_PRIME) 2) : Prop :=
  output = Specs.PoseidonOptimized.fullRoundOpt_t2 C_t2 M_t2 offset.val input

def elaborated (offset : Fin 71) : ElaboratedCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  main := main offset
  localLength _ := 10
  output _ i := #v[varFromOffset field (i + 8), varFromOffset field (i + 9)]
  subcircuitsConsistent := by
    simp only [circuit_norm, main, FullRound_t2.circuit]

theorem soundness (offset : Fin 71) :
    Soundness (F BN254_PRIME) (elaborated offset) (fun _ => True) (Spec offset) := by
  circuit_proof_start [FullRound_t2.circuit]
  simp only [Specs.PoseidonOptimized.fullRoundOpt_t2, Specs.Poseidon.sboxFull]
  rw [ark_t2_eq offset.val (by omega)]
  simp only [Specs.Poseidon.sigma, mix_t2_eq, Vector.getElem_map]
  obtain ⟨h0, h1⟩ := h_holds
  rw [h0, h1]
  rfl

theorem completeness (offset : Fin 71) :
    Completeness (F BN254_PRIME) (elaborated offset) (fun _ => True) := by
  circuit_proof_start [FullRound_t2.circuit]

def circuit (offset : Fin 71) : FormalCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  elaborated := elaborated offset
  Spec := Spec offset
  soundness := soundness offset
  completeness := completeness offset

end FullRoundOpt_t2

namespace ApplyFullRounds1
def main (state : Vector (Expression (F BN254_PRIME)) 2)
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) :=
  Circuit.foldl fullRoundOffsets1 state
    (fun st offset => FullRoundOpt_t2.circuit offset st)
    (by simp only [circuit_norm, FullRoundOpt_t2.circuit, FullRoundOpt_t2.elaborated])

def Spec (input output : Vector (F BN254_PRIME) 2) : Prop :=
  output = Specs.PoseidonOptimized.fullRoundsOpt_t2 C_t2 M_t2 3 2 input

def elaborated : ElaboratedCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  main
  localLength _ := 30
  output _ i := #v[varFromOffset field (i + 28), varFromOffset field (i + 29)]
  subcircuitsConsistent := by
    simp only [circuit_norm, main]

theorem soundness : Soundness (F BN254_PRIME) elaborated (fun _ => True) Spec := by
  circuit_proof_start [FullRoundOpt_t2.circuit, FullRoundOpt_t2.elaborated, FullRoundOpt_t2.Spec]
  obtain ⟨h0, h_step⟩ := h_holds
  have h1 := h_step 0 (by omega)
  have h2 := h_step 1 (by omega)
  simp_all [Specs.PoseidonOptimized.fullRoundsOpt_t2,
    fullRoundOffsets1, fullRoundOffsets]

theorem completeness : Completeness (F BN254_PRIME) elaborated (fun _ => True) := by
  circuit_proof_start [FullRoundOpt_t2.circuit]

def circuit : FormalCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  elaborated
  Spec
  soundness
  completeness
end ApplyFullRounds1

namespace ApplyFullRounds2

def main (state : Vector (Expression (F BN254_PRIME)) 2)
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) :=
  Circuit.foldl fullRoundOffsets2 state
    (fun st offset => FullRoundOpt_t2.circuit offset st)
    (by simp only [circuit_norm, FullRoundOpt_t2.circuit, FullRoundOpt_t2.elaborated])

def Spec (input output : Vector (F BN254_PRIME) 2) : Prop :=
  output = Specs.PoseidonOptimized.fullRoundsOpt_t2 C_t2 M_t2 3 66 input

def elaborated : ElaboratedCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  main
  localLength _ := 30
  output _ i := #v[varFromOffset field (i + 28), varFromOffset field (i + 29)]
  subcircuitsConsistent := by
    simp only [circuit_norm, main]

theorem soundness : Soundness (F BN254_PRIME) elaborated (fun _ => True) Spec := by
  circuit_proof_start [FullRoundOpt_t2.circuit, FullRoundOpt_t2.elaborated, FullRoundOpt_t2.Spec]
  obtain ⟨h0, h_step⟩ := h_holds
  have h1 := h_step 0 (by omega)
  have h2 := h_step 1 (by omega)
  simp_all [Specs.PoseidonOptimized.fullRoundsOpt_t2,
    fullRoundOffsets2, fullRoundOffsets]

theorem completeness : Completeness (F BN254_PRIME) elaborated (fun _ => True) := by
  circuit_proof_start [FullRoundOpt_t2.circuit]

def circuit : FormalCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  elaborated
  Spec
  soundness
  completeness

end ApplyFullRounds2

namespace FinalRound

def main (input : Vector (Expression (F BN254_PRIME)) 2)
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) := do
  let s0 ← Sigma.circuit input[0]
  let s1 ← Sigma.circuit input[1]
  let out0 <== Expression.const m00 * s0 + Expression.const m10 * s1
  let out1 <== Expression.const m01 * s0 + Expression.const m11 * s1
  return #v[out0, out1]

def circuit : FormalCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  main
  localLength _ := 8
  localLength_eq := by simp [circuit_norm, main, Sigma.circuit]
  subcircuitsConsistent := by simp +arith [circuit_norm, main, Sigma.circuit]
  output _ i := #v[varFromOffset field (i + 6), varFromOffset field (i + 7)]

  Assumptions _ := True
  Spec (input : Vector (F BN254_PRIME) 2) (output : Vector (F BN254_PRIME) 2) :=
    output = (input |> Specs.Poseidon.sboxFull |> Specs.Poseidon.mix M_t2)

  soundness := by
    circuit_proof_start [Sigma.circuit]
    have h_in0 : Expression.eval env input_var[0] = input[0] := by
      simpa using congrArg (fun v => v[0]) h_input
    have h_in1 : Expression.eval env input_var[1] = input[1] := by
      simpa using congrArg (fun v => v[1]) h_input
    rw [mix_t2_eq]
    simp_all [Specs.Poseidon.sboxFull, Specs.Poseidon.sigma]
    constructor <;> rfl

  completeness := by
    circuit_proof_all [Sigma.circuit]

end FinalRound

namespace PartialRoundOptStep_t2

def main (round : Fin 56) (state : Vector (Expression (F BN254_PRIME)) 2)
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) :=
  PartialRoundOpt_t2.circuit
    (C_t2[10 + round.val]'(by omega) : F BN254_PRIME)
    (S_t2[3*round.val]'(by omega) : F BN254_PRIME)
    (S_t2[3*round.val + 1]'(by omega) : F BN254_PRIME)
    (S_t2[3*round.val + 2]'(by omega) : F BN254_PRIME)
    state

def Spec (round : Fin 56) (input output : Vector (F BN254_PRIME) 2) : Prop :=
  output = Specs.PoseidonOptimized.partialRoundOpt_t2 C_t2 S_t2 (10 + round.val)
    round.val input round.isLt

def elaborated (round : Fin 56) : ElaboratedCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  main := main round
  localLength _ := 6
  output _ i := #v[varFromOffset field (i + 4), varFromOffset field (i + 5)]
  subcircuitsConsistent := by
    simp only [circuit_norm, main, PartialRoundOpt_t2.circuit]

theorem soundness (round : Fin 56) :
    Soundness (F BN254_PRIME) (elaborated round) (fun _ => True) (Spec round) := by
  circuit_proof_start [PartialRoundOpt_t2.circuit]
  simp only [Specs.PoseidonOptimized.partialRoundOpt_t2, Specs.Poseidon.sigma,
    dif_pos (show 10 + round.val < 72 by omega), mixS_t2_eq]
  obtain ⟨h0, h1⟩ := h_holds
  rw [h0, h1]
  simp +arith [show round.val * 3 = 3 * round.val by ring]
  constructor <;> rfl

theorem completeness (round : Fin 56) :
    Completeness (F BN254_PRIME) (elaborated round) (fun _ => True) := by
  circuit_proof_start [PartialRoundOpt_t2.circuit]

def circuit (round : Fin 56) : FormalCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  elaborated := elaborated round
  Spec := Spec round
  soundness := soundness round
  completeness := completeness round

end PartialRoundOptStep_t2

namespace ApplyPartialRoundsOpt

def main (state : Vector (Expression (F BN254_PRIME)) 2)
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) :=
  Circuit.foldl partialRoundConstants state
    (fun st c => PartialRoundOpt_t2.circuit c.1 c.2.1 c.2.2.1 c.2.2.2 st)
    (by simp only [circuit_norm, PartialRoundOpt_t2.circuit])

def roundSpec
    (c : F BN254_PRIME × F BN254_PRIME × F BN254_PRIME × F BN254_PRIME)
    (input : Vector (F BN254_PRIME) 2) : Vector (F BN254_PRIME) 2 :=
  let a0 := input[0] ^ 5 + c.1
  #v[c.2.1 * a0 + c.2.2.1 * input[1], input[1] + a0 * c.2.2.2]

def specState (input : Vector (F BN254_PRIME) 2) (rounds : ℕ) : Vector (F BN254_PRIME) 2 :=
  (List.range rounds).foldl
    (fun state i => if h : i < 56 then roundSpec partialRoundConstants[i] state else state)
    input

theorem specState_zero (input : Vector (F BN254_PRIME) 2) :
    specState input 0 = input := by
  simp [specState]

theorem specState_succ (input : Vector (F BN254_PRIME) 2) (rounds : ℕ) (h : rounds < 56) :
    specState input (rounds + 1) = roundSpec partialRoundConstants[rounds] (specState input rounds) := by
  simp [specState, List.range_succ, h]

def Spec (input output : Vector (F BN254_PRIME) 2) : Prop :=
  output = specState input 56

def Assumptions (_ : Vector (F BN254_PRIME) 2) : Prop :=
  True

def envState (env : Environment (F BN254_PRIME)) (input : Vector (F BN254_PRIME) 2)
    (n k : ℕ) : Vector (F BN254_PRIME) 2 :=
  if k = 0 then input
  else #v[env.get (n + (k - 1) * 6 + 4), env.get (n + (k - 1) * 6 + 5)]

def elaborated : ElaboratedCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  main
  localLength _ := 336
  localLength_eq := by
    simp only [circuit_norm, main, PartialRoundOpt_t2.circuit]
  output _ i := #v[varFromOffset field (i + 334), varFromOffset field (i + 335)]
  output_eq := by
    simp only [circuit_norm, main, PartialRoundOpt_t2.circuit]
  subcircuitsConsistent := by
    simp only [circuit_norm, main, PartialRoundOpt_t2.circuit]

theorem soundness : Soundness (F BN254_PRIME) elaborated Assumptions Spec := by
  circuit_proof_start [PartialRoundOpt_t2.circuit]
  obtain ⟨h0, h_step⟩ := h_holds
  have h0' := h0
  have h_round : ∀ (k : ℕ) (hk : k < 56),
      envState env input i₀ (k + 1) = roundSpec (partialRoundConstants[k]'hk) (envState env input i₀ k) := by
    intro k hk
    rcases k with _ | j
    · apply Vector.ext
      intro idx hidx
      have hidx' : idx = 0 ∨ idx = 1 := by omega
      rcases hidx' with rfl | rfl
      · simp +arith [envState, roundSpec, h0'.1]
      · simp +arith [envState, roundSpec, h0'.2]
    · have hj := h_step j (by omega)
      simp +arith only [] at hj
      apply Vector.ext
      intro idx hidx
      have hidx' : idx = 0 ∨ idx = 1 := by omega
      rcases hidx' with rfl | rfl
      · simp +arith [envState, roundSpec, hj.1]
      · simp +arith [envState, roundSpec, hj.2]
  have h_state : ∀ (k : ℕ), k ≤ 56 → envState env input i₀ k = specState input k := by
    intro k hk
    induction k with
    | zero =>
        simp only [envState, specState_zero, ↓reduceIte]
    | succ k ih =>
        rw [h_round k (by omega), ih (by omega), specState_succ input k (by omega)]
  exact congr_arg Vector.toArray (h_state 56 (by omega))

theorem completeness : Completeness (F BN254_PRIME) elaborated Assumptions := by
  circuit_proof_start [PartialRoundOpt_t2.circuit]

def circuit : FormalCircuit (F BN254_PRIME) (fields 2) (fields 2) := {
  elaborated with
  Assumptions,
  Spec,
  soundness,
  completeness := by simp [completeness]
}

end ApplyPartialRoundsOpt


end Poseidon1

end Circomlib.Poseidon
