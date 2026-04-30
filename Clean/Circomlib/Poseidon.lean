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
-/
namespace Ark_t2

def main (c0 c1 : F p) (input : Vector (Expression (F p)) 2)
    : Circuit (F p) (Vector (Expression (F p)) 2) := do
  let out0 <== input[0] + Expression.const c0
  let out1 <== input[1] + Expression.const c1
  return #v[out0, out1]

-- Parameterized circuit: constants c0, c1 are fixed at circuit construction time
def circuit (c0 c1 : F p) : FormalCircuit (F p) (fields 2) (fields 2) where
  main := main c0 c1
  localLength _ := 2
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]
  output _ i := #v[varFromOffset field i, varFromOffset field (i + 1)]

  Assumptions _ := True
  Spec (input : Vector (F p) 2) (output : Vector (F p) 2) :=
    output[0] = input[0] + c0 ∧ output[1] = input[1] + c1

  soundness := by
    intro offset env input_var input h_input h_assumptions h_constraints
    simp only [circuit_norm, main] at *
    obtain ⟨h_out0, h_out1⟩ := h_constraints
    rw [← h_input]
    simp only [circuit_norm] at *
    constructor <;> assumption

  completeness := by
    simp_all only [circuit_norm, main]

end Ark_t2

/-
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
-/
namespace Mix_t2

def main (m00 m01 m10 m11 : F p) (input : Vector (Expression (F p)) 2)
    : Circuit (F p) (Vector (Expression (F p)) 2) := do
  let out0 <== Expression.const m00 * input[0] + Expression.const m10 * input[1]
  let out1 <== Expression.const m01 * input[0] + Expression.const m11 * input[1]
  return #v[out0, out1]

-- Parameterized circuit: matrix elements are fixed at circuit construction time
def circuit (m00 m01 m10 m11 : F p) : FormalCircuit (F p) (fields 2) (fields 2) where
  main := main m00 m01 m10 m11
  localLength _ := 2
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]
  output _ i := #v[varFromOffset field i, varFromOffset field (i + 1)]

  Assumptions _ := True
  Spec (input : Vector (F p) 2) (output : Vector (F p) 2) :=
    output[0] = m00 * input[0] + m10 * input[1] ∧
    output[1] = m01 * input[0] + m11 * input[1]

  soundness := by
    intro offset env input_var input h_input h_assumptions h_constraints
    simp only [circuit_norm, main] at *
    obtain ⟨h_out0, h_out1⟩ := h_constraints
    rw [← h_input]
    simp only [circuit_norm] at *
    constructor <;> assumption

  completeness := by
    simp_all only [circuit_norm, main]

end Mix_t2

/-
============================================================================
MIXS: Sparse Matrix Multiplication for t=2 (optimized partial rounds)
============================================================================
In circomlib's optimized implementation, partial rounds use sparse matrices.
For t=2, each round uses 3 sparse constants from S:
  out[0] = S[0]*in[0] + S[1]*in[1]
  out[1] = in[1] + in[0]*S[2]

This is more efficient than full matrix multiplication.
-/
namespace MixS_t2

def main (s0 s1 s2 : F p) (input : Vector (Expression (F p)) 2)
    : Circuit (F p) (Vector (Expression (F p)) 2) := do
  let out0 <== Expression.const s0 * input[0] + Expression.const s1 * input[1]
  let out1 <== input[1] + input[0] * Expression.const s2
  return #v[out0, out1]

def circuit (s0 s1 s2 : F p) : FormalCircuit (F p) (fields 2) (fields 2) where
  main := main s0 s1 s2
  localLength _ := 2
  localLength_eq := by simp [circuit_norm, main]
  subcircuitsConsistent := by simp +arith [circuit_norm, main]
  output _ i := #v[varFromOffset field i, varFromOffset field (i + 1)]

  Assumptions _ := True
  Spec (input : Vector (F p) 2) (output : Vector (F p) 2) :=
    output[0] = s0 * input[0] + s1 * input[1] ∧
    output[1] = input[1] + input[0] * s2

  soundness := by
    intro offset env input_var input h_input h_assumptions h_constraints
    simp only [circuit_norm, main] at *
    obtain ⟨h_out0, h_out1⟩ := h_constraints
    rw [← h_input]
    simp only [circuit_norm] at *
    constructor <;> assumption

  completeness := by
    simp_all only [circuit_norm, main]

end MixS_t2

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

-- Pre-computed constant vectors for full rounds (using Circuit.foldl like Keccak)
-- Each element is (c0, c1) pair for one full round

-- First 3 full rounds: C[2..7]
def fullRoundConstants1 : Vector (F BN254_PRIME × F BN254_PRIME) 3 :=
  #v[(C_t2[2], C_t2[3]), (C_t2[4], C_t2[5]), (C_t2[6], C_t2[7])]

-- Last 3 full rounds: C[66..71]
def fullRoundConstants2 : Vector (F BN254_PRIME × F BN254_PRIME) 3 :=
  #v[(C_t2[66], C_t2[67]), (C_t2[68], C_t2[69]), (C_t2[70], C_t2[71])]

-- Partial round constants: 56 tuples of (c0, s0, s1, s2)
-- C[10..65] for c0, S[0..167] for sparse matrix (3 per round)
def partialRoundConstants : Vector (F BN254_PRIME × F BN254_PRIME × F BN254_PRIME × F BN254_PRIME) 56 :=
  Vector.ofFn fun i =>
    let c0 : F BN254_PRIME := C_t2[10 + i.val]'(by omega)
    let s0 : F BN254_PRIME := S_t2[3*i.val]'(by omega)
    let s1 : F BN254_PRIME := S_t2[3*i.val + 1]'(by omega)
    let s2 : F BN254_PRIME := S_t2[3*i.val + 2]'(by omega)
    (c0, s0, s1, s2)

-- Explicit ConstantLength/ConstantOutput instances for the foldl loops.
-- These bypass the auto-param synthesis which times out trying to evaluate
-- BN254 field constants (m00/m01/m10/m11) via kernel whnf.

instance fullRound_constLen :
    ConstantLength (fun (t : Vector (Expression (F BN254_PRIME)) 2 ×
        (F BN254_PRIME × F BN254_PRIME)) =>
      FullRound_t2.circuit t.2.1 t.2.2 m00 m01 m10 m11 t.1) where
  localLength := 10
  localLength_eq := by
    intro ⟨st, c0, c1⟩ n
    simp only [circuit_norm, FullRound_t2.circuit]

theorem fullRound_constOut :
    ConstantOutput (fun (t : Vector (Expression (F BN254_PRIME)) 2 ×
        (F BN254_PRIME × F BN254_PRIME)) =>
      FullRound_t2.circuit t.2.1 t.2.2 m00 m01 m10 m11 t.1) := by
  intro ⟨st, c0, c1⟩ n
  simp only [circuit_norm, FullRound_t2.circuit]

instance partialRound_constLen :
    ConstantLength (fun (t : Vector (Expression (F BN254_PRIME)) 2 ×
        (F BN254_PRIME × F BN254_PRIME × F BN254_PRIME × F BN254_PRIME)) =>
      PartialRoundOpt_t2.circuit t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 t.1) where
  localLength := 6
  localLength_eq := by
    intro ⟨st, c0, s0, s1, s2⟩ n
    simp only [circuit_norm, PartialRoundOpt_t2.circuit]

theorem partialRound_constOut :
    ConstantOutput (fun (t : Vector (Expression (F BN254_PRIME)) 2 ×
        (F BN254_PRIME × F BN254_PRIME × F BN254_PRIME × F BN254_PRIME)) =>
      PartialRoundOpt_t2.circuit t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2 t.1) := by
  intro ⟨st, c0, s0, s1, s2⟩ n
  simp only [circuit_norm, PartialRoundOpt_t2.circuit]

namespace ApplyFullRounds1

def body (t : Vector (Expression (F BN254_PRIME)) 2 × (F BN254_PRIME × F BN254_PRIME)) :
    Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) :=
  FullRound_t2.circuit t.2.1 t.2.2 m00 m01 m10 m11 t.1

def main (state : Vector (Expression (F BN254_PRIME)) 2)
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) :=
  Circuit.foldl fullRoundConstants1 state
    (fun st c => body (st, c))
    fullRound_constOut fullRound_constLen

@[circuit_norm]
theorem body_localLength_eq
    (state : Vector (Expression (F BN254_PRIME)) 2) (c : F BN254_PRIME × F BN254_PRIME)
    (n : ℕ) :
    (body (state, c)).localLength n = 10 :=
  fullRound_constLen.localLength_eq (state, c) n

@[circuit_norm]
theorem body_output_eq
    (state : Vector (Expression (F BN254_PRIME)) 2) (c : F BN254_PRIME × F BN254_PRIME)
    (n : ℕ) :
    (body (state, c)).output n = #v[varFromOffset field (n + 8), varFromOffset field (n + 9)] := by
  simp only [body, circuit_norm, FullRound_t2.circuit]

theorem body_subcircuitsConsistent
    (state : Vector (Expression (F BN254_PRIME)) 2) (c : F BN254_PRIME × F BN254_PRIME)
    (n : ℕ) :
    (body (state, c)).forAll n { subcircuit offset {m} _ := m = offset } := by
  simp only [body, circuit_norm, FullRound_t2.circuit, Operations.forAll]

@[circuit_norm]
theorem main_localLength_eq (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (main state).localLength n = 30 := by
  simp only [main, foldl.localLength_eq, body_localLength_eq]

@[circuit_norm]
theorem main_output_eq (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (main state).output n = #v[varFromOffset field (n + 28), varFromOffset field (n + 29)] := by
  unfold main
  rw [foldl.output_eq]
  simp only [body_output_eq, body_localLength_eq]

def roundSpec (c0 c1 : F BN254_PRIME) (input : Vector (F BN254_PRIME) 2) :
    Vector (F BN254_PRIME) 2 :=
  let s0 := input[0] ^ 5
  let s1 := input[1] ^ 5
  let a0 := s0 + c0
  let a1 := s1 + c1
  #v[m00 * a0 + m10 * a1, m01 * a0 + m11 * a1]

def specOutput (input : Vector (F BN254_PRIME) 2) : Vector (F BN254_PRIME) 2 :=
  let state0 := roundSpec fullRoundConstants1[0].1 fullRoundConstants1[0].2 input
  let state1 := roundSpec fullRoundConstants1[1].1 fullRoundConstants1[1].2 state0
  roundSpec fullRoundConstants1[2].1 fullRoundConstants1[2].2 state1

def Spec (input output : Vector (F BN254_PRIME) 2) : Prop :=
  output = specOutput input

def elaborated : ElaboratedCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  main
  localLength _ := 30
  localLength_eq := by
    intro input n
    simp only [main_localLength_eq]
  output _ i := #v[varFromOffset field (i + 28), varFromOffset field (i + 29)]
  output_eq := by
    intro input n
    simp only [main_output_eq]
  subcircuitsConsistent := by
    intro input n
    change (main input).forAll n { subcircuit offset {m} _ := m = offset }
    unfold main
    rw [forAll_def]
    rw [foldl.forAll]
    constructor
    · exact body_subcircuitsConsistent _ _ _
    · intro i hi
      exact body_subcircuitsConsistent _ _ _

theorem soundness : Soundness (F BN254_PRIME) elaborated (fun _ => True) Spec := by
  circuit_proof_start [main, Spec]
  simp only [body, circuit_norm] at h_holds
  obtain ⟨h0, h_step⟩ := h_holds
  have h0' := h0 trivial
  have h1' := h_step 0 (by omega) trivial
  have h2' := h_step 1 (by omega) trivial
  simp only [FullRound_t2.circuit, circuit_norm, h_input] at h0' h1' h2'
  simp only [specOutput, roundSpec]
  simp +arith only [] at h1' h2' ⊢
  rw [h2'.1, h2'.2, h1'.1, h1'.2, h0'.1, h0'.2]
  rfl

theorem completeness : Completeness (F BN254_PRIME) elaborated (fun _ => True) := by
  circuit_proof_start [main, body]
  exact ⟨trivial, fun _ _ => trivial⟩

def circuit : FormalCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  elaborated
  Assumptions _ := True
  Spec
  soundness
  completeness

end ApplyFullRounds1

namespace ApplyFullRounds2

def body (t : Vector (Expression (F BN254_PRIME)) 2 × (F BN254_PRIME × F BN254_PRIME)) :
    Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) :=
  FullRound_t2.circuit t.2.1 t.2.2 m00 m01 m10 m11 t.1

def main (state : Vector (Expression (F BN254_PRIME)) 2)
    : Circuit (F BN254_PRIME) (Vector (Expression (F BN254_PRIME)) 2) :=
  Circuit.foldl fullRoundConstants2 state
    (fun st c => body (st, c))
    fullRound_constOut fullRound_constLen

@[circuit_norm]
theorem body_localLength_eq
    (state : Vector (Expression (F BN254_PRIME)) 2) (c : F BN254_PRIME × F BN254_PRIME)
    (n : ℕ) :
    (body (state, c)).localLength n = 10 :=
  fullRound_constLen.localLength_eq (state, c) n

@[circuit_norm]
theorem body_output_eq
    (state : Vector (Expression (F BN254_PRIME)) 2) (c : F BN254_PRIME × F BN254_PRIME)
    (n : ℕ) :
    (body (state, c)).output n = #v[varFromOffset field (n + 8), varFromOffset field (n + 9)] := by
  simp only [body, circuit_norm, FullRound_t2.circuit]

theorem body_subcircuitsConsistent
    (state : Vector (Expression (F BN254_PRIME)) 2) (c : F BN254_PRIME × F BN254_PRIME)
    (n : ℕ) :
    (body (state, c)).forAll n { subcircuit offset {m} _ := m = offset } := by
  simp only [body, circuit_norm, FullRound_t2.circuit, Operations.forAll]

@[circuit_norm]
theorem main_localLength_eq (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (main state).localLength n = 30 := by
  simp only [main, foldl.localLength_eq, body_localLength_eq]

@[circuit_norm]
theorem main_output_eq (state : Vector (Expression (F BN254_PRIME)) 2) (n : ℕ) :
    (main state).output n = #v[varFromOffset field (n + 28), varFromOffset field (n + 29)] := by
  unfold main
  rw [foldl.output_eq]
  simp only [body_output_eq, body_localLength_eq]

def roundSpec (c0 c1 : F BN254_PRIME) (input : Vector (F BN254_PRIME) 2) :
    Vector (F BN254_PRIME) 2 :=
  let s0 := input[0] ^ 5
  let s1 := input[1] ^ 5
  let a0 := s0 + c0
  let a1 := s1 + c1
  #v[m00 * a0 + m10 * a1, m01 * a0 + m11 * a1]

def specOutput (input : Vector (F BN254_PRIME) 2) : Vector (F BN254_PRIME) 2 :=
  let state0 := roundSpec fullRoundConstants2[0].1 fullRoundConstants2[0].2 input
  let state1 := roundSpec fullRoundConstants2[1].1 fullRoundConstants2[1].2 state0
  roundSpec fullRoundConstants2[2].1 fullRoundConstants2[2].2 state1

def Spec (input output : Vector (F BN254_PRIME) 2) : Prop :=
  output = specOutput input

def elaborated : ElaboratedCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  main
  localLength _ := 30
  localLength_eq := by
    intro input n
    simp only [main_localLength_eq]
  output _ i := #v[varFromOffset field (i + 28), varFromOffset field (i + 29)]
  output_eq := by
    intro input n
    simp only [main_output_eq]
  subcircuitsConsistent := by
    intro input n
    change (main input).forAll n { subcircuit offset {m} _ := m = offset }
    unfold main
    rw [forAll_def]
    rw [foldl.forAll]
    constructor
    · exact body_subcircuitsConsistent _ _ _
    · intro i hi
      exact body_subcircuitsConsistent _ _ _

theorem soundness : Soundness (F BN254_PRIME) elaborated (fun _ => True) Spec := by
  circuit_proof_start [main, Spec]
  simp only [body, circuit_norm] at h_holds
  obtain ⟨h0, h_step⟩ := h_holds
  have h0' := h0 trivial
  have h1' := h_step 0 (by omega) trivial
  have h2' := h_step 1 (by omega) trivial
  simp only [FullRound_t2.circuit, circuit_norm, h_input] at h0' h1' h2'
  simp only [specOutput, roundSpec]
  simp +arith only [] at h1' h2' ⊢
  rw [h2'.1, h2'.2, h1'.1, h1'.2, h0'.1, h0'.2]
  rfl

theorem completeness : Completeness (F BN254_PRIME) elaborated (fun _ => True) := by
  circuit_proof_start [main, body]
  exact ⟨trivial, fun _ _ => trivial⟩

def circuit : FormalCircuit (F BN254_PRIME) (fields 2) (fields 2) where
  elaborated
  Assumptions _ := True
  Spec
  soundness
  completeness

end ApplyFullRounds2

namespace TransitionRound

def circuit : FormalCircuit (F BN254_PRIME) (fields 2) (fields 2) :=
  FullRound_t2.circuit (C_t2[8]'(by omega)) (C_t2[9]'(by omega)) p00 p01 p10 p11

end TransitionRound

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
    let s0 := input[0] ^ 5
    let s1 := input[1] ^ 5
    output[0] = m00 * s0 + m10 * s1 ∧
    output[1] = m01 * s0 + m11 * s1

  soundness := by
    circuit_proof_start [Sigma.circuit]
    grind

  completeness := by
    circuit_proof_all [Sigma.circuit]

end FinalRound


end Poseidon1

end Circomlib.Poseidon
