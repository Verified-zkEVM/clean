/-
Optimized Poseidon Hash Function Specification

This file contains the optimized version of Poseidon that matches circomlib's
structure exactly, using P matrix for transition and S sparse matrix for partial rounds.
Constants are in PoseidonConstants.lean.

This is intended for circuit formalization where structure matching simplifies proofs.
For mathematical reasoning, use the simpler Poseidon.lean spec.
-/
module

public import Clean.Specs.Poseidon

public meta import Clean.Specs.Poseidon

@[expose] public section

namespace Specs.PoseidonOptimized

open Specs.Poseidon (F BN254_PRIME sigma ark sboxFull mix C_t2 M_t2 C_t3 M_t3 C_t4 M_t4)

/-- Constants and round parameters for an optimized Poseidon permutation of
state width `t`. The vector lengths encode the relationships used by
circomlib's optimized round schedule. -/
structure Params (t : ℕ) where
  nPartial : ℕ
  C : Vector ℕ (8 * t + nPartial)
  M : Vector (Vector ℕ t) t
  P : Vector (Vector ℕ t) t
  S : Vector ℕ (nPartial * (2 * t - 1))
  two_le_width : 2 ≤ t

/-- Optimized circomlib parameters for one input and state width 2. -/
def params_t2 : Params 2 where
  nPartial := 56
  C := C_t2
  M := M_t2
  P := P_t2
  S := S_t2
  two_le_width := by omega

/-- Optimized circomlib parameters for two inputs and state width 3. -/
def params_t3 : Params 3 where
  nPartial := 57
  C := C_t3
  M := M_t3
  P := P_t3
  S := S_t3
  two_le_width := by omega

/-- Optimized circomlib parameters for three inputs and state width 4. -/
def params_t4 : Params 4 where
  nPartial := 56
  C := C_t4
  M := M_t4
  P := P_t4
  S := S_t4
  two_le_width := by omega

/-- Optimized circomlib parameters for four inputs and state width 5. -/
def params_t5 : Params 5 where
  nPartial := 60
  C := Specs.Poseidon.C_t5
  M := Specs.Poseidon.M_t5
  P := P_t5
  S := S_t5
  two_le_width := by omega

/-- Optimized circomlib parameters for five inputs and state width 6. -/
def params_t6 : Params 6 where
  nPartial := 60
  C := Specs.Poseidon.C_t6
  M := Specs.Poseidon.M_t6
  P := P_t6
  S := S_t6
  two_le_width := by omega

/-- Optimized circomlib parameters for six inputs and state width 7. -/
def params_t7 : Params 7 where
  nPartial := 63
  C := Specs.Poseidon.C_t7
  M := Specs.Poseidon.M_t7
  P := P_t7
  S := S_t7
  two_le_width := by omega

/-- Optimized circomlib parameters for seven inputs and state width 8. -/
def params_t8 : Params 8 where
  nPartial := 64
  C := Specs.Poseidon.C_t8
  M := Specs.Poseidon.M_t8
  P := P_t8
  S := S_t8
  two_le_width := by omega

/-- Optimized circomlib parameters for eight inputs and state width 9. -/
def params_t9 : Params 9 where
  nPartial := 63
  C := Specs.Poseidon.C_t9
  M := Specs.Poseidon.M_t9
  P := P_t9
  S := S_t9
  two_le_width := by omega

/-- Optimized circomlib parameters for nine inputs and state width 10. -/
def params_t10 : Params 10 where
  nPartial := 60
  C := Specs.Poseidon.C_t10
  M := Specs.Poseidon.M_t10
  P := P_t10
  S := S_t10
  two_le_width := by omega

/-- Optimized circomlib parameters for ten inputs and state width 11. -/
def params_t11 : Params 11 where
  nPartial := 66
  C := Specs.Poseidon.C_t11
  M := Specs.Poseidon.M_t11
  P := P_t11
  S := S_t11
  two_le_width := by omega

/-- Optimized circomlib parameters for eleven inputs and state width 12. -/
def params_t12 : Params 12 where
  nPartial := 60
  C := Specs.Poseidon.C_t12
  M := Specs.Poseidon.M_t12
  P := P_t12
  S := S_t12
  two_le_width := by omega

/-- Optimized circomlib parameters for twelve inputs and state width 13. -/
def params_t13 : Params 13 where
  nPartial := 65
  C := Specs.Poseidon.C_t13
  M := Specs.Poseidon.M_t13
  P := P_t13
  S := S_t13
  two_le_width := by omega

/-- Optimized circomlib parameters for thirteen inputs and state width 14. -/
def params_t14 : Params 14 where
  nPartial := 70
  C := Specs.Poseidon.C_t14
  M := Specs.Poseidon.M_t14
  P := P_t14
  S := S_t14
  two_le_width := by omega

/-- Optimized circomlib parameters for fourteen inputs and state width 15. -/
def params_t15 : Params 15 where
  nPartial := 60
  C := Specs.Poseidon.C_t15
  M := Specs.Poseidon.M_t15
  P := P_t15
  S := S_t15
  two_le_width := by omega

/-- Optimized circomlib parameters for fifteen inputs and state width 16. -/
def params_t16 : Params 16 where
  nPartial := 64
  C := Specs.Poseidon.C_t16
  M := Specs.Poseidon.M_t16
  P := P_t16
  S := S_t16
  two_le_width := by omega

/-- Optimized circomlib parameters for sixteen inputs and state width 17. -/
def params_t17 : Params 17 where
  nPartial := 68
  C := Specs.Poseidon.C_t17
  M := Specs.Poseidon.M_t17
  P := P_t17
  S := S_t17
  two_le_width := by omega

lemma sparseIndex_lt {t n round i : ℕ} (hr : round < n)
    (hi : i < 2 * t - 1) :
    round * (2 * t - 1) + i < n * (2 * t - 1) := by
  have hstride : 0 < 2 * t - 1 := by omega
  have hround : round + 1 ≤ n := by omega
  calc
    round * (2 * t - 1) + i < round * (2 * t - 1) + (2 * t - 1) := by omega
    _ = (round + 1) * (2 * t - 1) := by rw [Nat.add_mul]; simp
    _ ≤ n * (2 * t - 1) := Nat.mul_le_mul_right (2 * t - 1) hround

/-- The `2 * t - 1` sparse-matrix constants used by one partial round. -/
def sparseRoundConstants {t : ℕ} (params : Params t)
    (round : Fin params.nPartial) : Vector ℕ (2 * t - 1) :=
  Vector.ofFn fun i =>
    params.S[round.val * (2 * t - 1) + i.val]'(
      sparseIndex_lt round.isLt i.isLt)

/-- Sparse matrix multiplication for an optimized Poseidon partial round. -/
def mixS {t : ℕ} (params : Params t) (round : Fin params.nPartial)
    (state : Vector F t) : Vector F t :=
  let constants := sparseRoundConstants params round
  let first := Fin.foldl t (fun acc j =>
    acc + (constants[j.val]'(by omega) : F) * state[j.val]) 0
  Vector.ofFn fun i =>
    if hi : i.val = 0 then
      first
    else
      state[i] + state[0]'(by omega) *
        (constants[t + i.val - 1]'(by omega) : F)

/-- Apply a dense Poseidon round with the selected mixing matrix. This covers
both ordinary full rounds using `M` and the transition round using `P`. -/
def denseRound {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t)
    (offset : ℕ) (state : Vector F t) : Vector F t :=
  state |> sboxFull |> ark params.C offset |> mix matrix

/-- Apply an optimized full round using the ordinary MDS matrix `M`. -/
def fullRound {t : ℕ} (params : Params t) (offset : ℕ)
    (state : Vector F t) : Vector F t :=
  denseRound params params.M offset state

/-- Apply `nRounds` dense rounds using the selected mixing matrix. -/
def denseRounds {t : ℕ} (params : Params t) (matrix : Vector (Vector ℕ t) t)
    (nRounds offset : ℕ) (state : Vector F t) : Vector F t :=
  match nRounds with
  | 0 => state
  | r + 1 =>
    denseRounds params matrix r (offset + t) (denseRound params matrix offset state)

/-- Apply `nRounds` optimized full rounds using the ordinary MDS matrix `M`. -/
def fullRounds {t : ℕ} (params : Params t) (nRounds offset : ℕ)
    (state : Vector F t) : Vector F t :=
  denseRounds params params.M nRounds offset state

/-- Apply one optimized partial round: S-box and ARK on coordinate zero,
followed by sparse matrix multiplication. -/
def partialRound {t : ℕ} (params : Params t) (cOffset sRound : ℕ)
    (state : Vector F t) (hr : sRound < params.nPartial) : Vector F t :=
  let state' := Vector.ofFn fun i =>
    if hi : i.val = 0 then
      if hc : cOffset < 8 * t + params.nPartial then
        sigma (state[0]'(by omega)) + (params.C[cOffset]'hc : F)
      else
        sigma (state[0]'(by omega))
    else
      state[i]
  mixS params ⟨sRound, hr⟩ state'

/-- Apply `nRounds` consecutive optimized partial rounds. -/
def partialRounds {t : ℕ} (params : Params t) (nRounds cOffset sRound : ℕ)
    (state : Vector F t) (hr : sRound + nRounds ≤ params.nPartial) : Vector F t :=
  match nRounds with
  | 0 => state
  | r + 1 =>
    have hr' : sRound < params.nPartial := by omega
    have hr'' : sRound + 1 + r ≤ params.nPartial := by omega
    partialRounds params r (cOffset + 1) (sRound + 1)
      (partialRound params cOffset sRound state hr') hr''

/-- Initial Poseidon state with capacity element zero followed by the inputs. -/
def initialState {t : ℕ} (inputs : Vector F (t - 1)) : Vector F t :=
  Vector.ofFn fun i =>
    if hi : i.val = 0 then
      0
    else
      inputs[i.val - 1]'(by omega)

/-- The optimized circomlib Poseidon permutation for arbitrary supported state
width. -/
def permutation {t : ℕ} (params : Params t)
    (inputs : Vector F (t - 1)) : Vector F t :=
  let state := initialState inputs
  let state := ark params.C 0 state
  let state := fullRounds params 3 t state
  let state := denseRound params params.P (4 * t) state
  let state := partialRounds params params.nPartial (5 * t) 0 state (by omega)
  let state := fullRounds params 3 (5 * t + params.nPartial) state
  state |> sboxFull |> mix params.M

/-- The first output of the optimized circomlib Poseidon permutation. -/
def poseidon {t : ℕ} (params : Params t) (inputs : Vector F (t - 1)) : F :=
  (permutation params inputs)[0]'(by have := params.two_le_width; omega)

/-
============================================================================
SPARSE MATRIX MULTIPLICATION (MixS)
Matches circomlib's MixS template exactly
============================================================================
-/

-- MixS: Sparse matrix multiplication for partial rounds
-- For t=2: out[0] = S[0]*in[0] + S[1]*in[1]
--          out[1] = in[1] + in[0]*S[2]
def mixS_t2 (S : Vector ℕ 168) (round : ℕ) (state : Vector F 2) (hr : round < 56) : Vector F 2 :=
  let base := round * 3
  let s0 : F := S[base]
  let s1 : F := S[base + 1]
  let s2 : F := S[base + 2]
  let out0 := s0 * state[0] + s1 * state[1]
  let out1 := state[1] + state[0] * s2
  #v[out0, out1]

-- MixS: Sparse matrix multiplication for partial rounds
-- For t=3: out[0] = S[0]*in[0] + S[1]*in[1] + S[2]*in[2]
--          out[1] = in[1] + in[0]*S[3]
--          out[2] = in[2] + in[0]*S[4]
def mixS_t3 (S : Vector ℕ 285) (round : ℕ) (state : Vector F 3) (hr : round < 57) : Vector F 3 :=
  let base := round * 5
  let s0 : F := S[base]
  let s1 : F := S[base + 1]
  let s2 : F := S[base + 2]
  let s3 : F := S[base + 3]
  let s4 : F := S[base + 4]
  let out0 := s0 * state[0] + s1 * state[1] + s2 * state[2]
  let out1 := state[1] + state[0] * s3
  let out2 := state[2] + state[0] * s4
  #v[out0, out1, out2]

-- MixS: Sparse matrix multiplication for partial rounds
-- For t=4: out[0] = S[0]*in[0] + S[1]*in[1] + S[2]*in[2] + S[3]*in[3]
--          out[1] = in[1] + in[0]*S[4]
--          out[2] = in[2] + in[0]*S[5]
--          out[3] = in[3] + in[0]*S[6]
def mixS_t4 (S : Vector ℕ 392) (round : ℕ) (state : Vector F 4) (hr : round < 56) : Vector F 4 :=
  let base := round * 7
  let s0 : F := S[base]
  let s1 : F := S[base + 1]
  let s2 : F := S[base + 2]
  let s3 : F := S[base + 3]
  let s4 : F := S[base + 4]
  let s5 : F := S[base + 5]
  let s6 : F := S[base + 6]
  let out0 := s0 * state[0] + s1 * state[1] + s2 * state[2] + s3 * state[3]
  let out1 := state[1] + state[0] * s4
  let out2 := state[2] + state[0] * s5
  let out3 := state[3] + state[0] * s6
  #v[out0, out1, out2, out3]

/-
============================================================================
OPTIMIZED POSEIDON PERMUTATION
Matches circomlib structure exactly:
1. Initial ARK
2. First half full rounds (Rf/2 - 1): SBOX → ARK → MIX(M)
3. Transition round: SBOX → ARK → MIX(P)
4. Partial rounds: SBOX_first → ARK_first → MixS(S)
5. Second half full rounds (Rf/2 - 1): SBOX → ARK → MIX(M)
6. Final round: SBOX → MIX(M)
============================================================================
-/

/-
============================================================================
OPTIMIZED POSEIDON HASH (t=2, 1 input)
============================================================================
-/

-- Full round for t=2: SBOX → ARK → MIX
def fullRoundOpt_t2 (C : Vector ℕ 72) (M : Vector (Vector ℕ 2) 2) (offset : ℕ)
    (state : Vector F 2) : Vector F 2 :=
  state |> sboxFull |> ark C offset |> mix M

-- Apply n full rounds for t=2
def fullRoundsOpt_t2 (C : Vector ℕ 72) (M : Vector (Vector ℕ 2) 2)
    (nRounds : ℕ) (offset : ℕ) (state : Vector F 2) : Vector F 2 :=
  match nRounds with
  | 0 => state
  | r + 1 =>
    let state' := fullRoundOpt_t2 C M offset state
    fullRoundsOpt_t2 C M r (offset + 2) state'

-- Partial round for t=2 with MixS: SBOX_first → ARK_first → MixS
def partialRoundOpt_t2 (C : Vector ℕ 72) (S : Vector ℕ 168) (cOffset : ℕ) (sRound : ℕ)
    (state : Vector F 2) (hr : sRound < 56) : Vector F 2 :=
  let state' : Vector F 2 :=
    if hc : cOffset < 72 then
      #v[sigma state[0] + C[cOffset], state[1]]
    else
      #v[sigma state[0], state[1]]
  mixS_t2 S sRound state' hr

-- Apply n partial rounds for t=2 with MixS
def partialRoundsOpt_t2 (C : Vector ℕ 72) (S : Vector ℕ 168)
    (nRounds : ℕ) (cOffset : ℕ) (sRound : ℕ) (state : Vector F 2)
    (hr : sRound + nRounds ≤ 56) : Vector F 2 :=
  match nRounds with
  | 0 => state
  | r + 1 =>
    have hr' : sRound < 56 := by omega
    let state' := partialRoundOpt_t2 C S cOffset sRound state hr'
    have hr'' : sRound + 1 + r ≤ 56 := by omega
    partialRoundsOpt_t2 C S r (cOffset + 1) (sRound + 1) state' hr''

def poseidon1Permutation (input : F) : Vector F 2 :=
  permutation params_t2 #v[input]

def poseidon1Opt (input : F) : F :=
  poseidon params_t2 #v[input]

/-
============================================================================
OPTIMIZED POSEIDON HASH HELPERS (t=3)
============================================================================
-/

-- Full round: SBOX → ARK → MIX
def fullRoundOpt (C : Vector ℕ 81) (M : Vector (Vector ℕ 3) 3) (offset : ℕ)
    (state : Vector F 3) : Vector F 3 :=
  state |> sboxFull |> ark C offset |> mix M

-- Apply n full rounds
def fullRoundsOpt (C : Vector ℕ 81) (M : Vector (Vector ℕ 3) 3)
    (nRounds : ℕ) (offset : ℕ) (state : Vector F 3) : Vector F 3 :=
  match nRounds with
  | 0 => state
  | r + 1 =>
    let state' := fullRoundOpt C M offset state
    fullRoundsOpt C M r (offset + 3) state'

-- Partial round with MixS: SBOX_first → ARK_first → MixS
def partialRoundOpt (C : Vector ℕ 81) (S : Vector ℕ 285) (cOffset : ℕ) (sRound : ℕ)
    (state : Vector F 3) (hr : sRound < 57) : Vector F 3 :=
  -- Apply sbox to first element, then add round constant to first element
  let state' : Vector F 3 :=
    if hc : cOffset < 81 then
      #v[sigma state[0] + (C[cOffset]'hc : F), state[1], state[2]]
    else
      #v[sigma state[0], state[1], state[2]]
  mixS_t3 S sRound state' hr

-- Apply n partial rounds with MixS
def partialRoundsOpt (C : Vector ℕ 81) (S : Vector ℕ 285)
    (nRounds : ℕ) (cOffset : ℕ) (sRound : ℕ) (state : Vector F 3)
    (hr : sRound + nRounds ≤ 57) : Vector F 3 :=
  match nRounds with
  | 0 => state
  | r + 1 =>
    have hr' : sRound < 57 := by omega
    let state' := partialRoundOpt C S cOffset sRound state hr'
    have hr'' : sRound + 1 + r ≤ 57 := by omega
    partialRoundsOpt C S r (cOffset + 1) (sRound + 1) state' hr''

/-
============================================================================
OPTIMIZED POSEIDON HASH (t=3, 2 inputs)
============================================================================
-/

def poseidon2Opt (inputs : Vector F 2) : F :=
  let t := 3
  let nRoundsF := 8
  let nP := 57
  -- Initial state: [0, input0, input1]
  let state : Vector F 3 := #v[(0 : F), inputs[0], inputs[1]]

  -- 1. Initial ARK with C[0..2]
  let state := ark C_t3 0 state

  -- 2. First half full rounds (Rf/2 - 1 = 3): SBOX → ARK → MIX(M)
  --    Uses C[3..11] (3 rounds × 3)
  let state := fullRoundsOpt C_t3 M_t3 3 t state

  -- 3. Transition round: SBOX → ARK → MIX(P)
  --    Uses C[12..14]
  let state := state |> sboxFull |> ark C_t3 12 |> mix P_t3

  -- 4. Partial rounds (57): SBOX_first → ARK_first → MixS(S)
  --    Uses C[15..71] (57 × 1)
  let state := partialRoundsOpt C_t3 S_t3 nP 15 0 state (by omega)

  -- 5. Second half full rounds (Rf/2 - 1 = 3): SBOX → ARK → MIX(M)
  --    Uses C[72..80] (3 rounds × 3)
  let state := fullRoundsOpt C_t3 M_t3 3 72 state

  -- 6. Final round: SBOX → MIX(M) (no ARK)
  let state := state |> sboxFull |> mix M_t3

  -- Output first element
  state[0]

/-
============================================================================
OPTIMIZED POSEIDON HASH (t=4, 3 inputs)
============================================================================
-/

open Specs.Poseidon (C_t4 M_t4)

-- Full round for t=4: SBOX → ARK → MIX
def fullRoundOpt_t4 (C : Vector ℕ 88) (M : Vector (Vector ℕ 4) 4) (offset : ℕ)
    (state : Vector F 4) : Vector F 4 :=
  state |> sboxFull |> ark C offset |> mix M

-- Apply n full rounds for t=4
def fullRoundsOpt_t4 (C : Vector ℕ 88) (M : Vector (Vector ℕ 4) 4)
    (nRounds : ℕ) (offset : ℕ) (state : Vector F 4) : Vector F 4 :=
  match nRounds with
  | 0 => state
  | r + 1 =>
    let state' := fullRoundOpt_t4 C M offset state
    fullRoundsOpt_t4 C M r (offset + 4) state'

-- Partial round for t=4 with MixS: SBOX_first → ARK_first → MixS
def partialRoundOpt_t4 (C : Vector ℕ 88) (S : Vector ℕ 392) (cOffset : ℕ) (sRound : ℕ)
    (state : Vector F 4) (hr : sRound < 56) : Vector F 4 :=
  let state' : Vector F 4 :=
    if hc : cOffset < 88 then
      #v[sigma state[0] + (C[cOffset]'hc : F), state[1], state[2], state[3]]
    else
      #v[sigma state[0], state[1], state[2], state[3]]
  mixS_t4 S sRound state' hr

-- Apply n partial rounds for t=4 with MixS
def partialRoundsOpt_t4 (C : Vector ℕ 88) (S : Vector ℕ 392)
    (nRounds : ℕ) (cOffset : ℕ) (sRound : ℕ) (state : Vector F 4)
    (hr : sRound + nRounds ≤ 56) : Vector F 4 :=
  match nRounds with
  | 0 => state
  | r + 1 =>
    have hr' : sRound < 56 := by omega
    let state' := partialRoundOpt_t4 C S cOffset sRound state hr'
    have hr'' : sRound + 1 + r ≤ 56 := by omega
    partialRoundsOpt_t4 C S r (cOffset + 1) (sRound + 1) state' hr''

def poseidon3Opt (inputs : Vector F 3) : F :=
  let t := 4
  let nRoundsF := 8
  let nP := 56
  -- Initial state: [0, input0, input1, input2]
  let state : Vector F 4 := #v[(0 : F), inputs[0], inputs[1], inputs[2]]

  -- 1. Initial ARK with C[0..3]
  let state := ark C_t4 0 state

  -- 2. First half full rounds (Rf/2 - 1 = 3): SBOX → ARK → MIX(M)
  --    Uses C[4..15] (3 rounds × 4)
  let state := fullRoundsOpt_t4 C_t4 M_t4 3 t state

  -- 3. Transition round: SBOX → ARK → MIX(P)
  --    Uses C[16..19]
  let state := state |> sboxFull |> ark C_t4 16 |> mix P_t4

  -- 4. Partial rounds (56): SBOX_first → ARK_first → MixS(S)
  --    Uses C[20..75] (56 × 1)
  let state := partialRoundsOpt_t4 C_t4 S_t4 nP 20 0 state (by omega)

  -- 5. Second half full rounds (Rf/2 - 1 = 3): SBOX → ARK → MIX(M)
  --    Uses C[76..87] (3 rounds × 4)
  let state := fullRoundsOpt_t4 C_t4 M_t4 3 76 state

  -- 6. Final round: SBOX → MIX(M) (no ARK)
  let state := state |> sboxFull |> mix M_t4

  -- Output first element
  state[0]

/-
============================================================================
TEST VECTORS
Should produce same results as non-optimized version and circomlibjs
============================================================================
-/

open Specs.Poseidon (poseidon1 poseidon2 poseidon3 BN254_PRIME)

/-
============================================================================
POSEIDON1 (t=2) TEST VECTORS
============================================================================
-/

-- Test poseidon1Opt matches non-optimized poseidon1 for various inputs
example : poseidon1Opt (1 : F) = poseidon1 (1 : F) := by native_decide
example : poseidon1Opt (0 : F) = poseidon1 (0 : F) := by native_decide
example : poseidon1Opt (123 : F) = poseidon1 (123 : F) := by native_decide
example : poseidon1Opt (BN254_PRIME - 1 : F) = poseidon1 (BN254_PRIME - 1 : F) := by native_decide

/-
============================================================================
POSEIDON2 (t=3) TEST VECTORS
============================================================================
-/

-- Test 1: poseidon([1, 2]) = 0x115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a
example : poseidon2Opt #v[(1 : F), 2] =
    (0x115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a : F) := by
  native_decide

-- Test 2: Verify optimized version matches non-optimized version for [1, 2]
example : poseidon2Opt #v[(1 : F), 2] = poseidon2 #v[(1 : F), 2] := by
  native_decide

-- Test 3: poseidon([0, 0]) - edge case with zero inputs
example : poseidon2Opt #v[(0 : F), 0] = poseidon2 #v[(0 : F), 0] := by
  native_decide

-- Test 4: poseidon([1, 0])
example : poseidon2Opt #v[(1 : F), 0] = poseidon2 #v[(1 : F), 0] := by
  native_decide

-- Test 5: poseidon([0, 1])
example : poseidon2Opt #v[(0 : F), 1] = poseidon2 #v[(0 : F), 1] := by
  native_decide

-- Test 6: poseidon([3, 4]) - different inputs
example : poseidon2Opt #v[(3 : F), 4] = poseidon2 #v[(3 : F), 4] := by
  native_decide

-- Test 7: poseidon with larger values
example : poseidon2Opt #v[(12345 : F), 67890] = poseidon2 #v[(12345 : F), 67890] := by
  native_decide

-- Test 8: poseidon with field-sized values (near prime)
example : poseidon2Opt #v[(BN254_PRIME - 1 : F), 1] = poseidon2 #v[(BN254_PRIME - 1 : F), 1] := by
  native_decide

/-
============================================================================
POSEIDON3 (t=4) TEST VECTORS
============================================================================
-/

-- Test 9: poseidon3Opt matches poseidon3 for [1, 0, 0]
example : poseidon3Opt #v[(1 : F), 0, 0] = poseidon3 #v[(1 : F), 0, 0] := by
  native_decide

-- Test 10: poseidon3Opt matches poseidon3 for [0, 0, 0]
example : poseidon3Opt #v[(0 : F), 0, 0] = poseidon3 #v[(0 : F), 0, 0] := by
  native_decide

-- Test 11: poseidon3Opt matches poseidon3 for [1, 2, 3]
example : poseidon3Opt #v[(1 : F), 2, 3] = poseidon3 #v[(1 : F), 2, 3] := by
  native_decide

-- Test 12: poseidon3Opt produces known value for [1, 0, 0]
-- From Poseidon.lean: poseidon3([1, 0, 0]) = 16319005924338521988144249782199320915969277491928916027259324394544057385749
example : poseidon3Opt #v[(1 : F), 0, 0] =
    (16319005924338521988144249782199320915969277491928916027259324394544057385749 : F) := by
  native_decide

-- Test 13: poseidon3Opt produces known value for [0, 0, 0]
-- From Poseidon.lean: poseidon3([0, 0, 0]) = 5317387130258456662214331362918410991734007599705406860481038345552731150762
example : poseidon3Opt #v[(0 : F), 0, 0] =
    (5317387130258456662214331362918410991734007599705406860481038345552731150762 : F) := by
  native_decide

/-
============================================================================
GENERIC SPECIFICATION REGRESSION TESTS
============================================================================
-/

-- State width 2 / one input
theorem poseidon_params_t2_eq_poseidon1Opt (input : F) :
    poseidon params_t2 #v[input] = poseidon1Opt input := by
  rfl

-- State width 3 / two inputs
example : poseidon params_t3 #v[(1 : F), 2] = poseidon2Opt #v[(1 : F), 2] := by native_decide
example : poseidon params_t3 #v[(0 : F), 0] = poseidon2Opt #v[(0 : F), 0] := by native_decide
example : poseidon params_t3 #v[(1 : F), 0] = poseidon2Opt #v[(1 : F), 0] := by native_decide
example : poseidon params_t3 #v[(0 : F), 1] = poseidon2Opt #v[(0 : F), 1] := by native_decide
example : poseidon params_t3 #v[(3 : F), 4] = poseidon2Opt #v[(3 : F), 4] := by native_decide
example : poseidon params_t3 #v[(12345 : F), 67890] = poseidon2Opt #v[(12345 : F), 67890] := by
  native_decide
example : poseidon params_t3 #v[(BN254_PRIME - 1 : F), 1] =
    poseidon2Opt #v[(BN254_PRIME - 1 : F), 1] := by
  native_decide

-- State width 4 / three inputs
example : poseidon params_t4 #v[(1 : F), 0, 0] = poseidon3Opt #v[(1 : F), 0, 0] := by
  native_decide
example : poseidon params_t4 #v[(0 : F), 0, 0] = poseidon3Opt #v[(0 : F), 0, 0] := by
  native_decide
example : poseidon params_t4 #v[(1 : F), 2, 3] = poseidon3Opt #v[(1 : F), 2, 3] := by
  native_decide

end Specs.PoseidonOptimized
