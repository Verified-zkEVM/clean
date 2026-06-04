/-
Optimized Poseidon Hash Function Specification

This file contains the optimized version of Poseidon that matches circomlib's
structure exactly, using P matrix for transition and S sparse matrix for partial rounds.
Constants are in PoseidonConstants.lean.

This is intended for circuit formalization where structure matching simplifies proofs.
For mathematical reasoning, use the simpler Poseidon.lean spec.
-/
import Clean.Specs.Poseidon

namespace Specs.PoseidonOptimized

open Specs.Poseidon (F BN254_PRIME sigma ark sboxFull mix C_t2 M_t2 C_t3 M_t3)

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
  let t := 2
  let nRoundsF := 8
  let nP := 56
  -- Initial state: [0, input]
  let state : Vector F 2 := #v[(0 : F), input]

  -- 1. Initial ARK with C[0..1]
  let state := ark C_t2 0 state

  -- 2. First half full rounds (Rf/2 - 1 = 3): SBOX → ARK → MIX(M)
  --    Uses C[2..7] (3 rounds × 2)
  let state := fullRoundsOpt_t2 C_t2 M_t2 3 t state

  -- 3. Transition round: SBOX → ARK → MIX(P)
  --    Uses C[8..9]
  let state := state |> sboxFull |> ark C_t2 8 |> mix P_t2

  -- 4. Partial rounds (56): SBOX_first → ARK_first → MixS(S)
  --    Uses C[10..65] (56 × 1)
  let state := partialRoundsOpt_t2 C_t2 S_t2 nP 10 0 state (by omega)

  -- 5. Second half full rounds (Rf/2 - 1 = 3): SBOX → ARK → MIX(M)
  --    Uses C[66..71] (3 rounds × 2)
  let state := fullRoundsOpt_t2 C_t2 M_t2 3 66 state

  -- 6. Final round: SBOX → MIX(M) (no ARK)
  state |> sboxFull |> mix M_t2

def poseidon1Opt (input : F) : F :=
  let state := poseidon1Permutation input
  -- Output first element of the final state
  state[0]

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

end Specs.PoseidonOptimized
