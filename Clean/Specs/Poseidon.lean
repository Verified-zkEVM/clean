/-
Poseidon Hash Function Specification

This file contains the mathematical specification of the Poseidon hash function,
matching the circomlib implementation:
https://github.com/iden3/circomlib/blob/master/circuits/poseidon.circom
-/
import Clean.Utils.Vector
import Clean.Specs.PoseidonConstants

namespace Specs.Poseidon

-- BN254 scalar field prime (same as used in circomlib/snarkjs)
def BN254_PRIME : ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

abbrev F := ZMod BN254_PRIME

-- Number of full rounds (split into 4 at start, 4 at end)
def nRoundsF : ℕ := 8

-- Number of partial rounds for each t value (t = nInputs + 1)
-- Index by (t - 2), so t=2 -> index 0, t=3 -> index 1, etc.
def N_ROUNDS_P : Vector ℕ 16 := #v[56, 57, 56, 60, 60, 63, 64, 63, 60, 66, 60, 65, 70, 60, 64, 68]

def nRoundsP (t : ℕ) : ℕ :=
  if h : t ≥ 2 ∧ t ≤ 17 then N_ROUNDS_P[t - 2]'(by omega) else 0

/-
============================================================================
CORE FUNCTIONS
============================================================================
-/

-- S-box: x^5 (the Poseidon S-box for BN254)
def sigma (x : F) : F := x ^ 5

-- Add round constants to state
def ark {n t : ℕ} (C : Vector ℕ n) (offset : ℕ) (state : Vector F t) : Vector F t :=
  Vector.ofFn fun i =>
    if h : offset + i < n then
      state[i] + C[offset + i]
    else
      state[i]

-- Matrix-vector multiplication (Mix layer)
def mix {t : ℕ} (M : Vector (Vector ℕ t) t) (state : Vector F t) : Vector F t :=
  Vector.ofFn fun i =>
    (List.range t).foldl (fun acc j =>
      if hj : j < t then
        acc + M[j][i] * state[j]
      else acc
    ) 0

-- Apply S-box to all elements (full round)
def sboxFull {t : ℕ} (state : Vector F t) : Vector F t :=
  state.map sigma

-- Apply S-box to first element only (partial round)
def sboxPartial {t : ℕ} (state : Vector F t) (h : 0 < t) : Vector F t :=
  Vector.ofFn fun i =>
    if i.val = 0 then sigma state[0]
    else state[i]

/-
============================================================================
POSEIDON PERMUTATION (Circomlib round structure)
Round structure: ARK_initial → (SBOX → ARK → MIX)^(Rf/2) → (SBOX_partial → ARK_partial → MIX)^Rp → (SBOX → ARK → MIX)^(Rf/2-1) → SBOX → MIX
============================================================================
-/

-- One full round (circomlib style): sbox_full -> ark -> mix
def fullRoundCircom {n t : ℕ} (C : Vector ℕ n) (M : Vector (Vector ℕ t) t) (offset : ℕ)
    (state : Vector F t) : Vector F t :=
  state |> sboxFull |> ark C offset |> mix M

-- One partial round (circomlib style): sbox on first element, ark on first element, mix
-- Note: In circomlib partial rounds, only first element gets sbox and ark
def partialRoundCircom {n t : ℕ} (C : Vector ℕ n) (M : Vector (Vector ℕ t) t) (offset : ℕ)
    (state : Vector F t) (h : 0 < t) : Vector F t :=
  -- Apply sbox to first element, then add round constant to first element
  let state' : Vector F t := Vector.ofFn fun i =>
    if i.val = 0 then
      let sboxed := sigma state[0]
      if hoff : offset < n then
        sboxed + C[offset]
      else sboxed
    else state[i]
  mix M state'

-- Apply n full rounds (circomlib style) starting from given offset
def fullRoundsCircom {cLen t : ℕ} (C : Vector ℕ cLen) (M : Vector (Vector ℕ t) t)
    (nRounds : ℕ) (offset : ℕ) (state : Vector F t) : Vector F t :=
  match nRounds with
  | 0 => state
  | r + 1 =>
    let state' := fullRoundCircom C M offset state
    fullRoundsCircom C M r (offset + t) state'

-- Apply n partial rounds (circomlib style) starting from given offset
-- Each partial round uses only 1 constant (for the first element)
def partialRoundsCircom {cLen t : ℕ} (C : Vector ℕ cLen) (M : Vector (Vector ℕ t) t)
    (nRounds : ℕ) (offset : ℕ) (state : Vector F t) (h : 0 < t) : Vector F t :=
  match nRounds with
  | 0 => state
  | r + 1 =>
    let state' := partialRoundCircom C M offset state h
    partialRoundsCircom C M r (offset + 1) state' h  -- +1 not +t for partial rounds

/-
============================================================================
POSEIDON HASH FUNCTIONS (Circomlib compatible)

Round structure for t=2, nRoundsF=8, nRoundsP=56:
1. Initial ARK: C[0..1]
2. First half full rounds (4): (SBOX → ARK → MIX), using C[2..9] (4 rounds × 2)
3. Partial rounds (56): (SBOX_first → ARK_first → MIX), using C[10..65] (56 × 1)
4. Second half full rounds (3): (SBOX → ARK → MIX), using C[66..71] (3 rounds × 2)
5. Final: SBOX → MIX (no ARK)
============================================================================
-/

-- Poseidon hash for 1 input (t=2)
def poseidon1 (input : F) : F :=
  let t := 2
  let nP := 56  -- N_ROUNDS_P[0]
  -- Initial state: [initialState, input]
  let state : Vector F 2 := #v[0, input]
  -- Initial ARK with C[0..1]
  let state := ark C_t2 0 state
  -- First half full rounds (4): SBOX → ARK → MIX
  -- Uses C[2..9] (4 rounds × 2 constants)
  let state := fullRoundsCircom C_t2 M_t2 4 t state
  -- Partial rounds (56): SBOX_first → ARK_first → MIX
  -- Uses C[10..65] (56 × 1 constant each)
  let state := partialRoundsCircom C_t2 M_t2 nP (t + 4*t) state (by omega)
  -- Second half full rounds (3): SBOX → ARK → MIX
  -- Uses C[66..71] (3 rounds × 2 constants)
  let state := fullRoundsCircom C_t2 M_t2 3 (t + 4*t + nP) state
  -- Final round: just SBOX → MIX (no ARK)
  let state := state |> sboxFull |> mix M_t2
  -- Output is first element
  state[0]

-- Poseidon hash for 2 inputs (t=3)
def poseidon2 (inputs : Vector F 2) : F :=
  let t := 3
  let nRoundsF := 8
  let nP := 57  -- N_ROUNDS_P[1]
  -- Initial state: [initialState, input0, input1]
  let state : Vector F 3 := #v[(0 : F), inputs[0], inputs[1]]
  -- Initial ARK with C[0..2]
  let state := ark C_t3 0 state
  -- First half full rounds (nRoundsF/2 = 4): SBOX → ARK → MIX
  -- Uses C[3..14] (4 rounds × 3 constants)
  let state := fullRoundsCircom C_t3 M_t3 4 t state
  -- Partial rounds (57): SBOX_first → ARK_first → MIX
  -- Uses C[15..71] (57 × 1 constant each)
  let state := partialRoundsCircom C_t3 M_t3 nP (t + 4*t) state (by omega)
  -- Second half full rounds (nRoundsF/2 - 1 = 3): SBOX → ARK → MIX
  -- Uses C[72..80] (3 rounds × 3 constants)
  let state := fullRoundsCircom C_t3 M_t3 3 (t + 4*t + nP) state
  -- Final round: just SBOX → MIX (no ARK)
  let state := state |> sboxFull |> mix M_t3
  -- Output is first element
  state[0]

-- Poseidon hash for 3 inputs (t=4)
def poseidon3 (inputs : Vector F 3) : F :=
  let t := 4
  let nP := 56  -- N_ROUNDS_P[2]
  -- Initial state: [initialState, input0, input1, input2]
  let state : Vector F 4 := #v[(0 : F), inputs[0], inputs[1], inputs[2]]
  -- Initial ARK
  let state := ark C_t4 0 state
  -- First half full rounds (4)
  let state := fullRoundsCircom C_t4 M_t4 4 t state
  -- Partial rounds (56)
  let state := partialRoundsCircom C_t4 M_t4 nP (t + 4*t) state (by omega)
  -- Second half full rounds (3)
  let state := fullRoundsCircom C_t4 M_t4 3 (t + 4*t + nP) state
  -- Final round: SBOX → MIX
  let state := state |> sboxFull |> mix M_t4
  state[0]

-- Poseidon hash for 4 inputs (t=5)
def poseidon4 (inputs : Vector F 4) : F :=
  let t := 5
  let nP := 60  -- N_ROUNDS_P[3]
  -- Initial state: [initialState, input0, input1, input2, input3]
  let state : Vector F 5 := #v[(0 : F), inputs[0], inputs[1], inputs[2], inputs[3]]
  -- Initial ARK
  let state := ark C_t5 0 state
  -- First half full rounds (4)
  let state := fullRoundsCircom C_t5 M_t5 4 t state
  -- Partial rounds (60)
  let state := partialRoundsCircom C_t5 M_t5 nP (t + 4*t) state (by omega)
  -- Second half full rounds (3)
  let state := fullRoundsCircom C_t5 M_t5 3 (t + 4*t + nP) state
  -- Final round: SBOX → MIX
  let state := state |> sboxFull |> mix M_t5
  state[0]

/-
============================================================================
TEST VECTORS
These test vectors are from circomlibjs and validate our implementation.
============================================================================
-/

-- Test poseidon1 (1 input)
-- poseidon([1]) = 18586133768512220936620570745912940619677854269274689475585506675881198879027
example : poseidon1 (1 : F) =
    (18586133768512220936620570745912940619677854269274689475585506675881198879027 : F) := by
  native_decide

example : poseidon1 (0 : F) =
    (19014214495641488759237505126948346942972912379615652741039992445865937985820 : F) := by
  native_decide

example : poseidon1 (123 : F) =
    (9904028930859697121695025471312564917337032846528014134060777877259199866166 : F) := by
  native_decide

-- Test vector 1: poseidon([1, 2]) = 0x115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a
-- In decimal: 7853200120776062878684798364095072458815029376092732009249414926327459813530
example : poseidon2 #v[(1 : F), 2] =
    (0x115cc0f5e7d690413df64c6b9662e9cf2a3617f2743245519e19607a4417189a : F) := by
  native_decide

-- Test vector 2: poseidon([1, 0, 0]) = 16319005924338521988144249782199320915969277491928916027259324394544057385749
example : poseidon3 #v[(1 : F), 0, 0] =
    (16319005924338521988144249782199320915969277491928916027259324394544057385749 : F) := by
  native_decide

-- Test vector 3: poseidon([0, 0, 0]) = 5317387130258456662214331362918410991734007599705406860481038345552731150762
example : poseidon3 #v[(0 : F), 0, 0] =
    (5317387130258456662214331362918410991734007599705406860481038345552731150762 : F) := by
  native_decide

-- Test vector 4: poseidon([1, 2, 3, 4]) = 0x299c867db6c1fdd79dcefa40e4510b9837e60ebb1ce0663dbaa525df65250465
-- In decimal: 18821383157269793795438455681495246036402687001665670618754263018637548127845
example : poseidon4 #v[(1 : F), 2, 3, 4] =
    (0x299c867db6c1fdd79dcefa40e4510b9837e60ebb1ce0663dbaa525df65250465 : F) := by
  native_decide

end Specs.Poseidon
