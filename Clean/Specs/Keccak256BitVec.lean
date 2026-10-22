/-
Keccak-f on lanes of 64 bits indexed by `(x, y)`, with θ, ρ and π written for every lane at once,
as a bit-level circuit checks them. It agrees with `Specs.Keccak256` on every state.
-/
module

public import Clean.Specs.Keccak256
public import Clean.Utils.Rotation
public import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace Specs.Keccak256

/-- The rotation offsets `r[x][y]` of ρ. -/
def rotationOffsets : Vector (Vector (Fin 64) 5) 5 := #v[
  #v[0, 36, 3, 41, 18],
  #v[1, 44, 10, 45, 2],
  #v[62, 6, 43, 15, 61],
  #v[28, 55, 25, 21, 56],
  #v[27, 20, 39, 8, 14]]

/-- A Keccak-f state: lane `(x, y)` holds bits `z = 0, ..., 63`. -/
abbrev Lanes := Fin 5 → Fin 5 → BitVec 64

namespace Lanes

/-- The parity `C[x] = A[x, 0] ^ ... ^ A[x, 4]` of column `x`. -/
def columnParity (state : Lanes) (x : Fin 5) : BitVec 64 :=
  state x 0 ^^^ state x 1 ^^^ state x 2 ^^^ state x 3 ^^^ state x 4

/-- θ: `A[x, y] ^ C[x - 1] ^ rot(C[x + 1], 1)`, with `x - 1 = x + 4`. -/
def theta (state : Lanes) : Lanes := fun x y =>
  state x y ^^^ (columnParity state (x + 4) ^^^ (columnParity state (x + 1)).rotateLeft 1)

/-- ρ and π: `B[y, 2 x + 3 y] = rot(A[x, y], r[x][y])`, that is `B[x, y] = rot(A[a, x], r[a][x])`
with `a = x + 3 y`. -/
def rhoPi (state : Lanes) : Lanes := fun x y =>
  let a := x + 3 * y
  (state a x).rotateLeft rotationOffsets[a][x]

/-- χ: `B[x, y] ^ (~B[x + 1, y] & B[x + 2, y])`. -/
def chi (state : Lanes) : Lanes := fun x y =>
  state x y ^^^ (~~~state (x + 1) y &&& state (x + 2) y)

/-- ι: xor the round constant into lane `(0, 0)`. -/
def iota (state : Lanes) (roundConstant : BitVec 64) : Lanes := fun x y =>
  if x = 0 ∧ y = 0 then state x y ^^^ roundConstant else state x y

def round (state : Lanes) (roundConstant : UInt64) : Lanes :=
  iota (chi (rhoPi (theta state))) roundConstant.toBitVec

def permutation (state : Lanes) : Lanes :=
  roundConstants.foldl round state

/-- The state in `Specs.Keccak256`'s form: lane `(x, y)` at index `5 x + y`. -/
def toState (state : Lanes) : Vector ℕ 25 :=
  Vector.ofFn fun i => (state ⟨i.val / 5, by omega⟩ ⟨i.val % 5, by omega⟩).toNat

lemma toNat_not (lane : BitVec 64) : (~~~lane).toNat = not64 lane.toNat := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [not64, BitVec.testBit_toNat, BitVec.getLsbD_not, Nat.testBit_xor]
  rw [show (0xffffffffffffffff : ℕ) = 2 ^ 64 - 1 by norm_num, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 64
  · simp [hi]
  · simp [hi, BitVec.getLsbD_of_ge lane i (by omega)]

lemma toNat_rotateLeft (lane : BitVec 64) (offset : Fin 64) :
    (lane.rotateLeft offset).toNat = rotLeft64 lane.toNat offset := by
  rw [rotLeft64_eq_rotRight64, Utils.Rotation.rotRight64_eq_bv_rotate _ lane.isLt]
  congr 1
  have hlane : lane.toNat.toUInt64.toBitVec = lane := by
    apply BitVec.eq_of_toNat_eq
    simp
  rw [hlane]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hneg : (-offset).val = (64 - offset.val) % 64 := by
    rw [Fin.val_neg']
  rw [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_rotateRight, hneg]
  obtain ⟨k, hk⟩ := offset
  simp only [Nat.mod_mod]
  simp only [Nat.mod_eq_of_lt hk]
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [hi]
  · rw [Nat.mod_eq_of_lt (by omega : 64 - k < 64)]
    split_ifs <;> simp_all <;> congr 1 <;> omega

lemma toNat_rotateLeft' (lane : BitVec 64) (offset : ℕ) :
    (lane.rotateLeft offset).toNat = rotLeft64 lane.toNat (Fin.ofNat 64 offset) := by
  rw [← toNat_rotateLeft, Fin.val_ofNat]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_rotateLeft, Nat.mod_mod]

lemma theta_toState (state : Lanes) :
    Specs.Keccak256.theta (toState state) = toState (theta state) := by
  ext i hi
  interval_cases i <;>
    simp [Specs.Keccak256.theta, thetaC, thetaD, thetaXor, toState, theta, columnParity,
      toNat_rotateLeft', -BitVec.toNat_rotateLeft] <;> rfl

lemma rhoPi_toState (state : Lanes) :
    Specs.Keccak256.rhoPi (toState state) = toState (rhoPi state) := by
  ext i hi
  interval_cases i <;>
    simp [Specs.Keccak256.rhoPi, toState, rhoPi, rotationOffsets, toNat_rotateLeft',
      -BitVec.toNat_rotateLeft]

lemma chi_toState (state : Lanes) :
    Specs.Keccak256.chi (toState state) = toState (chi state) := by
  ext i hi
  interval_cases i <;> simp [Specs.Keccak256.chi, toState, chi, toNat_not, -BitVec.toNat_not]

lemma iota_toState (state : Lanes) (roundConstant : UInt64) :
    Specs.Keccak256.iota (toState state) roundConstant =
      toState (iota state roundConstant.toBitVec) := by
  ext i hi
  interval_cases i <;> simp [Specs.Keccak256.iota, toState, iota]

theorem keccakRound_toState (state : Lanes) (roundConstant : UInt64) :
    keccakRound (toState state) roundConstant = toState (round state roundConstant) := by
  simp only [keccakRound, theta_toState, rhoPi_toState, chi_toState, iota_toState, round]

theorem keccakPermutation_toState (state : Lanes) :
    keccakPermutation (toState state) = toState (permutation state) := by
  simp only [keccakPermutation, permutation, ← Vector.foldl_toList]
  generalize roundConstants.toList = constants
  induction constants generalizing state with
  | nil => rfl
  | cons constant constants ih => simp only [List.foldl_cons, keccakRound_toState, ih]

end Lanes
end Specs.Keccak256
