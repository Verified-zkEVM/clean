/-
What the rows of the Keccak-f AIR mean: the state a row holds, and the rounds of Keccak-f it has
applied to the permutation's preimage.
-/
module

public import Clean.Examples.KeccakAir.Row
public import Clean.Utils.Field

@[expose] public section

namespace KeccakAir
open Specs.Keccak256 Air.Flat

variable {p : ℕ} [Fact p.Prime]

/-- The value of a 64-bit lane held as four 16-bit limbs, lowest first. -/
def laneValue (limb : Fin 4 → F p) : ℕ :=
  (limb 0).val + 2 ^ 16 * (limb 1).val + 2 ^ 32 * (limb 2).val + 2 ^ 48 * (limb 3).val

/-- A state held as limbs `limb y x`, in `Specs.Keccak256`'s form: lane `(x, y)` at `5 x + y`. -/
def stateOf (limb : Fin 5 → Fin 5 → Fin 4 → F p) : Vector ℕ 25 :=
  Vector.ofFn fun i => laneValue (limb ⟨i.val % 5, by omega⟩ ⟨i.val / 5, by omega⟩)

/-- The first `n` rounds of Keccak-f. -/
def rounds (n : ℕ) (state : Vector ℕ 25) : Vector ℕ 25 :=
  (roundConstants.toList.take n).foldl keccakRound state

/-- The step flags of round `r`. -/
def oneHot (r : Fin 24) : Vector (F p) 24 :=
  Vector.ofFn fun i => if i = r then 1 else 0

namespace Row
variable (row : Row (F p))

/-- The permutation's preimage. -/
def preimageState : Vector ℕ 25 := stateOf row.preimageLimb

/-- The round's input. -/
def inputState : Vector ℕ 25 := stateOf row.aLimb

/-- The round's output. -/
def outputState : Vector ℕ 25 := stateOf row.aPrimePrimePrimeLimb

/-- The limbs of the preimage are 16-bit. -/
def PreimageNormalized : Prop := ∀ y x limb, (row.preimageLimb y x limb).val < 2 ^ 16

end Row

/-- What a row may assume of itself unless it is the first row, and what its previous row
establishes: its step flags are those of a round `r`, and unless `r = 0`, its input is the state
after `r` rounds of its preimage. -/
def Carried (row : Row (F p)) : Prop :=
  ∃ r : Fin 24, row.stepFlags = oneHot r ∧
    (r ≠ 0 → row.PreimageNormalized ∧ row.inputState = rounds r row.preimageState)

/-- A window computes round `r` of its row's preimage: its input is the state after `r` rounds,
its output the state after `r + 1` rounds. Only the last round may export. A transition moves to
round `r + 1`, of the same preimage unless `r` is the last round. -/
def WindowSpec (window : Window Row (F p)) : Prop :=
  let current := window.current
  ∃ r : Fin 24, current.stepFlags = oneHot r ∧ current.PreimageNormalized ∧
    current.inputState = rounds r current.preimageState ∧
    current.outputState = rounds (r.val + 1) current.preimageState ∧
    (current.exportFlag = 1 → r = 23) ∧
    (window.isTransition = 1 → window.next.stepFlags = oneHot (r + 1) ∧
      (r ≠ 23 → window.next.preimage = current.preimage ∧
        window.next.inputState = current.outputState))

end KeccakAir
