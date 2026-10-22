/-
Plonky3's Keccak-f AIR (`p3-keccak-air`): its columns, in Plonky3's order, and its constraints, in
the order and form in which Plonky3 emits them.

Every row computes one round of Keccak-f, and 24 consecutive rows one permutation. The one-hot
`stepFlags` say which round a row computes. A row holds the round's input state `a` in 16-bit limbs,
the bits of θ's column parities `c` and `cPrime` and of θ's output `aPrime`, which ρ and π only
rotate and move, χ's output `aPrimePrime` in limbs, and ι's output lane `(0, 0)`. The next row's
input is this row's output, unless this row computes the last round.

Lanes are indexed by `(x, y)`, and a state is stored `y`-major: lane `(x, y)` is at `5 y + x`, as in
the Keccak specification's `s[w (5 y + x) + z] = a[x][y][z]`.

The constraints are written once for any type with addition, subtraction and multiplication, so that
they are both the circuit's expressions and their values.
-/
module

public import Clean.Air.Window
public import Clean.Specs.Keccak256BitVec

@[expose] public section

namespace KeccakAir
open Air.Flat

/-- A row of the trace, in Plonky3's column order. Indices are `y`-major: `(y, x)` for lanes,
`(y, x, z)` for bits of lanes, `(x, z)` for bits of columns, and limbs and bits come last. -/
structure Row (F : Type) where
  /-- Element `r` is 1 if the row computes round `r`, and 0 otherwise. -/
  stepFlags : fields 24 F
  /-- Plonky3's `export`: whether the row's output would be exported to a bus. It is boolean, and
  only set on rows computing the last round. -/
  exportFlag : F
  /-- The input of the permutation, in 16-bit limbs. -/
  preimage : fields 100 F
  /-- The input of the round, in 16-bit limbs. -/
  a : fields 100 F
  /-- The bits of the column parities `C[x] = A[x, 0] ^ ... ^ A[x, 4]`. -/
  c : fields 320 F
  /-- The bits of `C'[x] = C[x] ^ C[x - 1] ^ rot(C[x + 1], 1)`. -/
  cPrime : fields 320 F
  /-- The bits of θ's output `A'[x, y] = A[x, y] ^ C[x] ^ C'[x]`. -/
  aPrime : fields 1600 F
  /-- χ's output `A''[x, y] = B[x, y] ^ (~B[x + 1, y] & B[x + 2, y])`, in 16-bit limbs. -/
  aPrimePrime : fields 100 F
  /-- The bits of `A''[0, 0]`. -/
  aPrimePrime00Bits : fields 64 F
  /-- ι's output lane `A'''[0, 0] = A''[0, 0] ^ RC`, in 16-bit limbs. -/
  aPrimePrimePrime00Limbs : fields 4 F
deriving ProvableStruct

/-- Bit `z` of the round constant of round `r`. -/
def roundConstantBit (r : Fin 24) (z : Fin 64) : Bool :=
  Specs.Keccak256.roundConstants[r].toNat.testBit z

/-- The position of limb `limb` of lane `(x, y)` in a state of limbs. -/
def limbIndex (y x : Fin 5) (limb : Fin 4) : Fin 100 :=
  ⟨(5 * y.val + x.val) * 4 + limb.val, by omega⟩

/-- The position of bit `z` of lane `(x, y)` in a state of bits. -/
def bitIndex (y x : Fin 5) (z : Fin 64) : Fin 1600 :=
  ⟨(5 * y.val + x.val) * 64 + z.val, by omega⟩

/-- The position of bit `z` of column `x` in the columns' bits. -/
def columnBitIndex (x : Fin 5) (z : Fin 64) : Fin 320 :=
  ⟨64 * x.val + z.val, by omega⟩

/-- Bit `k` of limb `limb` of a lane. -/
def limbBit (limb : Fin 4) (k : Fin 16) : Fin 64 :=
  ⟨16 * limb.val + k.val, by omega⟩

namespace Row
variable {α : Type}

def preimageLimb (row : Row α) (y x : Fin 5) (limb : Fin 4) : α := row.preimage[limbIndex y x limb]
def aLimb (row : Row α) (y x : Fin 5) (limb : Fin 4) : α := row.a[limbIndex y x limb]
def cBit (row : Row α) (x : Fin 5) (z : Fin 64) : α := row.c[columnBitIndex x z]
def cPrimeBit (row : Row α) (x : Fin 5) (z : Fin 64) : α := row.cPrime[columnBitIndex x z]
def aPrimeBit (row : Row α) (y x : Fin 5) (z : Fin 64) : α := row.aPrime[bitIndex y x z]
def aPrimePrimeLimb (row : Row α) (y x : Fin 5) (limb : Fin 4) : α :=
  row.aPrimePrime[limbIndex y x limb]

/-- Bit `z` of `B[x, y]`. `B` is `A'` moved by π and rotated by ρ, `B[y, 2 x + 3 y] = rot(A'[x, y],
r[x][y])`, so its bits are bits of `A'`: `B[x, y] = rot(A'[a, x], r[a][x])` with `a = x + 3 y`. -/
def b (row : Row α) (x y : Fin 5) (z : Fin 64) : α :=
  let a := x + 3 * y
  row.aPrimeBit x a (z - Specs.Keccak256.rotationOffsets[a][x])

/-- Apply `f` to every cell. -/
def map {β : Type} (f : α → β) (row : Row α) : Row β where
  stepFlags := row.stepFlags.map f
  exportFlag := f row.exportFlag
  preimage := row.preimage.map f
  a := row.a.map f
  c := row.c.map f
  cPrime := row.cPrime.map f
  aPrime := row.aPrime.map f
  aPrimePrime := row.aPrimePrime.map f
  aPrimePrime00Bits := row.aPrimePrime00Bits.map f
  aPrimePrimePrime00Limbs := row.aPrimePrimePrime00Limbs.map f

/-- Limb `limb` of the round's output `A'''[x, y]`. -/
def aPrimePrimePrimeLimb (row : Row α) (y x : Fin 5) (limb : Fin 4) : α :=
  if y = 0 ∧ x = 0 then row.aPrimePrimePrime00Limbs[limb] else row.aPrimePrimeLimb y x limb

section Map
variable {β : Type} (f : α → β) (row : Row α)

@[simp] lemma map_stepFlags : (row.map f).stepFlags = row.stepFlags.map f := rfl
@[simp] lemma map_exportFlag : (row.map f).exportFlag = f row.exportFlag := rfl
@[simp] lemma map_aPrimePrime00Bits :
    (row.map f).aPrimePrime00Bits = row.aPrimePrime00Bits.map f := rfl
@[simp] lemma map_aPrimePrimePrime00Limbs :
    (row.map f).aPrimePrimePrime00Limbs = row.aPrimePrimePrime00Limbs.map f := rfl
@[simp] lemma map_preimageLimb (y x limb) :
    (row.map f).preimageLimb y x limb = f (row.preimageLimb y x limb) := by
  simp [map, preimageLimb]
@[simp] lemma map_aLimb (y x limb) : (row.map f).aLimb y x limb = f (row.aLimb y x limb) := by
  simp [map, aLimb]
@[simp] lemma map_cBit (x z) : (row.map f).cBit x z = f (row.cBit x z) := by
  simp [map, cBit]
@[simp] lemma map_cPrimeBit (x z) : (row.map f).cPrimeBit x z = f (row.cPrimeBit x z) := by
  simp [map, cPrimeBit]
@[simp] lemma map_aPrimeBit (y x z) : (row.map f).aPrimeBit y x z = f (row.aPrimeBit y x z) := by
  simp [map, aPrimeBit]
@[simp] lemma map_aPrimePrimeLimb (y x limb) :
    (row.map f).aPrimePrimeLimb y x limb = f (row.aPrimePrimeLimb y x limb) := by
  simp [map, aPrimePrimeLimb]
@[simp] lemma map_b (x y z) : (row.map f).b x y z = f (row.b x y z) := by
  simp [b]
@[simp] lemma map_aPrimePrimePrimeLimb (y x limb) :
    (row.map f).aPrimePrimePrimeLimb y x limb = f (row.aPrimePrimePrimeLimb y x limb) := by
  simp only [aPrimePrimePrimeLimb]
  split <;> simp [map, aPrimePrimeLimb]

end Map

end Row

/-- Apply `f` to every cell of a window. -/
def mapWindow {α β : Type} (f : α → β) (window : Window Row α) : Window Row β where
  current := window.current.map f
  next := window.next.map f
  isFirstRow := f window.isFirstRow
  isLastRow := f window.isLastRow
  isTransition := f window.isTransition

section Constraints
variable {α : Type} [Add α] [Sub α] [Mul α] [OfNat α 1] [OfNat α 2] [OfNat α 4]

/-- Plonky3's `bool_check`: zero exactly on 0 and 1. -/
def boolCheck (x : α) : α := x * (x - (1 : α))

/-- Plonky3's `xor` of two bits. -/
def xor (x y : α) : α := x + y - x * ((2 : α) * y)

/-- Plonky3's `andn` of two bits: `!x & y`. -/
def andn (x y : α) : α := ((1 : α) - x) * y

/-- The bits `15 - n, ..., 15` of a 16-bit limb, by Horner's rule from the top bit, as Plonky3 folds
them. -/
def horner (bit : Fin 16 → α) : ℕ → α
  | 0 => bit 15
  | n + 1 => (2 : α) * horner bit n + bit (Fin.ofNat 16 (14 - n))

/-- Limb `limb` of a lane, from the lane's bits. -/
def limbOf (bit : Fin 64 → α) (limb : Fin 4) : α :=
  horner (fun k => bit (limbBit limb k)) 15

/-- Bit `z` of ι's output `A'''[0, 0]`, from bit `z` of `A''[0, 0]`: Plonky3 xors it with the sum
of the step flags of the rounds whose round constant has bit `z` set, and skips the xor if there
are none. -/
def iotaBit (stepFlags : Vector α 24) (bit : α) (z : Fin 64) : α :=
  match (List.finRange 24).filter (roundConstantBit · z) with
  | [] => bit
  | r :: rs => xor (rs.foldl (fun sum r => sum + stepFlags[r]) stepFlags[r]) bit

/-- The round flags start at round 0 and advance by one round per row. -/
def roundFlagConstraints (window : Window Row α) : List α :=
  let current := window.current
  window.isFirstRow * (current.stepFlags[0] - (1 : α)) ::
    (List.finRange 23).map (fun (i : Fin 23) => window.isFirstRow * current.stepFlags[i.succ]) ++
    (List.finRange 24).map fun (i : Fin 24) =>
      window.isTransition * (current.stepFlags[i] - window.next.stepFlags[i + 1])

/-- Transitions to a row of the same permutation. -/
def transitionInPermutation (window : Window Row α) : α :=
  window.isTransition * ((1 : α) - window.current.stepFlags[23])

/-- The first round's input is the preimage, and the preimage is the same along a permutation. -/
def preimageConstraints (window : Window Row α) : List α :=
  let current := window.current
  let firstStep := current.stepFlags[0]
  let sameBlock := transitionInPermutation window
  ((List.finRange 5).flatMap fun y => (List.finRange 5).flatMap fun x =>
    (List.finRange 4).map fun limb => firstStep * (current.preimageLimb y x limb -
      current.aLimb y x limb)) ++
  (List.finRange 5).flatMap fun y => (List.finRange 5).flatMap fun x =>
    (List.finRange 4).map fun limb => sameBlock * (current.preimageLimb y x limb -
      window.next.preimageLimb y x limb)

/-- The export flag is boolean and only set on the last round. -/
def exportConstraints (window : Window Row α) : List α :=
  let current := window.current
  [boolCheck current.exportFlag, ((1 : α) - current.stepFlags[23]) * current.exportFlag]

/-- θ: `C` is boolean and `C'[x] = C[x] ^ C[x - 1] ^ rot(C[x + 1], 1)`. -/
def thetaColumnConstraints (window : Window Row α) : List α :=
  let current := window.current
  (List.finRange 5).flatMap fun x =>
    (List.finRange 64).map (fun z => boolCheck (current.cBit x z)) ++
    (List.finRange 64).map fun z => current.cPrimeBit x z -
      xor (xor (current.cBit x z) (current.cBit (x + 4) z)) (current.cBit (x + 1) (z - 1))

/-- θ: `A'` is boolean, and `A = A' ^ C ^ C'`, which also range checks the limbs of `A`. -/
def thetaConstraints (window : Window Row α) : List α :=
  let current := window.current
  (List.finRange 5).flatMap fun x =>
    let cXorCPrime : Vector α 64 := .ofFn fun z => xor (current.cBit x z) (current.cPrimeBit x z)
    (List.finRange 5).flatMap fun y =>
      (List.finRange 64).map (fun z => boolCheck (current.aPrimeBit y x z)) ++
      (List.finRange 4).map fun limb =>
        limbOf (fun z => xor (current.aPrimeBit y x z) cXorCPrime[z]) limb -
          current.aLimb y x limb

/-- θ: the parity of `A'[x, 0], ..., A'[x, 4]` is `C'[x]`, so `C` are the column parities of `A`. -/
def parityConstraints (window : Window Row α) : List α :=
  let current := window.current
  (List.finRange 5).flatMap fun x => (List.finRange 64).map fun z =>
    let sum := current.aPrimeBit 0 x z + current.aPrimeBit 1 x z + current.aPrimeBit 2 x z +
      current.aPrimeBit 3 x z + current.aPrimeBit 4 x z
    let diff := sum - current.cPrimeBit x z
    diff * (diff - (2 : α)) * (diff - (4 : α))

/-- χ: `A''[x, y] = B[x, y] ^ (~B[x + 1, y] & B[x + 2, y])`, which also range checks `A''`. -/
def chiConstraints (window : Window Row α) : List α :=
  let current := window.current
  (List.finRange 5).flatMap fun y => (List.finRange 5).flatMap fun x =>
    (List.finRange 4).map fun limb =>
      limbOf (fun z => xor (andn (current.b (x + 1) y z) (current.b (x + 2) y z))
        (current.b x y z)) limb - current.aPrimePrimeLimb y x limb

/-- ι: the bits of `A''[0, 0]`, and `A'''[0, 0] = A''[0, 0] ^ RC`. -/
def iotaConstraints (window : Window Row α) : List α :=
  let current := window.current
  (List.finRange 64).map (fun z => boolCheck current.aPrimePrime00Bits[z]) ++
  (List.finRange 4).map (fun limb =>
    limbOf (fun z => current.aPrimePrime00Bits[z]) limb - current.aPrimePrimeLimb 0 0 limb) ++
  (List.finRange 4).map fun limb =>
    limbOf (fun z => iotaBit current.stepFlags current.aPrimePrime00Bits[z] z) limb -
      current.aPrimePrimePrime00Limbs[limb]

/-- The round's output is the next round's input, within a permutation. -/
def outputConstraints (window : Window Row α) : List α :=
  let sameBlock := transitionInPermutation window
  (List.finRange 5).flatMap fun x => (List.finRange 5).flatMap fun y =>
    (List.finRange 4).map fun limb => sameBlock * (window.current.aPrimePrimePrimeLimb y x limb -
      window.next.aLimb y x limb)

/-- All constraints of a window, in Plonky3's order. -/
def constraints (window : Window Row α) : List α :=
  roundFlagConstraints window ++ preimageConstraints window ++ exportConstraints window ++
    thetaColumnConstraints window ++ thetaConstraints window ++ parityConstraints window ++
    chiConstraints window ++ iotaConstraints window ++ outputConstraints window

end Constraints
end KeccakAir
