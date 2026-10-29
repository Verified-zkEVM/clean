/-
The columns of Plonky3's Keccak-f AIR (`p3-keccak-air`), in Plonky3's order.

Every row computes one round of Keccak-f, and 24 consecutive rows one permutation. The one-hot
`stepFlags` say which round a row computes. A row holds the round's input state `a` in 16-bit limbs,
the bits of θ's column parities `c` and `cPrime` and of θ's output `aPrime`, which ρ and π only
rotate and move, χ's output `aPrimePrime` in limbs, and ι's output lane `(0, 0)`. The next row's
input is this row's output, unless this row computes the last round.

Lanes are indexed by `(x, y)`, and a state is stored `y`-major: lane `(x, y)` is at `5 y + x`, as in
the Keccak specification's `s[w (5 y + x) + z] = a[x][y][z]`.
-/
module

public import Clean.Air.Window
public import Clean.Gadgets.Boolean
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

/-- The limbs of lane `(x, y)` of the round's input `A`. -/
def aLane (row : Row α) (y x : Fin 5) : Vector α 4 := .ofFn (row.aLimb y x)
/-- The bits of θ's column parity `C[x]`. -/
def cLane (row : Row α) (x : Fin 5) : Vector α 64 := .ofFn (row.cBit x)
/-- The bits of `C'[x]`. -/
def cPrimeLane (row : Row α) (x : Fin 5) : Vector α 64 := .ofFn (row.cPrimeBit x)
/-- The bits of lane `(x, y)` of θ's output `A'`. -/
def aPrimeLane (row : Row α) (y x : Fin 5) : Vector α 64 := .ofFn (row.aPrimeBit y x)
/-- The bits of lane `(x, y)` of `B`, the output of ρ and π. -/
def bLane (row : Row α) (x y : Fin 5) : Vector α 64 := .ofFn (row.b x y)
/-- The limbs of lane `(x, y)` of χ's output `A''`. -/
def aPrimePrimeLane (row : Row α) (y x : Fin 5) : Vector α 4 := .ofFn (row.aPrimePrimeLimb y x)
/-- The limbs of lane `(x, y)` of the round's output `A'''`. -/
def aPrimePrimePrimeLane (row : Row α) (y x : Fin 5) : Vector α 4 :=
  .ofFn (row.aPrimePrimePrimeLimb y x)

lemma getElem_cLane (row : Row α) (x : Fin 5) (z : ℕ) (hz : z < 64) :
    (row.cLane x)[z] = row.cBit x ⟨z, hz⟩ := by
  simp [cLane]

lemma getElem_cPrimeLane (row : Row α) (x : Fin 5) (z : ℕ) (hz : z < 64) :
    (row.cPrimeLane x)[z] = row.cPrimeBit x ⟨z, hz⟩ := by
  simp [cPrimeLane]

lemma getElem_aPrimeLane (row : Row α) (y x : Fin 5) (z : ℕ) (hz : z < 64) :
    (row.aPrimeLane y x)[z] = row.aPrimeBit y x ⟨z, hz⟩ := by
  simp [aPrimeLane]

section Map
variable {β : Type} (f : α → β) (row : Row α)

@[simp] lemma map_stepFlags : (row.map f).stepFlags = row.stepFlags.map f := rfl
@[simp] lemma map_exportFlag : (row.map f).exportFlag = f row.exportFlag := rfl
@[simp] lemma map_preimage : (row.map f).preimage = row.preimage.map f := rfl
@[simp] lemma map_a : (row.map f).a = row.a.map f := rfl
@[simp] lemma map_c : (row.map f).c = row.c.map f := rfl
@[simp] lemma map_cPrime : (row.map f).cPrime = row.cPrime.map f := rfl
@[simp] lemma map_aPrime : (row.map f).aPrime = row.aPrime.map f := rfl
@[simp] lemma map_aPrimePrime : (row.map f).aPrimePrime = row.aPrimePrime.map f := rfl
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
@[simp] lemma map_aLane (y x) : (row.map f).aLane y x = (row.aLane y x).map f := by
  ext; simp [aLane]
@[simp] lemma map_cLane (x) : (row.map f).cLane x = (row.cLane x).map f := by
  ext; simp [cLane]
@[simp] lemma map_cPrimeLane (x) : (row.map f).cPrimeLane x = (row.cPrimeLane x).map f := by
  ext; simp [cPrimeLane]
@[simp] lemma map_aPrimeLane (y x) : (row.map f).aPrimeLane y x = (row.aPrimeLane y x).map f := by
  ext; simp [aPrimeLane]
@[simp] lemma map_aPrimePrimeLane (y x) :
    (row.map f).aPrimePrimeLane y x = (row.aPrimePrimeLane y x).map f := by
  ext; simp [aPrimePrimeLane]
@[simp] lemma map_aPrimePrimePrimeLane (y x) :
    (row.map f).aPrimePrimePrimeLane y x = (row.aPrimePrimePrimeLane y x).map f := by
  ext; simp [aPrimePrimePrimeLane]

end Map

end Row

/-- Plonky3's check that `c` is the parity of the bits `a0, ..., a4`: their difference is 0, 2 or 4.
-/
def parityCheck {α : Type} [Add α] [Sub α] [Mul α] [OfNat α 2] [OfNat α 4] (a0 a1 a2 a3 a4 c : α) :
    α :=
  let diff := a0 + a1 + a2 + a3 + a4 - c
  diff * (diff - (2 : α)) * (diff - (4 : α))

/-- A window transitions to a row of the same permutation: it is not the last row, and does not
compute the last round. -/
def transitionInPermutation {α : Type} [Sub α] [Mul α] [OfNat α 1] (window : Window Row α) : α :=
  window.isTransition * ((1 : α) - window.current.stepFlags[23])

/-- Apply `f` to every cell of a window. -/
def mapWindow {α β : Type} (f : α → β) (window : Window Row α) : Window Row β where
  current := window.current.map f
  next := window.next.map f
  isFirstRow := f window.isFirstRow
  isLastRow := f window.isLastRow
  isTransition := f window.isTransition

section MapWindow
variable {α β : Type} (f : α → β) (window : Window Row α)

@[simp] lemma mapWindow_current : (mapWindow f window).current = window.current.map f := rfl
@[simp] lemma mapWindow_next : (mapWindow f window).next = window.next.map f := rfl
@[simp] lemma mapWindow_isFirstRow : (mapWindow f window).isFirstRow = f window.isFirstRow := rfl
@[simp] lemma mapWindow_isLastRow : (mapWindow f window).isLastRow = f window.isLastRow := rfl
@[simp] lemma mapWindow_isTransition :
    (mapWindow f window).isTransition = f window.isTransition := rfl

end MapWindow

section Eval
variable {p : ℕ} [Fact p.Prime] (env : Environment (F p))

/-- A row's values are its expressions' values. -/
lemma eval_row (row : Var Row (F p)) : eval env row = row.map (Expression.eval env) := by
  obtain ⟨⟩ := row
  simp only [circuit_norm, Row.map]

lemma provableStructEval_row (row : Var Row (F p)) :
    ProvableStruct.eval env row = row.map (Expression.eval env) := by
  obtain ⟨⟩ := row
  simp only [circuit_norm, Row.map]

/-- A window's values are its expressions' values. -/
lemma eval_window (window : Var (Window Row) (F p)) :
    eval env window = mapWindow (Expression.eval env) window := by
  obtain ⟨⟨⟩, ⟨⟩, _, _, _⟩ := window
  simp only [circuit_norm, mapWindow, Row.map]

@[circuit_norm]
lemma eval_parityCheck (a0 a1 a2 a3 a4 c : Expression (F p)) :
    Expression.eval env (parityCheck a0 a1 a2 a3 a4 c) =
      parityCheck (Expression.eval env a0) (Expression.eval env a1) (Expression.eval env a2)
        (Expression.eval env a3) (Expression.eval env a4) (Expression.eval env c) := by
  simp only [parityCheck, circuit_norm]

lemma provableStructEval_window (window : Var (Window Row) (F p)) :
    ProvableStruct.eval env window = mapWindow (Expression.eval env) window := by
  obtain ⟨⟨⟩, ⟨⟩, _, _, _⟩ := window
  simp only [circuit_norm, mapWindow, Row.map]

lemma transitionInPermutation_eval (window : Var (Window Row) (F p)) :
    transitionInPermutation (mapWindow (Expression.eval env) window) =
      Expression.eval env (transitionInPermutation window) := by
  simp only [transitionInPermutation, mapWindow, Row.map, circuit_norm]

end Eval

/-- The four 16-bit limbs of 64 bits, lowest first. -/
def limbBits {α : Type} (bits : Vector α 64) : Vector (Vector α 16) 4 :=
  .ofFn fun limb => .ofFn fun k => bits[limbBit limb k]

/-- Bit `z` of ι's output `A'''[0, 0]`, from bit `z` of `A''[0, 0]`: Plonky3 xors it with the sum
of the step flags of the rounds whose round constant has bit `z` set, and skips the xor if there
are none. -/
def iotaBit {α : Type} [Add α] [Sub α] [Mul α] [OfNat α 2] (stepFlags : Vector α 24) (bit : α)
    (z : Fin 64) : α :=
  match (List.finRange 24).filter (roundConstantBit · z) with
  | [] => bit
  | r :: rs => bitXor (rs.foldl (fun sum r => sum + stepFlags[r]) stepFlags[r]) bit

end KeccakAir
