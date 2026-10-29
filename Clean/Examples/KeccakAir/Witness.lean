/-
The witness of Plonky3's Keccak-f AIR as a segment program: 24 rows per permutation, as Plonky3's
`generate_trace_rows` computes them. The first row of a permutation reads its input from the hint
`keccak`, every later row continues from the previous row's output, and every row computes its
round on 64-bit lanes and stores them as limbs and bits.
-/
module

public import Clean.Air.RowProgram
public import Clean.Examples.KeccakAir.Row

@[expose] public section

namespace KeccakAir.Witness
open Witgen Specs.Keccak256

variable {F : Type} [Field F]

/-- A Keccak-f state as 64-bit lanes, indexed `(x, y)`. -/
abbrev Lanes (F : Type) := Fin 5 → Fin 5 → U64Expr F

/-- The lane of four 16-bit limbs, lowest first. -/
def laneOf (limb : Fin 4 → FExpr F) : U64Expr F :=
  (limb 0).val ||| ((limb 1).val <<< 16) ||| ((limb 2).val <<< 32) ||| ((limb 3).val <<< 48)

/-- `value` rotated left by `offset < 64`. -/
def rotateLeft (value : U64Expr F) (offset : ℕ) : U64Expr F :=
  if offset = 0 then value else (value <<< offset) ||| (value >>> (64 - offset))

/-- Limb `limb` of a lane, as a field element. -/
def limb (value : U64Expr F) (limb : Fin 4) : FExpr F :=
  ((value >>> (16 * limb.val)) &&& (0xffff : U64Expr F)).toField

/-- Bit `z` of a lane, as a field element. -/
def bit (value : U64Expr F) (z : Fin 64) : FExpr F :=
  ((value >>> z.val) &&& (1 : U64Expr F)).toField

/-- Bind `n` values as steps. -/
def letUs (n : ℕ) (value : Fin n → U64Expr F) : M F (Vector (U64Expr F) n) :=
  (Vector.ofFn value).mapM letU

/-- Bind the 25 lanes of a state as steps. -/
def letLanes (value : Lanes F) : M F (Lanes F) := do
  let lanes ← letUs 25 fun i => value ⟨i.val / 5, by omega⟩ ⟨i.val % 5, by omega⟩
  return fun x y => lanes[5 * x.val + y.val]

/-- The round constant of round `round`, read limb by limb from a table of the 24 constants. -/
def roundConstant (round : U64Expr F) : U64Expr F :=
  laneOf fun l => .listGet (roundConstants.toList.map fun constant =>
    .const (((constant >>> (16 * l.val).toUInt64) &&& 0xffff).toNat : F)) round

/-- The row of round `round` of the permutation of `preimage`, whose input is the state `a`:
Plonky3's `generate_trace_row_for_round`. -/
def roundRow (preimage : Vector (FExpr F) 100) (a : Lanes F) (round : U64Expr F) :
    M F (Row (FExpr F)) := do
  let c ← letUs 5 fun x => a x 0 ^^^ a x 1 ^^^ a x 2 ^^^ a x 3 ^^^ a x 4
  let c' ← letUs 5 fun x => c[x] ^^^ c[x + 4] ^^^ rotateLeft c[x + 1] 1
  let a' ← letLanes fun x y => a x y ^^^ c[x] ^^^ c'[x]
  -- `B[x, y] = rot(A'[x + 3 y, x], r[x + 3 y][x])`, ρ and π
  let b ← letLanes fun x y => rotateLeft (a' (x + 3 * y) x) (rotationOffsets[x + 3 * y][x]).val
  -- χ
  let a'' ← letLanes fun x y => b x y ^^^ ((b (x + 1) y ^^^ (0xffffffffffffffff : U64Expr F)) &&&
    b (x + 2) y)
  -- ι
  let a'''00 ← letU (a'' 0 0 ^^^ roundConstant round)
  return {
    stepFlags := .ofFn fun r => .ite (.neq round (r.val : U64Expr F)) 1 0
    exportFlag := 0
    preimage
    a := .ofFn fun i => limb (a (limbX i) (limbY i)) (limbOfIndex i)
    c := .ofFn fun i => bit c[columnOfIndex i] (columnBitOfIndex i)
    cPrime := .ofFn fun i => bit c'[columnOfIndex i] (columnBitOfIndex i)
    aPrime := .ofFn fun i => bit (a' (bitX i) (bitY i)) (bitOfIndex i)
    aPrimePrime := .ofFn fun i => limb (a'' (limbX i) (limbY i)) (limbOfIndex i)
    aPrimePrime00Bits := .ofFn fun z => bit (a'' 0 0) z
    aPrimePrimePrime00Limbs := .ofFn fun l => limb a'''00 l
  }
where
  limbX (i : Fin 100) : Fin 5 := ⟨i.val / 4 % 5, by omega⟩
  limbY (i : Fin 100) : Fin 5 := ⟨i.val / 20, by omega⟩
  limbOfIndex (i : Fin 100) : Fin 4 := ⟨i.val % 4, by omega⟩
  columnOfIndex (i : Fin 320) : Fin 5 := ⟨i.val / 64, by omega⟩
  columnBitOfIndex (i : Fin 320) : Fin 64 := ⟨i.val % 64, by omega⟩
  bitX (i : Fin 1600) : Fin 5 := ⟨i.val / 64 % 5, by omega⟩
  bitY (i : Fin 1600) : Fin 5 := ⟨i.val / 320, by omega⟩
  bitOfIndex (i : Fin 1600) : Fin 64 := ⟨i.val % 64, by omega⟩

/-- The first row of a permutation: round 0 of the permutation whose input is row `i / 24` of the
hint `keccak`, the 100 16-bit limbs of the input lanes in the order of the `preimage` columns. -/
def first (i : U64Expr F) : M F (Row (FExpr F)) := do
  let round ← letU (i % 24)
  let preimage := Vector.ofFn fun j : Fin 100 => FExpr.hintGet "keccak" 100 (i / 24) j
  let a ← letLanes fun x y => laneOf fun l => preimage[limbIndex y x l]
  roundRow preimage a round

/-- A later row of a permutation: its preimage is the previous row's, its input the previous row's
output. -/
def next (i : U64Expr F) (previous : Row (Expression F)) : M F (Row (FExpr F)) := do
  let round ← letU (i % 24)
  let a ← letLanes fun x y => laneOf fun l => previous.aPrimePrimePrimeLimb y x l
  roundRow (previous.preimage.map .expr) a round

/-- The trace of the Keccak-f AIR, 24 rows per permutation. -/
def program : SegmentProgram F where
  Row
  length := 24
  first
  next

end KeccakAir.Witness
