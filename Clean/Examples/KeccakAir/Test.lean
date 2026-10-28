module

public import Clean.Examples.KeccakAir.Ensemble
public import Clean.Backends.Program

-- `#guard` runs compiled code from these modules.
public meta import Clean.Examples.KeccakAir.Ensemble
public meta import Clean.Backends.Program

@[expose] public section

namespace KeccakAir.Test

open Air.Flat Air.Flat.WitnessGeneration Backends

abbrev F := _root_.F KoalaBear.fieldSize

/-!
## Reference constraints

Plonky3's `KeccakAir::eval` at a4982ec, transcribed into expressions over the cells of a window:
`cur i` and `next i` read column `i` of the current and the next row. The fingerprint of these
expressions (their values at pseudorandom points, in emission order) matches Plonky3's symbolic
constraints on all 3182 constraints.
-/
namespace Reference

inductive Expr where
  | cur (i : ℕ)
  | next (i : ℕ)
  | const (c : ℕ)
  | isFirstRow
  | isLastRow
  | isTransition
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)

instance : Add Expr := ⟨.add⟩
instance : Sub Expr := ⟨.sub⟩
instance : Mul Expr := ⟨.mul⟩

/-- The value of an expression on a window: its row's cells, the next row's and the selectors. -/
def Expr.eval (cells : Array F) (width : ℕ) : Expr → F
  | .cur i => cells[i]!
  | .next i => cells[width + i]!
  | .const c => c
  | .isFirstRow => cells[2 * width]!
  | .isLastRow => cells[2 * width + 1]!
  | .isTransition => cells[2 * width + 2]!
  | .add a b => a.eval cells width + b.eval cells width
  | .sub a b => a.eval cells width - b.eval cells width
  | .mul a b => a.eval cells width * b.eval cells width

def R : Array (Array ℕ) := #[#[0, 36, 3, 41, 18], #[1, 44, 10, 45, 2], #[62, 6, 43, 15, 61],
  #[28, 55, 25, 21, 56], #[27, 20, 39, 8, 14]]

def RC : Array ℕ := #[0x0000000000000001, 0x0000000000008082, 0x800000000000808A,
  0x8000000080008000, 0x000000000000808B, 0x0000000080000001, 0x8000000080008081,
  0x8000000000008009, 0x000000000000008A, 0x0000000000000088, 0x0000000080008009,
  0x000000008000000A, 0x000000008000808B, 0x800000000000008B, 0x8000000000008089,
  0x8000000000008003, 0x8000000000008002, 0x8000000000000080, 0x000000000000800A,
  0x800000008000000A, 0x8000000080008081, 0x8000000000008080, 0x0000000080000001,
  0x8000000080008008]

def exportCol := 24
def preimage (y x l : ℕ) := 25 + (y * 5 + x) * 4 + l
def aCol (y x l : ℕ) := 125 + (y * 5 + x) * 4 + l
def cCol (x z : ℕ) := 225 + x * 64 + z
def cpCol (x z : ℕ) := 545 + x * 64 + z
def apCol (y x z : ℕ) := 865 + (y * 5 + x) * 64 + z
def appCol (y x l : ℕ) := 2465 + (y * 5 + x) * 4 + l
def app00bit (z : ℕ) := 2565 + z
def appp00 (l : ℕ) := 2629 + l
def width := 2633

def bCol (x y z : ℕ) : ℕ :=
  let a := (x + 3 * y) % 5
  let rot := (R.getD a #[]).getD x 0
  apCol x a ((z + 64 - rot) % 64)

def apppCol (y x l : ℕ) : ℕ := if y = 0 ∧ x = 0 then appp00 l else appCol y x l

def c (n : ℕ) : Expr := .const n
def cur (i : ℕ) : Expr := .cur i
def nxt (i : ℕ) : Expr := .next i
def xor (a b : Expr) : Expr := a + b - a * (c 2 * b)
def andn (a b : Expr) : Expr := (c 1 - a) * b
def boolCheck (x : Expr) : Expr := x * (x - c 1)
def limbOf (bit : ℕ → Expr) (limb : ℕ) : Expr :=
  (List.range 15).foldl (fun acc k => c 2 * acc + bit (limb * 16 + 14 - k)) (bit (limb * 16 + 15))

def grid {α : Type} (f : ℕ → ℕ → List α) : List α :=
  (List.range 5).flatMap fun i => (List.range 5).flatMap fun j => f i j
def limbs {α : Type} (f : ℕ → α) : List α := (List.range 4).map f

def constraints : List Expr :=
  let tnf : Expr := .isTransition * (c 1 - cur 23)
  let flags := [.isFirstRow * (cur 0 - c 1)] ++
    (List.range 23).map (fun i => .isFirstRow * cur (i + 1)) ++
    (List.range 24).map fun i => .isTransition * (cur i - nxt ((i + 1) % 24))
  let firstPre := grid fun y x => limbs fun l => cur 0 * (cur (preimage y x l) - cur (aCol y x l))
  let tPre := grid fun y x => limbs fun l => tnf * (cur (preimage y x l) - nxt (preimage y x l))
  let exp := [boolCheck (cur exportCol), (c 1 - cur 23) * cur exportCol]
  let cs := (List.range 5).flatMap fun x =>
    (List.range 64).map (fun z => boolCheck (cur (cCol x z))) ++
    (List.range 64).map fun z => cur (cpCol x z) - xor (xor (cur (cCol x z))
      (cur (cCol ((x + 4) % 5) z))) (cur (cCol ((x + 1) % 5) ((z + 63) % 64)))
  let aps := (List.range 5).flatMap fun x =>
    let cxc (z : ℕ) : Expr := xor (cur (cCol x z)) (cur (cpCol x z))
    (List.range 5).flatMap fun y =>
      (List.range 64).map (fun z => boolCheck (cur (apCol y x z))) ++
      limbs fun l => limbOf (fun z => xor (cur (apCol y x z)) (cxc z)) l - cur (aCol y x l)
  let parity := (List.range 5).flatMap fun x => (List.range 64).map fun z =>
    let sum := (List.range 4).foldl (fun s y => s + cur (apCol (y + 1) x z)) (cur (apCol 0 x z))
    let diff := sum - cur (cpCol x z)
    diff * (diff - c 2) * (diff - c 4)
  let chi := grid fun y x => limbs fun l =>
    limbOf (fun z => xor (andn (cur (bCol ((x + 1) % 5) y z)) (cur (bCol ((x + 2) % 5) y z)))
      (cur (bCol x y z))) l - cur (appCol y x l)
  let bits := (List.range 64).map (fun z => boolCheck (cur (app00bit z))) ++
    limbs fun l => limbOf (fun z => cur (app00bit z)) l - cur (appCol 0 0 l)
  let rcBit (i : ℕ) : Expr :=
    match (List.range 24).filter (fun r => (RC.getD r 0).testBit i) with
    | [] => c 0
    | r :: rs => rs.foldl (fun s r => s + cur r) (cur r)
  let iota := limbs fun l => limbOf (fun z => xor (rcBit z) (cur (app00bit z))) l - cur (appp00 l)
  let out := (List.range 5).flatMap fun x => (List.range 5).flatMap fun y =>
    limbs fun l => tnf * (cur (apppCol y x l) - nxt (aCol y x l))
  flags ++ firstPre ++ tPre ++ exp ++ cs ++ aps ++ parity ++ chi ++ bits ++ iota ++ out

end Reference

/-! ## The lowered constraints are Plonky3's -/

def program : Except LoweringError (ComponentProgram F) := do
  let program ← lower (ensemble (p := KoalaBear.fieldSize) 32) 10
  match program.components with
  | [component] => return component
  | _ => throw (.validation (.preallocatedHeight "keccak" 0))

/-- Pseudorandom field elements (SplitMix64). -/
def samples (seed : UInt64) (n : ℕ) : Array F := Id.run do
  let mut state := seed
  let mut values := #[]
  for _ in [0:n] do
    state := state + 0x9e3779b97f4a7c15
    let z := (state ^^^ (state >>> 30)) * 0xbf58476d1ce4e5b9
    let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
    values := values.push ((z ^^^ (z >>> 31)).toNat : F)
  return values

/-- The lowered constraints, each times the value of its gate, at a point. -/
def loweredValues (cells : Array F) : List F :=
  match program with
  | .error _ => []
  | .ok component => component.constraints.map fun constraint =>
    let gate : F := match constraint.gate with
      | .everyRow => 1
      | .firstRow => cells[2 * size Row]!
      | .lastRow => cells[2 * size Row + 1]!
      | .transition => cells[2 * size Row + 2]!
    gate * constraint.body.eval (Environment.fromArray cells fun _ _ => #[])

-- 3182 constraints, of which 24 on the first row and 224 on transitions, as in Plonky3.
#guard (program.toOption.map fun component => (component.constraints.length,
  (component.constraints.filter (·.gate == .firstRow)).length,
  (component.constraints.filter (·.gate == .transition)).length)) = some (3182, 24, 224)

-- At pseudorandom points, the lowered constraints are the reference constraints, in order.
#guard [1, 2, 3].all fun seed =>
  let cells := samples seed (2 * size Row + 3)
  loweredValues cells == Reference.constraints.map (·.eval cells (size Row))

/-! ## Plonky3's trace satisfies the constraints and computes Keccak-f

`plonky3-trace.txt` is the trace of Plonky3's `generate_trace_rows` (at a4982ec, over KoalaBear) for
one permutation, whose lane `i` (lane `(x, y)` at `x + 5 y`) is `(i + 1) * 0x0123456789abcdef`: its
24 rows and 8 rows of the permutation of the zero state. A line is a row; a cell is `0`, `1`, or `x`
and four hex digits.
-/

/-- The cells of a line of `plonky3-trace.txt`. -/
def parseCells : List Char → List F
  | 'x' :: a :: b :: c :: d :: rest =>
    (([a, b, c, d].foldl (fun n digit => 16 * n + if digit.isDigit then digit.toNat - '0'.toNat
      else digit.toNat - 'a'.toNat + 10) 0 : ℕ) : F) :: parseCells rest
  | digit :: rest => (if digit = '1' then 1 else 0) :: parseCells rest
  | [] => []

def traceRows : Array (Array F) :=
  (((include_str "plonky3-trace.txt").splitOn "\n").filter (· ≠ "")).toArray.map
    fun line => (parseCells line.toList).toArray

/-- Row `i` with its window cells. -/
def windowCells (rows : Array (Array F)) (i : ℕ) : Array F :=
  rows[i]! ++ rows[(i + 1) % rows.size]! ++
    #[if i = 0 then 1 else 0, if i + 1 = rows.size then 1 else 0,
      if i + 1 = rows.size then 0 else 1]

def satisfies (rows : Array (Array F)) : Bool :=
  match program with
  | .error _ => false
  | .ok component => (List.range rows.size).all fun i =>
    component.constraintsHold (windowCells rows i) fun _ _ => #[]

/-- The state in `Specs.Keccak256`'s order whose lane `(x, y)` has the limbs `column y x l` of a
row. -/
def specState (row : Array F) (column : ℕ → ℕ → ℕ → ℕ) : Vector ℕ 25 :=
  Vector.ofFn fun i => (List.range 4).foldl (fun lane l =>
    lane + 2 ^ (16 * l) * (row[column (i.val % 5) (i.val / 5) l]!).val) 0

-- One permutation and its padding, 32 rows, satisfy the constraints.
#guard traceRows.size = 32 && traceRows.all (·.size = size Row) && satisfies traceRows

-- The last round's output is Keccak-f of the first round's preimage.
#guard specState traceRows[23]! Reference.apppCol =
  Specs.Keccak256.keccakPermutation (specState traceRows[0]! Reference.preimage)

-- Flipping a bit of `A'`, a preimage limb on a later row, or a step flag violates the constraints.
#guard !satisfies (traceRows.modify 3 fun row => row.modify 900 (1 - ·))
#guard !satisfies (traceRows.modify 5 fun row => row.modify 30 (· + 1))
#guard !satisfies (traceRows.modify 0 fun row => (row.set! 0 0).set! 1 1)

/-! ## Witness generation copies the trace

Generation copies every cell from the hint table, interpreted by `#guard`, so this checks a table of
two rows: the first two rounds of the permutation.
-/

def proverInput : (ensemble (p := KoalaBear.fieldSize) 2).ProverInput F :=
  Vector.ofFn fun i => (traceRows[i.val / size Row]!)[i.val % size Row]!

def generated : Except String (List (List F) × Bool) :=
  match WitnessGeneration.generate (ensemble (p := KoalaBear.fieldSize) 2) 10 () proverInput with
  | .error error => .error (toString error)
  | .ok witness => .ok (witness.tables.flatMap fun table =>
      table.table.map fun row => (row.extract 0 (size Row)).toList, constraintsHold witness)

#guard generated = .ok ((traceRows.toList.take 2).map (·.toList), true)

end KeccakAir.Test
