module

public import Clean.Air.FlatComponent
public import CompPoly.Fields.Montgomery.Native32Field

@[expose] public section

/-!
# Compiling witness IR to register programs

Fast witness generation evaluates witness IR over CompPoly's Montgomery field `FastField p`, writing
rows of packed words as CompStark's fast prover reads them: each cell as the 32-bit Montgomery word
of its value, little-endian, rows one after the other. Rather than walking the IR's trees, it runs a
register program compiled from them (`Clean.Air.FastWitness.Run` runs it).

A register holds a 64-bit word: a `u64` value, a condition (`0` or `1`), or the Montgomery word of
a field element, which is canonical, so that field equality is word equality. Constants live in
registers set once. Every IR step gets a register; output cells are stores into the row.

The compiler recognizes the cells that a row stores most: the bit `(x >>> s) &&& 1` of a `u64` value
is a store of `0` or the word of `1`, and runs of such bits of one value are one instruction; a
value below `p` enters Montgomery form without a reduction modulo `p`; and runs of cells copied from
the previous row are one copy.
-/

namespace Air.Flat.FastWitness
open Witgen Montgomery.Native32

/-- Binary operations on register words: `u64` operations as Lean's `UInt64` ones (`x / 0 = 0`,
`x % 0 = x`, shifts by the amount modulo 64), comparisons valued `0` or `1`, and field operations on
Montgomery words. -/
inductive BinaryOp where
  | add | mul | div | mod | and | or | xor | shiftLeft | shiftRight
  | eq | lt
  | fieldAdd | fieldMul
deriving Repr, BEq, Inhabited

/-- An instruction of a register program. `dest`, `source` and the like are registers, `column` is
a cell of the current row, `previousColumn` one of the previous row. -/
inductive Instr where
  | binary (op : BinaryOp) (dest left right : ℕ)
  /-- `dest := if condition ≠ 0 then yes else no`. -/
  | select (dest condition yes no : ℕ)
  /-- The canonical value of a field word. -/
  | value (dest source : ℕ)
  /-- The field word of a `u64` value, reduced modulo `p`. -/
  | ofU64 (dest source : ℕ)
  /-- The field word of a `u64` value below `p`. -/
  | ofSmall (dest source : ℕ)
  /-- The field word of the inverse, `0` for `0`. -/
  | inverse (dest source : ℕ)
  /-- `words[index]`, or `0` out of range. -/
  | table (dest index : ℕ) (words : Array UInt64)
  /-- The register `sources[index]`, or `0` out of range. -/
  | pick (dest index : ℕ) (sources : Array ℕ)
  | previous (dest previousColumn : ℕ)
  | current (dest column : ℕ)
  /-- Column `column` of row `row` (a register) of hint table `table` of rows of `width` words, or
  `0` out of range. -/
  | hint (dest table width row column : ℕ)
  | store (column source : ℕ)
  /-- Store the bits `shift, …, shift + count - 1` of `source` as the words of `0` and `1` in the
  columns `column, …, column + count - 1`. -/
  | storeBits (column source shift count : ℕ)
  /-- Copy the previous row's columns `previousColumn, …` to `column, …`. -/
  | copy (column previousColumn count : ℕ)
  /-- For `k < count`: `index := k`, run `body`, store `result` in column `column + k`. -/
  | loop (count index result column : ℕ) (body : Array Instr)
deriving Inhabited

/-- Where a program's cell reads go. -/
inductive CellRead where
  | previous (column : ℕ)
  | current (column : ℕ)
  | zero

/-- What a program reads, besides its registers: its cells, and the hint tables that the generation
provides, by key and width, in order. -/
structure Scope where
  cell : ℕ → Except String CellRead
  hints : Array (String × ℕ)

structure CompileState where
  registers : ℕ := 0
  constants : Std.HashMap UInt64 ℕ := {}
  code : Array Instr := #[]
  /-- The registers of the steps so far, and whether each holds a field element. -/
  locals : Array (Bool × ℕ) := #[]
  /-- The register of `.idx`. -/
  index : ℕ := 0

abbrev CompileM := ReaderT Scope (StateT CompileState (Except String))

instance {α : Type} [Inhabited α] : Inhabited (CompileM α) := ⟨pure default⟩

def fresh : CompileM ℕ := modifyGet fun s => (s.registers, { s with registers := s.registers + 1 })

/-- Append an instruction, merging bit stores of one register and copies that continue the last
instruction. -/
def emit (instr : Instr) : CompileM Unit := modify fun s =>
  let merged : Option Instr := match s.code.back?, instr with
    | some (.storeBits column source shift count), .storeBits column' source' shift' 1 =>
        if source' = source ∧ column' = column + count ∧ shift' = shift + count ∧ shift' < 64 then
          some (.storeBits column source shift (count + 1))
        else none
    | some (.copy column previousColumn count), .copy column' previousColumn' 1 =>
        if column' = column + count ∧ previousColumn' = previousColumn + count then
          some (.copy column previousColumn (count + 1))
        else none
    | _, _ => none
  match merged with
  | some instr => { s with code := s.code.pop.push instr }
  | none => { s with code := s.code.push instr }

/-- The register holding a constant word. -/
def constant (word : UInt64) : CompileM ℕ := do
  if let some register := (← get).constants[word]? then return register
  let register ← fresh
  modify fun s => { s with constants := s.constants.insert word register }
  return register

def compute (instr : ℕ → Instr) : CompileM ℕ := do
  let dest ← fresh
  emit (instr dest)
  return dest

variable {p : ℕ} [Mont32Field p]

/-- The Montgomery word of a field element. -/
def word (x : F p) : UInt64 := (FastField.ofField x).val.toUInt64

def cellRead (cell : ℕ) : CompileM CellRead := do
  match (← read).cell cell with
  | .ok read => return read
  | .error message => throw message

def readCell (cell : ℕ) : CompileM ℕ := do
  match ← cellRead cell with
  | .previous column => compute (.previous · column)
  | .current column => compute (.current · column)
  | .zero => constant 0

def expression : Expression (F p) → CompileM ℕ
  | .var v => readCell v.index
  | .const c => constant (word c)
  | .add left right => do
      compute (.binary .fieldAdd · (← expression left) (← expression right))
  | .mul left right => do
      compute (.binary .fieldMul · (← expression left) (← expression right))

/-- An upper bound of a `u64` expression's value, where an easy one is known. -/
def bound : U64Expr (F p) → Option ℕ
  | .const n => some n.toNat
  | .val _ => some (p - 1)
  | .land left right => match bound left, bound right with
    | some a, some b => some (min a b)
    | some a, none | none, some a => some a
    | none, none => none
  | .mod _ (.const m) => if m = 0 then none else some (m.toNat - 1)
  | .shiftR value (.const s) => (bound value).map (· >>> (s.toNat % 64))
  | _ => none

/-- `(x >>> s) &&& 1` and its variants as the value `x` and the shift `s`. -/
def bitOf? : U64Expr (F p) → Option (U64Expr (F p) × ℕ)
  | .land (.shiftR value (.const s)) (.const 1) | .mod (.shiftR value (.const s)) (.const 2) =>
      some (value, s.toNat % 64)
  | .land value (.const 1) | .mod value (.const 2) => some (value, 0)
  | _ => none

def localRegister (i : ℕ) (field : Bool) : CompileM ℕ := do
  match (← get).locals[i]? with
  | some (isField, register) => if isField == field then return register else constant 0
  | none => constant 0

mutual

partial def fexpr : FExpr (F p) → CompileM ℕ
  | .expr e => expression e
  | .const c => constant (word c)
  | .localVar i => localRegister i true
  | .add left right => do compute (.binary .fieldAdd · (← fexpr left) (← fexpr right))
  | .mul left right => do compute (.binary .fieldMul · (← fexpr left) (← fexpr right))
  | .inv value => do compute (.inverse · (← fexpr value))
  | .ofU64 value => do
      let source ← uexpr value
      if (bound value).any (· < p) then compute (.ofSmall · source)
      else compute (.ofU64 · source)
  | .ite condition yes no => do
      compute (.select · (← bexpr condition) (← fexpr yes) (← fexpr no))
  | .listGet values index => do
      let index ← uexpr index
      let constants := values.filterMap fun | .const c => some (word c) | _ => none
      if constants.length = values.length then compute (.table · index constants.toArray)
      else
        let sources ← values.toArray.mapM fexpr
        compute (.pick · index sources)
  | .dataGet key .. => throw s!"fast witness generation reads no prover data, but a program \
      reads '{key}'"
  | .hintGet key width row column => do
      match (← read).hints.findIdx? (· == (key, width)) with
      | none => constant 0
      | some table => do compute (.hint · table width (← uexpr row) column.val)

partial def uexpr : U64Expr (F p) → CompileM ℕ
  | .const n => constant n
  | .val value => do compute (.value · (← fexpr value))
  | .idx => return (← get).index
  | .localVar i => localRegister i false
  | .add left right => binary .add left right
  | .mul left right => binary .mul left right
  | .div left right => binary .div left right
  | .mod left right => binary .mod left right
  | .land left right => binary .and left right
  | .lor left right => binary .or left right
  | .lxor left right => binary .xor left right
  | .shiftL left right => binary .shiftLeft left right
  | .shiftR left right => binary .shiftRight left right
  | .ite condition yes no => do
      compute (.select · (← bexpr condition) (← uexpr yes) (← uexpr no))
where
  binary (op : BinaryOp) (left right : U64Expr (F p)) : CompileM ℕ := do
    compute (.binary op · (← uexpr left) (← uexpr right))

partial def bexpr : BExpr (F p) → CompileM ℕ
  | .true => constant 1
  | .false => constant 0
  | .feq left right => do compute (.binary .eq · (← fexpr left) (← fexpr right))
  | .neq left right => do compute (.binary .eq · (← uexpr left) (← uexpr right))
  | .lt left right => do compute (.binary .lt · (← uexpr left) (← uexpr right))
  | .flt left right => do
      let left ← compute (.value · (← fexpr left))
      let right ← compute (.value · (← fexpr right))
      compute (.binary .lt · left right)
  | .bit value i =>
      if i < 64 then do
        let value ← compute (.value · (← fexpr value))
        let shifted ← compute (.binary .shiftRight · value (← constant i.toUInt64))
        compute (.binary .and · shifted (← constant 1))
      else constant 0
  | .not condition => do compute (.binary .xor · (← bexpr condition) (← constant 1))
  | .and left right => do compute (.binary .and · (← bexpr left) (← bexpr right))

end

/-- Store the value of an output expression in a column. -/
def cell (column : ℕ) (e : FExpr (F p)) : CompileM Unit := do
  match e with
  | .ofU64 value =>
      if let some (value, shift) := bitOf? value then
        emit (.storeBits column (← uexpr value) shift 1)
      else emit (.store column (← fexpr e))
  | .expr (.var v) =>
      match ← cellRead v.index with
      | .previous previousColumn => emit (.copy column previousColumn 1)
      | _ => emit (.store column (← fexpr e))
  | _ => emit (.store column (← fexpr e))

/-- Store an output vector from a column on. -/
def vexpr (column : ℕ) : {n : ℕ} → VExpr (F p) n → CompileM Unit
  | _, .lit values => do
      for (value, k) in values.toList.zipIdx do cell (column + k) value
  | n, .mapRange _ body => do
      let s ← get
      let index ← fresh
      modify fun s => { s with code := #[], index }
      let result ← fexpr body
      let body := (← get).code
      modify fun t => { t with code := s.code, index := s.index }
      emit (.loop n index result column body)
  | n, .envRange offset => do
      for k in [0:n] do cell (column + k) (.expr (.var ⟨offset + k⟩) : FExpr (F p))
  | n, .bitsOf value => do
      let value ← compute (.value · (← fexpr value))
      for k in [0:n] do
        if k < 64 then emit (.storeBits (column + k) value k 1)
        else emit (.store (column + k) (← constant 0))
  | _, .append (m := m) left right => do
      vexpr column left
      vexpr (column + m) right

/-- Compile the steps of a program, then its output from a column on. -/
def program {n : ℕ} (steps : List (Step (F p))) (out : VExpr (F p) n) (column : ℕ) :
    CompileM Unit := do
  modify fun s => { s with locals := #[] }
  for step in steps do
    let local_ : Bool × ℕ ← match step with
      | .letF e => do pure (true, ← fexpr e)
      | .letU e => do pure (false, ← uexpr e)
    modify fun s => { s with locals := s.locals.push local_ }
  vexpr column out

/-- A compiled row program of a component: the registers it uses, the constants to set before it
runs, the register of the row index, and the code of the rows that start a segment and of the
others. Rows have `width` words. -/
structure Kernel where
  registers : ℕ
  constants : Array (ℕ × UInt64)
  index : ℕ
  first : Array Instr
  next : Array Instr
  width : ℕ
  /-- The length of a segment. -/
  length : ℕ

/-- Run a compilation with a scope and a state, returning the code it emitted. -/
def compileCode (scope : Scope) (s : CompileState) (m : CompileM Unit) :
    Except String (Array Instr × CompileState) := do
  let ((), s) ← (m.run scope).run { s with code := #[] }
  return (s.code, s)

/-- The witness operations of a component, with the first cell of each. -/
def witnessOperations (component : Component (F p)) :
    List ((m : ℕ) × WitgenIR (F p) m × ℕ) :=
  let step (state : List ((m : ℕ) × WitgenIR (F p) m × ℕ) × ℕ) :
      FlatOperation (F p) → List ((m : ℕ) × WitgenIR (F p) m × ℕ) × ℕ
    | .witness m code => (state.1 ++ [⟨m, code, state.2⟩], state.2 + m)
    | _ => state
  (component.rowOperations.toFlat.foldl step ([], size component.Input)).1

/-- Compile the generation of a segment-generated component, whose segment program computes the
row's own input, and its witness programs, to a kernel writing the rows of its trace: each row's
cells but the window cells, as CompStark's backend commits them. Hint tables are named by key and
width, in the order of the hint words that the kernel will read. -/
def compileSegments (component : Component (F p)) (hints : Array (String × ℕ)) :
    Except String Kernel := do
  let .segments { program := segments, .. } := component.generation
    | throw s!"component '{component.circuit.name}' is not generated by a segment program"
  let ownWidth := component.ownInputWidth
  unless segments.width = ownWidth do
    throw s!"segment program of component '{component.circuit.name}' has the wrong width"
  let windowEnd := size component.Input
  let s : CompileState := {}
  let (index, s) ← (fresh.run { cell _ := pure .zero, hints }).run s
  let s := { s with index }
  -- the witness programs read the row's cells computed before them
  let witnesses (s : CompileState) : Except String (Array Instr × CompileState) := do
    let mut s := s
    let mut code := #[]
    for ⟨_, witness, start⟩ in witnessOperations component do
      let .ir steps out := witness
        | throw s!"component '{component.circuit.name}' has a native witness program"
      let cell (j : ℕ) : Except String CellRead :=
        if j < ownWidth then pure (.current j)
        else if j < windowEnd ∨ start ≤ j then pure .zero
        else pure (.current (j - (windowEnd - ownWidth)))
      -- `.idx` is `0` in a witness program
      let (zeroRegister, s') ← ((constant 0).run { cell, hints }).run s
      let (more, s') ← compileCode { cell, hints } { s' with index := zeroRegister }
        (program steps out (start - (windowEnd - ownWidth)))
      s := { s' with index := s.index }
      code := code ++ more
    return (code, s)
  let (firstOut, firstSteps) := segments.firstProgram #[]
  let (first, s) ← compileCode { cell _ := pure .zero, hints } s
    (program firstSteps.toList (.lit (toElements firstOut)) 0)
  let (firstWitnesses, s) ← witnesses s
  let (nextOut, nextSteps) := segments.nextProgram #[]
  let previousCell (j : ℕ) : Except String CellRead :=
    pure (if j < segments.width then .previous j else .zero)
  let (next, s) ← compileCode { cell := previousCell, hints } s
    (program nextSteps.toList (.lit (toElements nextOut)) 0)
  let (nextWitnesses, s) ← witnesses s
  return {
    registers := s.registers
    constants := s.constants.toArray.map fun (word, register) => (register, word)
    index
    first := first ++ firstWitnesses
    next := next ++ nextWitnesses
    width := component.width - (windowEnd - ownWidth)
    length := segments.length
  }

end Air.Flat.FastWitness
