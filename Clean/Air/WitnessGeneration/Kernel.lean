module

public import Clean.Air.FlatComponent

@[expose] public section

/-!
# Compiling generation to register programs

Generation over a field `K` with word conversions (`WordField`) evaluates the witness IR of a
segment-generated component through register programs compiled from it, rather than by walking the
IR's trees: `Clean.Air.WitnessGeneration.Packed` runs them, writing each row's cells into a buffer
in the layout of `CompPoly.PackedRepr K`, and `Clean.Air.WitnessGeneration.Codegen` compiles them
to native code. The component's IR is over a field `F`; its constants are mapped to `K` along a
ring homomorphism `F →+* K`.

A program has two register files: field registers, holding elements of `K`, and word registers,
holding `u64` values and conditions (`0` or `1`). Constants live in registers set once. Every IR
step gets a register; output cells are stores into the row.

The compiler recognizes the cells that a row stores most: the bit `(x >>> s) &&& 1` of a `u64` value
is a store of `0` or `1`, and runs of such bits of one value are one instruction; a value below the
field size enters the field without a reduction (`WordField.ofSmallWord`); and runs of cells copied
from the previous row are one copy.
-/

namespace Air.Flat.WitnessGeneration
open Witgen

/-- Binary operations on words, as Lean's `UInt64` ones (`x / 0 = 0`, `x % 0 = x`, shifts by the
amount modulo 64), and comparisons valued `0` or `1`. -/
inductive WordOp where
  | add | mul | div | mod | and | or | xor | shiftLeft | shiftRight
  | eq | lt
deriving Repr, BEq, Inhabited

/-- Binary operations on field elements. -/
inductive FieldOp where
  | add | mul
deriving Repr, BEq, Inhabited

/-- An instruction of a register program over `K`. `dest`, `source` and the like are registers, of
the file that the instruction reads or writes; `column` is a cell of the current row,
`previousColumn` one of the previous row. -/
inductive Instr (K : Type) where
  | word (op : WordOp) (dest left right : ℕ)
  | field (op : FieldOp) (dest left right : ℕ)
  /-- The word `1` if the field registers `left` and `right` are equal, else `0`. -/
  | fieldEq (dest left right : ℕ)
  /-- `dest := if condition ≠ 0 then yes else no`, on words. -/
  | selectWord (dest condition yes no : ℕ)
  /-- `dest := if condition ≠ 0 then yes else no`, on field elements, with a word condition. -/
  | selectField (dest condition yes no : ℕ)
  /-- The value of a field element, as a word. -/
  | value (dest source : ℕ)
  /-- The field element of a word's value. -/
  | ofWord (dest source : ℕ)
  /-- The field element of a word's value below the field size. -/
  | ofSmallWord (dest source : ℕ)
  /-- The inverse, `0` for `0`. -/
  | inverse (dest source : ℕ)
  /-- `values[index]`, or `0` out of range, with a word `index`. -/
  | table (dest index : ℕ) (values : Array K)
  /-- The field register `sources[index]`, or `0` out of range, with a word `index`. -/
  | pick (dest index : ℕ) (sources : Array ℕ)
  | previous (dest previousColumn : ℕ)
  | current (dest column : ℕ)
  /-- Column `column` of row `row` (a word register) of hint table `table` of rows of `width`
  elements, or `0` out of range. -/
  | hint (dest table width row column : ℕ)
  | store (column source : ℕ)
  /-- Store the bits `shift, …, shift + count - 1` of the word `source` as the elements `0` and `1`
  in the columns `column, …, column + count - 1`. -/
  | storeBits (column source shift count : ℕ)
  /-- Copy the previous row's columns `previousColumn, …` to `column, …`. -/
  | copy (column previousColumn count : ℕ)
  /-- For `k < count`: word `index := k`, run `body`, store field `result` in column
  `column + k`. -/
  | loop (count index result column : ℕ) (body : Array (Instr K))
deriving Inhabited

/-- An instruction with its constant elements mapped. -/
partial def Instr.map {K L : Type} (f : K → L) : Instr K → Instr L
  | .word op dest left right => .word op dest left right
  | .field op dest left right => .field op dest left right
  | .fieldEq dest left right => .fieldEq dest left right
  | .selectWord dest condition yes no => .selectWord dest condition yes no
  | .selectField dest condition yes no => .selectField dest condition yes no
  | .value dest source => .value dest source
  | .ofWord dest source => .ofWord dest source
  | .ofSmallWord dest source => .ofSmallWord dest source
  | .inverse dest source => .inverse dest source
  | .table dest index values => .table dest index (values.map f)
  | .pick dest index sources => .pick dest index sources
  | .previous dest previousColumn => .previous dest previousColumn
  | .current dest column => .current dest column
  | .hint dest t width row column => .hint dest t width row column
  | .store column source => .store column source
  | .storeBits column source shift count => .storeBits column source shift count
  | .copy column previousColumn count => .copy column previousColumn count
  | .loop count index result column body => .loop count index result column (body.map (map f))

/-- Where a program's cell reads go. -/
inductive CellRead where
  | previous (column : ℕ)
  | current (column : ℕ)
  | zero

/-- What a program reads, besides its registers: its cells, and the hint tables that the generation
provides, by key and width, in order; and how its constants map to `K`. -/
structure Scope (F K : Type) where
  cell : ℕ → Except String CellRead
  hints : Array (String × ℕ)
  constant : F → K

structure CompileState (K : Type) where
  fieldRegisters : ℕ := 0
  wordRegisters : ℕ := 0
  /-- The register of each field constant, by its value. -/
  fieldConstants : Std.HashMap ℕ (ℕ × K) := {}
  wordConstants : Std.HashMap UInt64 ℕ := {}
  code : Array (Instr K) := #[]
  /-- The registers of the steps so far, and whether each is a field register. -/
  locals : Array (Bool × ℕ) := #[]
  /-- The word register of `.idx`. -/
  index : ℕ := 0

abbrev CompileM (F K : Type) := ReaderT (Scope F K) (StateT (CompileState K) (Except String))

instance {F K α : Type} [Inhabited α] : Inhabited (CompileM F K α) := ⟨pure default⟩

variable {F K : Type} [FiniteField F] [FiniteField K]

def freshField : CompileM F K ℕ :=
  modifyGet fun s => (s.fieldRegisters, { s with fieldRegisters := s.fieldRegisters + 1 })

def freshWord : CompileM F K ℕ :=
  modifyGet fun s => (s.wordRegisters, { s with wordRegisters := s.wordRegisters + 1 })

/-- Append an instruction, merging bit stores of one register and copies that continue the last
instruction. -/
def emit (instr : Instr K) : CompileM F K Unit := modify fun s =>
  let merged : Option (Instr K) := match s.code.back?, instr with
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

/-- The field register holding a constant. -/
def fieldConstant (x : K) : CompileM F K ℕ := do
  let key := FiniteField.val x
  if let some (register, _) := (← get).fieldConstants[key]? then return register
  let register ← freshField
  modify fun s => { s with fieldConstants := s.fieldConstants.insert key (register, x) }
  return register

/-- The word register holding a constant. -/
def wordConstant (word : UInt64) : CompileM F K ℕ := do
  if let some register := (← get).wordConstants[word]? then return register
  let register ← freshWord
  modify fun s => { s with wordConstants := s.wordConstants.insert word register }
  return register

def computeField (instr : ℕ → Instr K) : CompileM F K ℕ := do
  let dest ← freshField
  emit (instr dest)
  return dest

def computeWord (instr : ℕ → Instr K) : CompileM F K ℕ := do
  let dest ← freshWord
  emit (instr dest)
  return dest

/-- The register holding a constant of the IR's field. -/
def irConstant (c : F) : CompileM F K ℕ := do fieldConstant ((← read).constant c)

def cellRead (cell : ℕ) : CompileM F K CellRead := do
  match (← read).cell cell with
  | .ok read => return read
  | .error message => throw message

def readCell (cell : ℕ) : CompileM F K ℕ := do
  match ← cellRead cell with
  | .previous column => computeField (.previous · column)
  | .current column => computeField (.current · column)
  | .zero => fieldConstant 0

def expression : Expression F → CompileM F K ℕ
  | .var v => readCell v.index
  | .const c => irConstant c
  | .add left right => do
      computeField (.field .add · (← expression left) (← expression right))
  | .mul left right => do
      computeField (.field .mul · (← expression left) (← expression right))

/-- An upper bound of a `u64` expression's value over `K`, where an easy one is known. -/
def bound : U64Expr F → Option ℕ
  | .const n => some n.toNat
  | .val _ => some (FiniteField.size K - 1)
  | .land left right => match bound left, bound right with
    | some a, some b => some (min a b)
    | some a, none | none, some a => some a
    | none, none => none
  | .mod _ (.const m) => if m = 0 then none else some (m.toNat - 1)
  | .shiftR value (.const s) => (bound value).map (· >>> (s.toNat % 64))
  | _ => none

/-- `(x >>> s) &&& 1` and its variants as the value `x` and the shift `s`. -/
def bitOf? : U64Expr F → Option (U64Expr F × ℕ)
  | .land (.shiftR value (.const s)) (.const 1) | .mod (.shiftR value (.const s)) (.const 2) =>
      some (value, s.toNat % 64)
  | .land value (.const 1) | .mod value (.const 2) => some (value, 0)
  | _ => none

def localRegister (i : ℕ) (field : Bool) : CompileM F K ℕ := do
  match (← get).locals[i]? with
  | some (isField, register) => if isField == field then return register
  | none => pure ()
  if field then fieldConstant 0 else wordConstant 0

mutual

partial def fexpr : FExpr F → CompileM F K ℕ
  | .expr e => expression e
  | .const c => irConstant c
  | .localVar i => localRegister i true
  | .add left right => do computeField (.field .add · (← fexpr left) (← fexpr right))
  | .mul left right => do computeField (.field .mul · (← fexpr left) (← fexpr right))
  | .inv value => do computeField (.inverse · (← fexpr value))
  | .ofU64 value => do
      let source ← uexpr value
      if ((bound (K := K) value).any (· < FiniteField.size K)) then
        computeField (.ofSmallWord · source)
      else computeField (.ofWord · source)
  | .ite condition yes no => do
      computeField (.selectField · (← bexpr condition) (← fexpr yes) (← fexpr no))
  | .listGet values index => do
      let index ← uexpr index
      let constants := values.filterMap fun | .const c => some c | _ => none
      if constants.length = values.length then
        let map := (← read).constant
        computeField (.table · index (constants.toArray.map map))
      else
        let sources ← values.toArray.mapM fexpr
        computeField (.pick · index sources)
  | .dataGet key .. => throw s!"compiled witness generation reads no prover data, but a program \
      reads '{key}'"
  | .hintGet key width row column => do
      match (← read).hints.findIdx? (· == (key, width)) with
      | none => fieldConstant 0
      | some table => do computeField (.hint · table width (← uexpr row) column.val)

partial def uexpr : U64Expr F → CompileM F K ℕ
  | .const n => wordConstant n
  | .val value => do computeWord (.value · (← fexpr value))
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
      computeWord (.selectWord · (← bexpr condition) (← uexpr yes) (← uexpr no))
where
  binary (op : WordOp) (left right : U64Expr F) : CompileM F K ℕ := do
    computeWord (.word op · (← uexpr left) (← uexpr right))

partial def bexpr : BExpr F → CompileM F K ℕ
  | .true => wordConstant 1
  | .false => wordConstant 0
  | .feq left right => do computeWord (.fieldEq · (← fexpr left) (← fexpr right))
  | .neq left right => do computeWord (.word .eq · (← uexpr left) (← uexpr right))
  | .lt left right => do computeWord (.word .lt · (← uexpr left) (← uexpr right))
  | .flt left right => do
      let left ← computeWord (.value · (← fexpr left))
      let right ← computeWord (.value · (← fexpr right))
      computeWord (.word .lt · left right)
  | .bit value i =>
      if i < 64 then do
        let value ← computeWord (.value · (← fexpr value))
        let shifted ← computeWord (.word .shiftRight · value (← wordConstant i.toUInt64))
        computeWord (.word .and · shifted (← wordConstant 1))
      else wordConstant 0
  | .not condition => do computeWord (.word .xor · (← bexpr condition) (← wordConstant 1))
  | .and left right => do computeWord (.word .and · (← bexpr left) (← bexpr right))

end

/-- Store the value of an output expression in a column. -/
def cell (column : ℕ) (e : FExpr F) : CompileM F K Unit := do
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
def vexpr (column : ℕ) : {n : ℕ} → VExpr F n → CompileM F K Unit
  | _, .lit values => do
      for (value, k) in values.toList.zipIdx do cell (column + k) value
  | n, .mapRange _ body => do
      let s ← get
      let index ← freshWord
      modify fun s => { s with code := #[], index }
      let result ← fexpr body
      let body := (← get).code
      modify fun t => { t with code := s.code, index := s.index }
      emit (.loop n index result column body)
  | n, .envRange offset => do
      for k in [0:n] do cell (column + k) (.expr (.var ⟨offset + k⟩) : FExpr F)
  | n, .bitsOf value => do
      let value ← computeWord (.value · (← fexpr value))
      for k in [0:n] do
        if k < 64 then emit (.storeBits (column + k) value k 1)
        else emit (.store (column + k) (← fieldConstant 0))
  | _, .append (m := m) left right => do
      vexpr column left
      vexpr (column + m) right

/-- Compile the steps of a program, then its output from a column on. -/
def program {n : ℕ} (steps : List (Step F)) (out : VExpr F n) (column : ℕ) :
    CompileM F K Unit := do
  modify fun s => { s with locals := #[] }
  for step in steps do
    let local_ : Bool × ℕ ← match step with
      | .letF e => do pure (true, ← fexpr e)
      | .letU e => do pure (false, ← uexpr e)
    modify fun s => { s with locals := s.locals.push local_ }
  vexpr column out

/-- A compiled row program of a component over `K`: the registers it uses, the constants to set
before it runs, the word register of the row index, and the code of the rows that start a segment
and of the others. Rows have `width` elements. -/
structure Kernel (K : Type) where
  fieldRegisters : ℕ
  wordRegisters : ℕ
  fieldConstants : Array (ℕ × K)
  wordConstants : Array (ℕ × UInt64)
  index : ℕ
  first : Array (Instr K)
  next : Array (Instr K)
  width : ℕ
  /-- The length of a segment. -/
  length : ℕ
deriving Inhabited

/-- A kernel with its constant elements mapped. -/
def Kernel.map {K L : Type} (f : K → L) (kernel : Kernel K) : Kernel L :=
  { kernel with
    fieldConstants := kernel.fieldConstants.map fun (register, x) => (register, f x)
    first := kernel.first.map (·.map f)
    next := kernel.next.map (·.map f) }

/-- Run a compilation with a scope and a state, returning the code it emitted. -/
def compileCode (scope : Scope F K) (s : CompileState K) (m : CompileM F K Unit) :
    Except String (Array (Instr K) × CompileState K) := do
  let ((), s) ← (m.run scope).run { s with code := #[] }
  return (s.code, s)

/-- The witness operations of a component, with the first cell of each. -/
def witnessOperations (component : Component F) :
    List ((m : ℕ) × WitgenIR F m × ℕ) :=
  let step (state : List ((m : ℕ) × WitgenIR F m × ℕ) × ℕ) :
      FlatOperation F → List ((m : ℕ) × WitgenIR F m × ℕ) × ℕ
    | .witness m code => (state.1 ++ [⟨m, code, state.2⟩], state.2 + m)
    | _ => state
  (component.rowOperations.toFlat.foldl step ([], size component.Input)).1

/-- Compile the generation of a segment-generated component over `F`, whose segment program
computes the row's own input, and its witness programs, to a kernel over `K` writing the rows of
its trace: each row's cells but the window cells, which a backend doesn't commit. The constants
map along `f`. Hint tables are named by key and width, in the order of the hint buffers that the
kernel will read. -/
def compileSegments (component : Component F) (f : F →+* K) (hints : Array (String × ℕ)) :
    Except String (Kernel K) := do
  let .segments { program := segments, .. } := component.generation
    | throw s!"component '{component.circuit.name}' is not generated by a segment program"
  let ownWidth := component.ownInputWidth
  unless segments.width = ownWidth do
    throw s!"segment program of component '{component.circuit.name}' has the wrong width"
  let windowEnd := size component.Input
  let scope (cell : ℕ → Except String CellRead) : Scope F K := { cell, hints, constant := f }
  let s : CompileState K := {}
  let (index, s) ← (freshWord.run (scope fun _ => pure .zero)).run s
  let s := { s with index }
  -- the witness programs read the row's cells computed before them
  let witnesses (s : CompileState K) : Except String (Array (Instr K) × CompileState K) := do
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
      let (zeroRegister, s') ← ((wordConstant 0).run (scope cell)).run s
      let (more, s') ← compileCode (scope cell) { s' with index := zeroRegister }
        (program steps out (start - (windowEnd - ownWidth)))
      s := { s' with index := s.index }
      code := code ++ more
    return (code, s)
  let (firstOut, firstSteps) := segments.firstProgram #[]
  let (first, s) ← compileCode (scope fun _ => pure .zero) s
    (program firstSteps.toList (.lit (toElements firstOut)) 0)
  let (firstWitnesses, s) ← witnesses s
  let (nextOut, nextSteps) := segments.nextProgram #[]
  let previousCell (j : ℕ) : Except String CellRead :=
    pure (if j < segments.width then .previous j else .zero)
  let (next, s) ← compileCode (scope previousCell) s
    (program nextSteps.toList (.lit (toElements nextOut)) 0)
  let (nextWitnesses, s) ← witnesses s
  return {
    fieldRegisters := s.fieldRegisters
    wordRegisters := s.wordRegisters
    fieldConstants := s.fieldConstants.toArray.map (·.2)
    wordConstants := s.wordConstants.toArray.map fun (word, register) => (register, word)
    index
    first := first ++ firstWitnesses
    next := next ++ nextWitnesses
    width := component.width - (windowEnd - ownWidth)
    length := segments.length
  }

end Air.Flat.WitnessGeneration
