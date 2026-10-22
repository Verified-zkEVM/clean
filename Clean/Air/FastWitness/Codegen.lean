module

public import Clean.Air.FastWitness.Run
public meta import Clean.Air.FastWitness.Run
public meta import Lean.Elab.Command

@[expose] public section

/-!
# Compiling kernels to native code

`fast_witness_kernel name for p := kernel` compiles a kernel (`Clean.Air.FastWitness.Compile`) for
the 32-bit Montgomery field of `p` to native code: it evaluates `kernel : Except String Kernel`,
translates the code of the rows that start a segment and of the others to straight-line Lean
functions, one `let` per instruction on unboxed words, and adds them with `addAndCompile`, as
`name.first` and `name.next`, and `name : CompiledKernel`.

The functions do what the interpreter does (`Clean.Air.FastWitness.Run`): registers become local
words, constants literals, loops are unrolled, and the word operations are the same branch-free
functions, so that Lean's compiler keeps the code straight. Stores to consecutive columns are
batched into one store of up to 16 words with one range check (`storeSixteen`, `storeFew`).
-/

namespace Air.Flat.FastWitness.Codegen
open Lean Meta Elab Command

meta section

/-- A `let`-chain under construction: the bindings so far, each a name, a type and a value whose
references to earlier bindings `j` are `.bvar j`. -/
structure Chain where
  bindings : Array (Name × Expr × Expr) := #[]
  /-- The binding or expression of every register. -/
  registers : Std.HashMap ℕ Expr := {}
  /-- The current rows buffer, of type `Rows n`. -/
  rows : Expr

/-- The parameters, proofs and constants that the generated code refers to: the rows are a
`Rows n` with room for the row's `width` words from the byte offsets `current` and `previous`. -/
structure Target where
  hints : Expr
  rowsType : Expr
  n : Expr
  width : ℕ
  current : Expr
  currentRoom : Expr
  previous : Expr
  previousRoom : Expr
  row : Expr
  p64 : UInt64
  negInv : UInt64
  r2 : UInt64
  one : UInt32
  inverse : Expr

abbrev GenM := StateT Chain MetaM

def bind (name : Name) (type value : Expr) : GenM Expr := do
  let s ← get
  set { s with bindings := s.bindings.push (name, type, value) }
  return .bvar s.bindings.size

def u64 (v : UInt64) : Expr := toExpr v

def u64Type : Expr := mkConst ``UInt64

def register (r : ℕ) : GenM Expr := do
  match (← get).registers[r]? with
  | some e => return e
  | none => throwError "fast_witness_kernel: register {r} is read before it is written"

def setRegister (r : ℕ) (value : Expr) : GenM Unit := do
  let e ← bind (.mkSimple s!"r{r}") u64Type value
  modify fun s => { s with registers := s.registers.insert r e }

def reduceExpr (t : Target) (x : Expr) : Expr :=
  mkApp3 (mkConst ``reduceWord) (u64 t.p64) (u64 t.negInv) x

def binaryExpr (t : Target) (op : BinaryOp) (a b : Expr) : Expr :=
  match op with
  | .add => mkApp2 (mkConst ``UInt64.add) a b
  | .mul => mkApp2 (mkConst ``UInt64.mul) a b
  | .div => mkApp2 (mkConst ``UInt64.div) a b
  | .mod => mkApp2 (mkConst ``UInt64.mod) a b
  | .and => mkApp2 (mkConst ``UInt64.land) a b
  | .or => mkApp2 (mkConst ``UInt64.lor) a b
  | .xor => mkApp2 (mkConst ``UInt64.xor) a b
  | .shiftLeft => mkApp2 (mkConst ``UInt64.shiftLeft) a b
  | .shiftRight => mkApp2 (mkConst ``UInt64.shiftRight) a b
  | .eq => mkApp2 (mkConst ``eqWord) a b
  | .lt => mkApp2 (mkConst ``ltWord) a b
  | .fieldAdd => mkApp3 (mkConst ``addWord) (u64 t.p64) a b
  | .fieldMul => reduceExpr t (mkApp2 (mkConst ``UInt64.mul) a b)

/-- A proof of `k < width`, by `decide`. -/
def columnProof (t : Target) (k : ℕ) : GenM Expr := do
  unless k < t.width do throwError "fast_witness_kernel: column {k} is outside the row"
  let k := mkNatLit k
  let width := mkNatLit t.width
  let lt := mkApp4 (mkConst ``LT.lt [0]) (mkConst ``Nat) (mkConst ``instLTNat) k width
  return mkApp3 (mkConst ``of_decide_eq_true) lt (mkApp2 (mkConst ``Nat.decLt) k width)
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- Store a word in a column of the row. -/
def store (t : Target) (column : ℕ) (value : Expr) : GenM Unit := do
  let proof ← columnProof t column
  let rows := mkAppN (mkConst ``storeAt) #[t.n, mkNatLit t.width, (← get).rows, t.current,
    t.currentRoom, mkNatLit column, proof, value]
  let rows ← bind `rows t.rowsType rows
  modify fun s => { s with rows := rows }

/-- Word `column` of the row (`current`) or the previous row. -/
def load (t : Target) (current : Bool) (column : ℕ) : GenM Expr := do
  let (base, room) := if current then (t.current, t.currentRoom) else (t.previous, t.previousRoom)
  return mkAppN (mkConst ``loadAt) #[t.n, mkNatLit t.width, (← get).rows, base, room,
    mkNatLit column, ← columnProof t column]

partial def instr (t : Target) : Instr → GenM Unit
  | .binary op dest left right => do
      setRegister dest (binaryExpr t op (← register left) (← register right))
  | .select dest condition yes no => do
      setRegister dest
        (mkApp3 (mkConst ``selectWord) (← register condition) (← register yes) (← register no))
  | .value dest source => do setRegister dest (reduceExpr t (← register source))
  | .ofU64 dest source => do
      setRegister dest (reduceExpr t (mkApp2 (mkConst ``UInt64.mul)
        (mkApp2 (mkConst ``UInt64.mod) (← register source) (u64 t.p64)) (u64 t.r2)))
  | .ofSmall dest source => do
      setRegister dest (reduceExpr t (mkApp2 (mkConst ``UInt64.mul) (← register source) (u64 t.r2)))
  | .inverse dest source => do setRegister dest (mkApp t.inverse (← register source))
  | .table dest index words => do
      setRegister dest (mkApp2 (mkConst ``tableWord) (toExpr words) (← register index))
  | .pick dest index sources => do
      let sources ← sources.mapM register
      setRegister dest (mkApp2 (mkConst ``tableWord) (← mkArrayLit u64Type sources.toList)
        (← register index))
  | .previous dest column => do
      setRegister dest (mkApp (mkConst ``UInt32.toUInt64) (← load t false column))
  | .current dest column => do
      setRegister dest (mkApp (mkConst ``UInt32.toUInt64) (← load t true column))
  | .hint dest table width row column => do
      setRegister dest (mkApp5 (mkConst ``hintWord) t.hints (mkNatLit table) (mkNatLit width)
        (← register row) (mkNatLit column))
  | .store column source => do
      store t column (mkApp (mkConst ``UInt64.toUInt32) (← register source))
  | .storeBits column source shift count => do
      let value ← register source
      for k in [0:count] do
        store t (column + k)
          (mkApp3 (mkConst ``bitWord) (toExpr t.one) value (u64 (shift + k).toUInt64))
  | .copy column previousColumn count => do
      for k in [0:count] do
        let word ← bind `word (mkConst ``UInt32) (← load t false (previousColumn + k))
        store t (column + k) word
  | .loop count index result column body => do
      for k in [0:count] do
        modify fun s => { s with registers := s.registers.insert index (u64 k.toUInt64) }
        for i in body do instr t i
        store t (column + k) (mkApp (mkConst ``UInt64.toUInt32) (← register result))

/-- The function `rows hints current previous row ↦ rows` running `code`: if the rows have room
for the row and the previous row, the `let`-chain of `code`, else the rows unchanged. -/
def rowFunction (kernel : Kernel) (constants : UInt64 × UInt64 × UInt64 × UInt32)
    (inverse : Expr) (code : Array Instr) : MetaM Expr := do
  let byteArray := mkConst ``ByteArray
  withLocalDeclD `rows byteArray fun rows =>
  withLocalDeclD `hints (mkApp (mkConst ``Array [0]) byteArray) fun hints =>
  withLocalDeclD `current (mkConst ``Nat) fun currentWords =>
  withLocalDeclD `previous (mkConst ``Nat) fun previousWords =>
  withLocalDeclD `row u64Type fun row => do
    let n := mkApp (mkConst ``ByteArray.size) rows
    let width := mkNatLit kernel.width
    let offset (words : Expr) : Expr :=
      mkApp (mkConst ``Nat.toUSize) (mkApp2 (mkConst ``Nat.mul) (mkNatLit 4) words)
    let room (base : Expr) : Expr := mkApp3 (mkConst ``Room) n width base
    let condition := mkApp2 (mkConst ``And) (room (offset currentWords))
      (room (offset previousWords))
    let decidable ← synthInstance (mkApp (mkConst ``Decidable) condition)
    let body ← withLocalDeclD `room condition fun hroom => do
      let (p64, negInv, r2, one) := constants
      let rowsType := mkApp (mkConst ``Rows) n
      let t : Target := ⟨hints, rowsType, n, kernel.width, offset currentWords,
        mkApp3 (mkConst ``And.left) (room (offset currentWords)) (room (offset previousWords))
          hroom,
        offset previousWords,
        mkApp3 (mkConst ``And.right) (room (offset currentWords)) (room (offset previousWords))
          hroom,
        row, p64, negInv, r2, one, inverse⟩
      let initial := mkApp (mkConst ``Rows.of) rows
      let generate : GenM Unit := do
        modify fun s => { s with registers := s.registers.insert kernel.index row }
        for (r, v) in kernel.constants do
          modify fun s => { s with registers := s.registers.insert r (u64 v) }
        for i in code do instr t i
      let ((), chain) ← generate.run { rows := initial }
      -- references to bindings are `.bvar j`; under `k` bindings, binding `j` is
      -- `.bvar (k - 1 - j)`
      let index (k : ℕ) (e : Expr) : Expr := e.replace fun
        | .bvar j => some (.bvar (k - 1 - j))
        | _ => none
      let bindings := chain.bindings.size
      -- the bindings' values have no binders of their own
      let mut body := index bindings (mkApp2 (mkConst ``Rows.buffer) n chain.rows)
      for k' in [0:bindings] do
        let k := bindings - 1 - k'
        let (name, type, value) := chain.bindings[k]!
        body := .letE name type (index k value) body false
      mkLambdaFVars #[hroom] body
    let otherwise ← withLocalDeclD `room (mkNot condition) fun h => mkLambdaFVars #[h] rows
    let result := mkApp5 (mkConst ``dite [1]) byteArray condition decidable body otherwise
    mkLambdaFVars #[rows, hints, currentWords, previousWords, row] result

unsafe def evalKernelUnsafe (e : Expr) : TermElabM (Except String Kernel) :=
  evalExpr (Except String Kernel) (mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String)
    (mkConst ``Kernel)) e

@[implemented_by evalKernelUnsafe]
opaque evalKernel (e : Expr) : TermElabM (Except String Kernel)

unsafe def evalConstantsUnsafe (e : Expr) : TermElabM (UInt64 × UInt64 × UInt64 × UInt32) := do
  evalExpr (UInt64 × UInt64 × UInt64 × UInt32) (← inferType e) e

@[implemented_by evalConstantsUnsafe]
opaque evalConstants (e : Expr) : TermElabM (UInt64 × UInt64 × UInt64 × UInt32)

/-- `fast_witness_kernel name for p := kernel`: compile `kernel : Except String Kernel` for the
Montgomery field of `p` to `name.first`, `name.next` and `name : CompiledKernel`. -/
elab "fast_witness_kernel " name:ident " for " p:term " := " kernel:term : command => do
  let name := name.getId
  let (first, next, width, length) ← liftTermElabM do
    let p ← Term.elabTerm p (mkConst ``Nat)
    let constants ← evalConstants (← mkAppOptM ``fieldConstants #[some p, none])
    let inverse ← mkAppOptM ``inverseWord #[some p, none]
    let kernelType := mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String) (mkConst ``Kernel)
    let e ← Term.elabTerm kernel kernelType
    Term.synthesizeSyntheticMVarsNoPostponing
    let kernel ← match ← evalKernel (← instantiateMVars e) with
      | .ok kernel => pure kernel
      | .error message => throwError "fast_witness_kernel: {message}"
    let first ← rowFunction kernel constants inverse kernel.first
    let next ← rowFunction kernel constants inverse kernel.next
    return (first, next, kernel.width, kernel.length)
  let byteArray := mkConst ``ByteArray
  let type := mkForall `rows .default byteArray <| mkForall `hints .default
    (mkApp (mkConst ``Array [0]) byteArray) <| mkForall `current .default (mkConst ``Nat) <|
    mkForall `previous .default (mkConst ``Nat) <| mkForall `row .default u64Type byteArray
  -- the compiler recurses along the `let`-chain
  for (suffix, value) in [(`first, first), (`next, next)] do
    liftCoreM <| withTheReader Core.Context (fun c =>
      { c with maxRecDepth := 1000000, options := maxRecDepth.set c.options 1000000 }) <|
      addAndCompile <| .defnDecl <|
        mkDefinitionValEx (name ++ suffix) [] type value .opaque .safe []
  liftCoreM <| addAndCompile <| .defnDecl <| mkDefinitionValEx name [] (mkConst ``CompiledKernel)
    (mkApp4 (mkConst ``CompiledKernel.mk) (mkNatLit width) (mkNatLit length)
      (mkConst (name ++ `first)) (mkConst (name ++ `next))) .opaque .safe []

end

end Air.Flat.FastWitness.Codegen
