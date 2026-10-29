module

public import Clean.Air.WitnessGeneration.Packed
public meta import Clean.Air.WitnessGeneration.Packed
public meta import Lean.Elab.Command

@[expose] public section

/-!
# Compiling kernels to native code

`witness_kernel name over K := kernel` compiles a kernel over the field `K`
(`Clean.Air.WitnessGeneration.Kernel`) to native code: it evaluates `kernel : Except String
(Kernel K)`, translates the code of the rows that start a segment and of the others to straight-line
Lean functions, one `let` per instruction, and adds them with `addAndCompile`, as `name.first` and
`name.next`, and `name : CompiledKernel K`.

The functions do what the interpreter does (`Clean.Air.WitnessGeneration.Packed`): registers become
local values of `K` or `UInt64`, constants the elements of their words (`WordField.ofWord`), and
loops are unrolled. The operations are `K`'s own, applied at `K`, so that Lean's compiler inlines
them and keeps the code straight. Each row is checked once to have room in the rows buffer; its
loads and stores carry proofs of their bounds.
-/

namespace Air.Flat.WitnessGeneration.Codegen
open Lean Meta Elab Command

meta section

/-- A `let`-chain under construction: the bindings so far, each a name, a type and a value whose
references to earlier bindings `j` are `.bvar j`. -/
structure Chain where
  bindings : Array (Name × Expr × Expr) := #[]
  /-- The binding or expression of every field register. -/
  fields : Std.HashMap ℕ Expr := {}
  /-- The binding or expression of every word register. -/
  words : Std.HashMap ℕ Expr := {}
  /-- The current rows buffer, of type `Rows n`. -/
  rows : Expr

def u64 (v : UInt64) : Expr := toExpr v

def u64Type : Expr := mkConst ``UInt64

/-- A function of `K`: the constant `name` applied to `K` and the instances it takes, up to its
first other argument. -/
def atField (K : Expr) (name : Name) : MetaM Expr := do
  let mut e ← mkConstWithFreshMVarLevels name
  let mut type ← inferType e
  let mut applied := false
  repeat
    type ← whnf type
    let .forallE _ domain body info := type | break
    if info.isInstImplicit || (info.isImplicit && (← isClass? domain).isSome) then
      let inst ← synthInstance domain
      e := mkApp e inst
      type := body.instantiate1 inst
    else if !applied && (← isDefEq domain (mkSort Level.one)) then
      e := mkApp e K
      type := body.instantiate1 K
      applied := true
    else break
  instantiateMVars e

/-- A function of `K` built from its arguments, as a closed lambda. -/
def lambdaAt (types : Array Expr) (body : Array Expr → MetaM Expr) : MetaM Expr := do
  let rec go (i : ℕ) (xs : Array Expr) : MetaM Expr := do
    if h : i < types.size then
      withLocalDeclD (.mkSimple s!"x{i}") types[i] fun x => go (i + 1) (xs.push x)
    else mkLambdaFVars xs (← body xs)
  go 0 #[]

/-- The operations of `K` that the generated code applies, each a function of `K`. -/
structure Operations where
  add : Expr
  mul : Expr
  inv : Expr
  eqField : Expr
  selectField : Expr
  bitElement : Expr
  toWord : Expr
  ofWord : Expr
  ofSmallWord : Expr
  tableElement : Expr
  hintElement : Expr
  storeAt : Expr
  loadAt : Expr

/-- The operations of `K`, by name, applied at `K`. -/
def Operations.ofField (K : Expr) : MetaM (Array (Name × Expr)) := do
  return #[
    (`add, ← lambdaAt #[K, K] fun xs => mkAppM ``HAdd.hAdd #[xs[0]!, xs[1]!]),
    (`mul, ← lambdaAt #[K, K] fun xs => mkAppM ``HMul.hMul #[xs[0]!, xs[1]!]),
    (`inv, ← lambdaAt #[K] fun xs => mkAppM ``Inv.inv #[xs[0]!]),
    (`eqField, ← atField K ``Air.Flat.WitnessGeneration.eqField),
    (`selectField, ← atField K ``Air.Flat.WitnessGeneration.selectField),
    (`bitElement, ← atField K ``Air.Flat.WitnessGeneration.bitElement),
    (`toWord, ← atField K ``WordField.toWord),
    (`ofWord, ← atField K ``WordField.ofWord),
    (`ofSmallWord, ← atField K ``WordField.ofSmallWord),
    (`tableElement, ← atField K ``Air.Flat.WitnessGeneration.tableElement),
    (`hintElement, ← atField K ``Air.Flat.WitnessGeneration.hintElement),
    (`storeAt, ← atField K ``Air.Flat.WitnessGeneration.storeAt),
    (`loadAt, ← atField K ``Air.Flat.WitnessGeneration.loadAt)]

/-- The operations that branch, which the generated code calls rather than inlines: inlined, their
branches would make the compiler's passes over a kernel's long straight-line code slow. -/
def Operations.called : List Name := [`eqField, `selectField, `hintElement, `loadAt]

/-- Add the operations of `K` as definitions under `pre`, compiled once, so that the compiler
resolves `K`'s instances once rather than at every use. -/
def Operations.define (pre : Name) (K : Expr) : MetaM Operations := do
  let mut constants : Std.HashMap Name Expr := {}
  for (name, value) in ← Operations.ofField K do
    let declName := pre ++ name
    let decl := Declaration.defnDecl <|
      mkDefinitionValEx declName [] (← inferType value) value .abbrev .safe [declName]
    addDecl decl
    let kind := if Operations.called.contains name then .noinline else .inline
    match Compiler.setInlineAttribute (← getEnv) declName kind with
    | .ok env => setEnv env
    | .error message => throwError message
    compileDecl decl
    constants := constants.insert name (mkConst declName)
  let get (name : Name) : Expr := constants.getD name (mkConst name)
  return {
    add := get `add, mul := get `mul, inv := get `inv, eqField := get `eqField
    selectField := get `selectField, bitElement := get `bitElement, toWord := get `toWord
    ofWord := get `ofWord, ofSmallWord := get `ofSmallWord, tableElement := get `tableElement
    hintElement := get `hintElement, storeAt := get `storeAt, loadAt := get `loadAt }

/-- Add a closed value as a constant, which the program computes once, when it initializes the
module, rather than at every row. -/
def defineConstant (declName : Name) (type value : Expr) : MetaM Expr := do
  let decl := Declaration.defnDecl <|
    mkDefinitionValEx declName [] type value .opaque .safe []
  addDecl decl
  match Compiler.setInlineAttribute (← getEnv) declName .noinline with
  | .ok env => setEnv env
  | .error message => throwError message
  compileDecl decl
  return mkConst declName

/-- The constant arrays of `table` instructions, as the words of their elements. -/
partial def Instr.tables : Instr UInt64 → List (Array UInt64)
  | .table _ _ values => [values]
  | .loop _ _ _ _ body => body.toList.flatMap Instr.tables
  | _ => []

/-- The constants that the generated code reads: the elements `0` and `1` as a `Vector K 2`, and
the arrays of `table` instructions, by their words. -/
structure Constants where
  bits : Expr
  tables : Std.HashMap (Array UInt64) Expr

/-- Add the constants of the code of a kernel over `K` under `pre`. -/
def Constants.define (pre : Name) (K : Expr) (operations : Operations)
    (code : Array (Instr UInt64)) : MetaM Constants := do
  let element (word : UInt64) : Expr := mkApp operations.ofWord (u64 word)
  let bits ← defineConstant (pre ++ `bits) (← mkAppM ``Vector #[K, mkNatLit 2])
    (← mkAppM ``Vector.mk #[← mkArrayLit K [element 0, element 1], ← mkEqRefl (mkNatLit 2)])
  let mut tables : Std.HashMap (Array UInt64) Expr := {}
  for values in code.toList.flatMap Instr.tables do
    unless tables.contains values do
      let table ← defineConstant (pre ++ .mkSimple s!"table{tables.size}")
        (mkApp (mkConst ``Array [0]) K) (← mkArrayLit K (values.toList.map element))
      tables := tables.insert values table
  return { bits, tables }

/-- The parameters, proofs, operations and constants that the generated code refers to: the rows
are a `Rows n` with room for the row's `width` elements from the element offsets `current` and
`previous`. -/
structure Target extends Operations, Constants where
  K : Expr
  hints : Expr
  rowsType : Expr
  n : Expr
  width : ℕ
  current : Expr
  currentRoom : Expr
  previous : Expr
  previousRoom : Expr
  row : Expr

abbrev GenM := StateT Chain MetaM

def bind (name : Name) (type value : Expr) : GenM Expr := do
  let s ← get
  set { s with bindings := s.bindings.push (name, type, value) }
  return .bvar s.bindings.size

def field (r : ℕ) : GenM Expr := do
  match (← get).fields[r]? with
  | some e => return e
  | none => throwError "witness_kernel: field register {r} is read before it is written"

def word (r : ℕ) : GenM Expr := do
  match (← get).words[r]? with
  | some e => return e
  | none => throwError "witness_kernel: word register {r} is read before it is written"

def setField (t : Target) (r : ℕ) (value : Expr) : GenM Unit := do
  let e ← bind (.mkSimple s!"f{r}") t.K value
  modify fun s => { s with fields := s.fields.insert r e }

def setWord (r : ℕ) (value : Expr) : GenM Unit := do
  let e ← bind (.mkSimple s!"w{r}") u64Type value
  modify fun s => { s with words := s.words.insert r e }

/-- The element of a constant's word. -/
def constant (t : Target) (word : UInt64) : Expr := mkApp t.ofWord (u64 word)

def wordOpExpr (op : WordOp) (a b : Expr) : Expr :=
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

/-- A proof of `k < width`, by `decide`. -/
def columnProof (t : Target) (k : ℕ) : GenM Expr := do
  unless k < t.width do throwError "witness_kernel: column {k} is outside the row"
  let k := mkNatLit k
  let width := mkNatLit t.width
  let lt := mkApp4 (mkConst ``LT.lt [0]) (mkConst ``Nat) (mkConst ``instLTNat) k width
  return mkApp3 (mkConst ``of_decide_eq_true) lt (mkApp2 (mkConst ``Nat.decLt) k width)
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))

/-- Store an element in a column of the row. -/
def store (t : Target) (column : ℕ) (value : Expr) : GenM Unit := do
  let proof ← columnProof t column
  let rows := mkAppN t.storeAt #[t.n, mkNatLit t.width, (← get).rows, t.current,
    t.currentRoom, mkNatLit column, proof, value]
  let rows ← bind `rows t.rowsType rows
  modify fun s => { s with rows := rows }

/-- Element `column` of the row (`current`) or the previous row. -/
def load (t : Target) (current : Bool) (column : ℕ) : GenM Expr := do
  let (base, room) := if current then (t.current, t.currentRoom) else (t.previous, t.previousRoom)
  return mkAppN t.loadAt #[t.n, mkNatLit t.width, (← get).rows, base, room,
    mkNatLit column, ← columnProof t column]

partial def instr (t : Target) : Instr UInt64 → GenM Unit
  | .word op dest left right => do setWord dest (wordOpExpr op (← word left) (← word right))
  | .field op dest left right => do
      let f := match op with | .add => t.add | .mul => t.mul
      setField t dest (mkApp2 f (← field left) (← field right))
  | .fieldEq dest left right => do
      setWord dest (mkApp2 t.eqField (← field left) (← field right))
  | .selectWord dest condition yes no => do
      setWord dest (mkApp3 (mkConst ``selectWord) (← word condition) (← word yes) (← word no))
  | .selectField dest condition yes no => do
      setField t dest (mkApp3 t.selectField (← word condition) (← field yes) (← field no))
  | .value dest source => do setWord dest (mkApp t.toWord (← field source))
  | .ofWord dest source => do setField t dest (mkApp t.ofWord (← word source))
  | .ofSmallWord dest source => do setField t dest (mkApp t.ofSmallWord (← word source))
  | .inverse dest source => do setField t dest (mkApp t.inv (← field source))
  | .table dest index values => do
      let some values := t.tables[values]?
        | throwError "witness_kernel: a table of the code is not among its constants"
      setField t dest (mkApp2 t.tableElement values (← word index))
  | .pick dest index sources => do
      let sources ← sources.mapM field
      setField t dest (mkApp2 t.tableElement (← mkArrayLit t.K sources.toList) (← word index))
  | .previous dest column => do setField t dest (← load t false column)
  | .current dest column => do setField t dest (← load t true column)
  | .hint dest table width row column => do
      setField t dest (mkApp5 t.hintElement t.hints (mkNatLit table) (mkNatLit width)
        (← word row) (mkNatLit column))
  | .store column source => do store t column (← field source)
  | .storeBits column source shift count => do
      let value ← word source
      for k in [0:count] do
        store t (column + k) (mkApp3 t.bitElement t.bits value (u64 (shift + k).toUInt64))
  | .copy column previousColumn count => do
      for k in [0:count] do
        let element ← bind `element t.K (← load t false (previousColumn + k))
        store t (column + k) element
  | .loop count index result column body => do
      for k in [0:count] do
        modify fun s => { s with words := s.words.insert index (u64 k.toUInt64) }
        for i in body do instr t i
        store t (column + k) (← field result)

/-- The function `rows hints current previous row ↦ rows` running `code`: if the rows have room
for the row and the previous row, the `let`-chain of `code`, else the rows unchanged. -/
def rowFunction (K : Expr) (operations : Operations) (constants : Constants)
    (kernel : Kernel UInt64) (code : Array (Instr UInt64)) : MetaM Expr := do
  let byteArray := mkConst ``ByteArray
  let room ← atField K ``Room
  withLocalDeclD `rows byteArray fun rows =>
  withLocalDeclD `hints (mkApp (mkConst ``Array [0]) byteArray) fun hints =>
  withLocalDeclD `current (mkConst ``Nat) fun currentElements =>
  withLocalDeclD `previous (mkConst ``Nat) fun previousElements =>
  withLocalDeclD `row u64Type fun row => do
    let n := mkApp (mkConst ``ByteArray.size) rows
    let width := mkNatLit kernel.width
    let offset (elements : Expr) : Expr := mkApp (mkConst ``Nat.toUSize) elements
    let roomAt (base : Expr) : Expr := mkApp3 room n width base
    let condition := mkApp2 (mkConst ``And) (roomAt (offset currentElements))
      (roomAt (offset previousElements))
    let decidable ← synthInstance (mkApp (mkConst ``Decidable) condition)
    let body ← withLocalDeclD `room condition fun hroom => do
      let rowsType := mkApp (mkConst ``Rows) n
      let t : Target := {
        operations, constants with
        K, hints, rowsType, n, width := kernel.width
        current := offset currentElements
        currentRoom := mkApp3 (mkConst ``And.left) (roomAt (offset currentElements))
          (roomAt (offset previousElements)) hroom
        previous := offset previousElements
        previousRoom := mkApp3 (mkConst ``And.right) (roomAt (offset currentElements))
          (roomAt (offset previousElements)) hroom
        row }
      let initial := mkApp (mkConst ``Rows.of) rows
      let generate : GenM Unit := do
        modify fun s => { s with words := s.words.insert kernel.index row }
        for (r, v) in kernel.wordConstants do
          modify fun s => { s with words := s.words.insert r (u64 v) }
        for (r, v) in kernel.fieldConstants do setField t r (constant t v)
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
    mkLambdaFVars #[rows, hints, currentElements, previousElements, row] result

unsafe def evalKernelUnsafe (e : Expr) : TermElabM (Except String (Kernel UInt64)) := do
  evalExpr (Except String (Kernel UInt64)) (← inferType e) e

@[implemented_by evalKernelUnsafe]
opaque evalKernel (e : Expr) : TermElabM (Except String (Kernel UInt64))

unsafe def evalNatUnsafe (e : Expr) : TermElabM ℕ := evalExpr ℕ (mkConst ``Nat) e

@[implemented_by evalNatUnsafe]
opaque evalNat (e : Expr) : TermElabM ℕ

/-- `witness_kernel name over K := kernel`: compile `kernel : Except String (Kernel K)` to
`name.first`, `name.next` and `name : CompiledKernel K`. The elements of `K` must have values below
`2 ^ 64`, so that constants are the elements of their words. -/
elab "witness_kernel " name:ident " over " K:term " := " kernel:term : command => do
  let name := (← getCurrNamespace) ++ name.getId
  let (K, first, next, width, length) ← liftTermElabM do
    let K ← Term.elabType K
    Term.synthesizeSyntheticMVarsNoPostponing
    let K ← instantiateMVars K
    let size ← evalNat (← atField K ``FiniteField.size)
    unless size ≤ 2 ^ 64 do
      throwError "witness_kernel: the elements of {K} have values of more than 64 bits"
    let e ← Term.elabTerm kernel (← mkAppM ``Except #[mkConst ``String,
      mkApp (mkConst ``Kernel) K])
    Term.synthesizeSyntheticMVarsNoPostponing
    let words ← mkAppM ``Except.map #[← mkAppM ``Kernel.map #[← atField K ``WordField.toWord],
      ← instantiateMVars e]
    let kernel ← match ← evalKernel words with
      | .ok kernel => pure kernel
      | .error message => throwError "witness_kernel: {message}"
    let operations ← Operations.define (name ++ `operations) K
    let constants ← Constants.define name K operations (kernel.first ++ kernel.next)
    let first ← rowFunction K operations constants kernel kernel.first
    let next ← rowFunction K operations constants kernel kernel.next
    return (K, first, next, kernel.width, kernel.length)
  let byteArray := mkConst ``ByteArray
  let type := mkForall `rows .default byteArray <| mkForall `hints .default
    (mkApp (mkConst ``Array [0]) byteArray) <| mkForall `current .default (mkConst ``Nat) <|
    mkForall `previous .default (mkConst ``Nat) <| mkForall `row .default u64Type byteArray
  -- the compiler recurses along the `let`-chain, whose length is the kernel's
  for (suffix, value) in [(`first, first), (`next, next)] do
    liftCoreM <| withTheReader Core.Context (fun c => { c with
        maxRecDepth := 1000000
        maxHeartbeats := 0
        options := maxRecDepth.set c.options 1000000 }) <|
      addAndCompile <| .defnDecl <|
        mkDefinitionValEx (name ++ suffix) [] type value .opaque .safe []
  liftCoreM <| addAndCompile <| .defnDecl <| mkDefinitionValEx name []
    (mkApp (mkConst ``CompiledKernel) K)
    (mkApp5 (mkConst ``CompiledKernel.mk) K (mkNatLit width) (mkNatLit length)
      (mkConst (name ++ `first)) (mkConst (name ++ `next))) .opaque .safe []

end

end Air.Flat.WitnessGeneration.Codegen
