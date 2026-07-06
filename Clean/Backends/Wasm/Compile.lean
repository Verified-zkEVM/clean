/-
WASM WAT Compiler: WitgenIR → WAT text
-/
import Clean.Circuit.WitnessIR
import Clean.Circuit.Expression
import Clean.Circuit.Operations
import Clean.Backends.Wasm.Ast

namespace Backends.Wasm

open Witgen (FExpr NExpr BExpr VExpr Step WitgenIR)
open Ast (ValType Instr Func Module BinOp UnOp RelOp)

variable {F : Type} [FiniteField F]

/-! ## Instruction builder (AST-based) -/

structure CodeBuilder where
  instrs : List Instr := []

def CodeBuilder.push (i : Instr) (cb : CodeBuilder) : CodeBuilder :=
  { cb with instrs := i :: cb.instrs }

def CodeBuilder.pushList (is : List Instr) (cb : CodeBuilder) : CodeBuilder :=
  { cb with instrs := is.reverse ++ cb.instrs }

def CodeBuilder.build (cb : CodeBuilder) : List Instr :=
  cb.instrs.reverse

/-! ## Concise AST constructors -/

-- i64 operations
def i64.const (n : ℕ) : Instr := .const .i64 n
def i64.add : Instr := .binop .i64 .add
def i64.sub : Instr := .binop .i64 .sub
def i64.mul : Instr := .binop .i64 .mul
def i64.rem_u : Instr := .binop .i64 .rem_u
def i64.and : Instr := .binop .i64 .and
def i64.or : Instr := .binop .i64 .or
def i64.shl : Instr := .binop .i64 .shl
def i64.shr_u : Instr := .binop .i64 .shr_u
def i64.lt_u : Instr := .relop .i64 .lt_u
def i64.lt_s : Instr := .relop .i64 .lt_s
def i64.eq : Instr := .relop .i64 .eq
def i64.eqz : Instr := .relop .i64 .eqz
def i64.extend_i32_u : Instr := .unop .i64 .extend_i32_u

-- i32 operations
def i32.const (n : ℕ) : Instr := .const .i32 n
def i32.load (off : ℕ := 0) : Instr := .memLoad .i32 off 2
def i32.store (off : ℕ := 0) : Instr := .memStore .i32 off 2
def i32.wrap_i64 : Instr := .unop .i32 .wrap_i64

-- Local access (by index)
def local.get (idx : ℕ) : Instr := .localGet idx
def local.set (idx : ℕ) : Instr := .localSet idx
def local.tee (idx : ℕ) : Instr := .localTee idx

-- Control flow
def call (name : String) : Instr := .call name
def block (label : String) (body : List Instr) : Instr := .block label none body
def loop (label : String) (body : List Instr) : Instr := .loop label none body
def br (label : String) : Instr := .br label
def br_if (label : String) : Instr := .brIf label
def if_ (t : Option ValType) (thenB elseB : List Instr) : Instr := .ifElse t thenB elseB
def ifNone (thenB elseB : List Instr) : Instr := .ifElse none thenB elseB

/-! ## String-based builder (legacy, being replaced) -/

structure Builder where
  lines : List String := []
  indent : ℕ := 0

def Builder.push (line : String) (b : Builder) : Builder :=
  let pad := String.join (List.replicate b.indent "    ")
  { b with lines := (pad ++ line) :: b.lines }

def Builder.indented (n : ℕ) (f : Builder → Builder) (b : Builder) : Builder :=
  let inner := f { b with indent := b.indent + n }
  { inner with indent := b.indent }

def Builder.build (b : Builder) : String :=
  String.intercalate "\n" b.lines.reverse

/-! ## Single-word field arithmetic (numWords=1) -/

/-- Generate single-word field arithmetic as AST Func values. -/
def genSingleWordArithAST (p : ℕ) : List Func :=
  let pVal : ℕ := p
  let pm2 : ℕ := p - 2
  [
    { name := "$fadd"
      params := [("", .i64), ("", .i64)]
      results := [.i64]
      body := [.localGet 0, .localGet 1, .binop .i64 .add,
               .const .i64 pVal, .binop .i64 .rem_u] }
    ,
    { name := "$fmul"
      params := [("", .i64), ("", .i64)]
      results := [.i64]
      body := [.localGet 0, .localGet 1, .binop .i64 .mul,
               .const .i64 pVal, .binop .i64 .rem_u] }
    ,
    { name := "$fsub"
      params := [("", .i64), ("", .i64)]
      results := [.i64]
      locals := [("$d", .i64)]
      body := [.localGet 0, .localGet 1, .binop .i64 .sub, .localTee 2,
               .const .i64 0, .relop .i64 .lt_s,
               .ifElse (some .i64)
                 [.localGet 2, .const .i64 pVal, .binop .i64 .add]
                 [.localGet 2],
               .const .i64 pVal, .binop .i64 .rem_u] }
    ,
    { name := "$fpow"
      params := [("", .i64), ("", .i64)]
      results := [.i64]
      locals := [("$r", .i64), ("$b", .i64), ("$e", .i64)]
      body := [.const .i64 1, .localSet 2,
               .localGet 0, .localSet 3,
               .localGet 1, .localSet 4,
               .block "done" none [
                 .loop "loop" none [
                   .localGet 4, .relop .i64 .eqz, .brIf "done",
                   .localGet 4, .const .i64 1, .binop .i64 .and,
                   .relop .i64 .eqz,
                   .ifElse none [] [.localGet 2, .localGet 3, .call "$fmul", .localSet 2],
                   .localGet 3, .localGet 3, .call "$fmul", .localSet 3,
                   .localGet 4, .const .i64 1, .binop .i64 .shr_u, .localSet 4,
                   .br "loop"
                 ]
               ],
               .localGet 2] }
    ,
    { name := "$finv"
      params := [("", .i64)]
      results := [.i64]
      body := [.localGet 0, .const .i64 pm2, .call "$fpow"] }
  ]

def genSingleWordArith (p : ℕ) : String :=
  String.intercalate "\n" ([s!"  ;; Field arithmetic modulo {toString p} (single-word)"]
    ++ (genSingleWordArithAST p).map Ast.Func.toString)

/-! ## Multi-word field arithmetic (numWords > 1) -/

/-- Split a Nat into numWords 64-bit limbs (little-endian). -/
def toLimbs (n numWords : ℕ) : List ℕ :=
  List.range numWords |>.map fun i => (n >>> (i * 64)) % (2^64)

/-- 64×64→128 multiplication helper (AST version).
    Locals: a_lo(2), a_hi(3), b_lo(4), b_hi(5), p00(6), p01(7), p10(8), p11(9), lo(10), hi(11), tmp(12) -/
def genMul64x64AST : Func :=
  let _a := 0; let _b := 1; let a_lo := 2; let a_hi := 3; let b_lo := 4; let b_hi := 5
  let p00 := 6; let p01 := 7; let p10 := 8; let p11 := 9; let lo := 10; let hi := 11; let tmp := 12
  { name := "$mul64x64"
    params := [("$a", .i64), ("$b", .i64)]
    results := [.i64, .i64]
    locals := [("$a_lo", .i64), ("$a_hi", .i64), ("$b_lo", .i64), ("$b_hi", .i64),
               ("$p00", .i64), ("$p01", .i64), ("$p10", .i64), ("$p11", .i64),
               ("$lo", .i64), ("$hi", .i64), ("$tmp", .i64)]
    body :=
      [ local.get _a, i64.const 0xFFFFFFFF, i64.and, local.set a_lo,
        local.get _a, i64.const 32, i64.shr_u, local.set a_hi,
        local.get _b, i64.const 0xFFFFFFFF, i64.and, local.set b_lo,
        local.get _b, i64.const 32, i64.shr_u, local.set b_hi ]
      ++ [ local.get a_lo, local.get b_lo, i64.mul, local.set p00 ]
      ++ [ local.get a_lo, local.get b_hi, i64.mul, local.set p01 ]
      ++ [ local.get a_hi, local.get b_lo, i64.mul, local.set p10 ]
      ++ [ local.get a_hi, local.get b_hi, i64.mul, local.set p11 ]
      -- Compute v1+v2 first, detect overflow (carry1)
      ++ [ local.get p01, i64.const 0xFFFFFFFF, i64.and, i64.const 32, i64.shl,
           local.get p10, i64.const 0xFFFFFFFF, i64.and, i64.const 32, i64.shl,
           i64.add, local.tee tmp,
           local.get p01, i64.const 0xFFFFFFFF, i64.and, i64.const 32, i64.shl,
           i64.lt_u, i64.extend_i32_u, local.set hi ]  -- carry1 in hi temporarily
      -- lo = p00 + tmp, detect carry2
      ++ [ local.get p00, local.get tmp, i64.add, local.set lo,
           local.get lo, local.get p00, i64.lt_u, i64.extend_i32_u,
           local.get hi, i64.add, local.set hi ]  -- hi = carry1 + carry2
      -- Add high parts: hi += p11 + (p01>>32) + (p10>>32)
      ++ [ local.get hi, local.get p11, i64.add,
           local.get p01, i64.const 32, i64.shr_u, i64.add,
           local.get p10, i64.const 32, i64.shr_u, i64.add,
           local.set hi ]
      ++ [ local.get lo, local.get hi ]
  }

def genMul64x64 : String := Ast.Func.toString genMul64x64AST

/-- AST version: c[k] += a[i]*b[j] with full carry propagation.
    Uses locals: a(0..N-1), b(N..2N-1), lo(2N), hi(2N+1), carry(2N+2), sum(2N+3), c(2N+4..2N+4+2N-1) -/
def genSchoolbookAccum (N i j srcAOff srcBOff destOff : ℕ) : List Instr :=
  let k := i + j
  let aIdx := srcAOff + i
  let bIdx := srcBOff + j
  let loIdx := 2*N      -- working locals are still at 2N..2N+3
  let hiIdx := 2*N + 1
  let carryIdx := 2*N + 2
  let sumIdx := 2*N + 3
  let dIdx (x : ℕ) : ℕ := destOff + x
  let dk := dIdx k
  let dk1 := dIdx (k+1)
  let body : List Instr :=
    [ local.get aIdx, local.get bIdx, call "$mul64x64", local.set hiIdx, local.set loIdx,
      local.get dk, local.get loIdx, i64.add, local.tee dk,
      local.get loIdx, i64.lt_u, i64.extend_i32_u, local.set carryIdx,
      local.get hiIdx, local.get carryIdx, i64.add, local.tee sumIdx,
      local.get hiIdx, i64.lt_u, i64.extend_i32_u, local.set carryIdx,
      local.get dk1, local.get sumIdx, i64.add, local.tee dk1,
      local.get sumIdx, i64.lt_u, i64.extend_i32_u,
      local.get carryIdx, i64.or, local.set carryIdx ]
  let propagate : List Instr :=
    (List.range ((2*N) - (k+2))) >>= fun d =>
      let idx := k + 2 + d
      [ local.get (dIdx idx), local.get carryIdx, i64.add, local.tee (dIdx idx),
        local.get carryIdx, i64.lt_u, i64.extend_i32_u, local.set carryIdx ]
  body ++ propagate

/-- Full schoolbook for two N-limb operands. -/
def genSchoolbook (N srcAOff srcBOff destOff : ℕ) : List Instr :=
  (List.range N) >>= fun i =>
    (List.range N) >>= fun j =>
      genSchoolbookAccum N i j srcAOff srcBOff destOff

/-- Generate multi-word modular multiplication AST Func with Barrett reduction. -/
def genFmulAST (p numWords : ℕ) : Func :=
  let N := numWords
  let limbs2N := 2 * N
  let rModP := (2^(N*64)) % p
  let rLimbs := toLimbs rModP N
  let pLimbs := toLimbs p N
  -- Local indices (after 2N params)
  let loIdx := 2*N; let hiIdx := 2*N+1; let carryIdx := 2*N+2; let sumIdx := 2*N+3
  let cBase := 2*N+4; let tBase := cBase+limbs2N; let rBase := tBase+limbs2N; let pBase := rBase+N
  -- Main schoolbook: a(0) × b(N) → c(cBase)
  let mainSB := genSchoolbook N 0 N cBase
  -- Reduction schoolbook: c_hi(cBase+N) × r(rBase) → t(tBase)
  let redSB := genSchoolbook N (cBase+N) rBase tBase
  -- Add t_lo to c_lo (addRed low)
  let addRedLo : List Instr :=
    [ local.get (cBase+0), local.get (tBase+0), i64.add, local.set (cBase+0),
      local.get (cBase+0), local.get (tBase+0), i64.lt_u, i64.extend_i32_u, local.set carryIdx ]
    ++ ((List.range (N-1)) >>= fun i =>
      let idx := i + 1
      [ local.get (cBase+idx), local.get (tBase+idx), i64.add, local.get carryIdx, i64.add, local.tee (cBase+idx),
        local.get (tBase+idx), i64.lt_u, i64.extend_i32_u,
        local.get (cBase+idx), local.get carryIdx, i64.lt_u, i64.extend_i32_u, i64.or, local.set carryIdx ])
  -- Set c_hi = t_hi (replacement, not addition — the reduced value is c_lo_new + t_hi * 2^256)
  let setCHi : List Instr :=
    ((List.range N) >>= fun i => [ local.get (tBase+N+i), local.set (cBase+N+i) ])
  let addRed : List Instr := addRedLo ++ setCHi
  -- Carry elimination loop
  let carryLoop : List Instr :=
    [ block "carry_done" [
        loop "carry_loop" (
          [ local.get carryIdx, i64.eqz, br_if "carry_done", i64.const 0, local.set carryIdx,
            local.get (cBase+0), local.get (rBase+0), i64.add, local.tee (cBase+0),
            local.get (cBase+0), local.get (rBase+0), i64.lt_u, i64.extend_i32_u, local.set carryIdx ]
          ++ ((List.range (N-1)) >>= fun i =>
            let idx := i + 1
            [ local.get (cBase+idx), local.get (rBase+idx), i64.add, local.get carryIdx, i64.add, local.tee (cBase+idx),
              local.get (cBase+idx), local.get (rBase+idx), i64.lt_u, i64.extend_i32_u,
              local.get (cBase+idx), local.get carryIdx, i64.lt_u, i64.extend_i32_u, i64.or, local.set carryIdx ])
          ++ [ br "carry_loop" ]
        ) ] ]
  -- Conditional subtraction: c - p → t, if no borrow use t (up to 3 passes for safety)
  let subOne : List Instr :=
    [ local.get (cBase+0), local.get (pBase+0), i64.sub, local.set (tBase+0),
      local.get (cBase+0), local.get (pBase+0), i64.lt_u, i64.extend_i32_u, local.set carryIdx ]
    ++ ((List.range (N-1)) >>= fun i =>
      let idx := i + 1
      [ local.get (cBase+idx), local.get (pBase+idx), i64.sub, local.get carryIdx, i64.sub, local.set (tBase+idx),
        local.get (cBase+idx), local.get (pBase+idx), i64.lt_u, i64.extend_i32_u,
        local.get (cBase+idx), local.get (pBase+idx), i64.eq, i64.extend_i32_u,
        local.get carryIdx, i64.and, i64.or, local.set carryIdx ])
    ++ [ local.get carryIdx, i64.eqz,
         .ifElse none ((List.range N) >>= fun i => [ local.get (tBase+i), local.set (cBase+i) ]) [] ]
  let condSub : List Instr := subOne ++ subOne ++ subOne
  -- Init: zero out c and t, load r and p constants
  let initAll : List Instr :=
    ((List.range limbs2N) >>= fun i => [ i64.const 0, local.set (cBase+i) ]) ++
    ((List.range limbs2N) >>= fun i => [ i64.const 0, local.set (tBase+i) ]) ++
    ((rLimbs.zip (List.range N)) >>= fun (val, i) => [ i64.const val, local.set (rBase+i) ]) ++
    ((pLimbs.zip (List.range N)) >>= fun (val, i) => [ i64.const val, local.set (pBase+i) ])
  -- Result: return c[0..N-1]
  let rets : List Instr := (List.range N) >>= fun i => [ local.get (cBase+i) ]
  -- Handle t_hi from Barrett: copy to c_hi, zero t, run redSB+addRed again
  let onePass := redSB ++ addRed ++ carryLoop
  { name := "$fmul"
    params := ((List.range N).map fun i => (s!"$a{i}", ValType.i64)) ++ ((List.range N).map fun i => (s!"$b{i}", ValType.i64))
    results := List.replicate N ValType.i64
    locals :=
      [("$lo", ValType.i64), ("$hi", ValType.i64), ("$carry", ValType.i64), ("$sum", ValType.i64)]
      ++ ((List.range limbs2N).map fun i => (s!"$c{i}", ValType.i64))
      ++ ((List.range limbs2N).map fun i => (s!"$t{i}", ValType.i64))
      ++ ((List.range N).map fun i => (s!"$r{i}", ValType.i64))
      ++ ((List.range N).map fun i => (s!"$p{i}", ValType.i64))
    body := initAll ++ mainSB ++ onePass ++ onePass ++ onePass ++ onePass ++ condSub ++ rets }

def genFmul (p numWords : ℕ) : String := Ast.Func.toString (genFmulAST p numWords)

def genFaddAST (numWords : ℕ) : Func :=
  let N := numWords
  let ri (i : ℕ) : ℕ := 2*N + i   -- result limbs at offset 2*N
  let cIdx : ℕ := 2*N + N          -- carry at 3*N
  let addLimb0 : List Instr :=
    [ local.get 0, local.get N, i64.add, local.set (ri 0),
      local.get (ri 0), local.get 0, i64.lt_u, i64.extend_i32_u, local.set cIdx ]
  let addRest : List Instr := (List.range (N-1)) >>= fun i =>
    let idx := i + 1
    [ local.get idx, local.get (N + idx), i64.add, local.get cIdx, i64.add, local.set (ri idx),
      local.get (ri idx), local.get idx, i64.lt_u, i64.extend_i32_u,
      local.get (ri idx), local.get (N + idx), i64.lt_u, i64.extend_i32_u, i64.or, local.set cIdx ]
  let rets : List Instr := (List.range N) >>= fun i => [ local.get (ri i) ]
  { name := "$fadd"
    params := ((List.range N).map fun i => (s!"$a{i}", .i64)) ++ ((List.range N).map fun i => (s!"$b{i}", .i64))
    results := List.replicate N .i64
    locals := ((List.range N).map fun i => (s!"$r{i}", .i64)) ++ [("$c", .i64)]
    body := addLimb0 ++ addRest ++ rets }

def genFadd (numWords : ℕ) : String := Ast.Func.toString (genFaddAST numWords)

/-- Generate multi-word modular subtraction as AST Func. -/
def genFsubAST (numWords : ℕ) : Func :=
  let N := numWords
  let ri (i : ℕ) : ℕ := 2*N + i
  let brIdx : ℕ := 2*N + N
  let subLimb0 : List Instr :=
    [ local.get 0, local.get N, i64.sub, local.set (ri 0),
      local.get 0, local.get N, i64.lt_u, i64.extend_i32_u, local.set brIdx ]
  let subRest : List Instr := (List.range (N-1)) >>= fun i =>
    let idx := i + 1
    [ local.get idx, local.get (N + idx), i64.sub, local.get brIdx, i64.sub, local.set (ri idx),
      local.get idx, local.get (N + idx), i64.lt_u, i64.extend_i32_u,
      local.get idx, local.get (N + idx), i64.eq, i64.extend_i32_u,
      local.get brIdx, i64.and, i64.or, local.set brIdx ]
  let rets : List Instr := (List.range N) >>= fun i => [ local.get (ri i) ]
  { name := "$fsub"
    params := ((List.range N).map fun i => (s!"$a{i}", .i64)) ++ ((List.range N).map fun i => (s!"$b{i}", .i64))
    results := List.replicate N .i64
    locals := ((List.range N).map fun i => (s!"$r{i}", .i64)) ++ [("$br", .i64)]
    body := subLimb0 ++ subRest ++ rets }

def genFsub (numWords : ℕ) : String := Ast.Func.toString (genFsubAST numWords)

/-- Generate multi-word modular inverse as AST Func (Fermat square-and-multiply). -/
def genFinvAST (p numWords : ℕ) : Func :=
  let N := numWords
  let exp := p - 2
  let bitPositions := List.range (N*64) |>.reverse
  let msb := (bitPositions.find? fun b => (exp >>> b) % 2 = 1).getD (N*64 - 1)
  let ri (i : ℕ) : ℕ := N + i  -- r limbs at offset N (after params a0..a{N-1})
  let pushR : List Instr := (List.range N) >>= fun i => [ local.get (ri i) ]
  let pushA : List Instr := (List.range N) >>= fun i => [ local.get i ]
  let captureR : List Instr := (List.range N).reverse >>= fun i => [ local.set (ri i) ]
  let square : List Instr := pushR ++ pushR ++ [ call "$fmul" ] ++ captureR
  let multiply : List Instr := pushR ++ pushA ++ [ call "$fmul" ] ++ captureR
  let init : List Instr :=
    (i64.const 1 :: (List.replicate (N-1) (i64.const 0))) ++ captureR
  let steps : List Instr := (List.range (msb+1) |>.reverse) >>= fun b =>
    if (exp >>> b) % 2 = 1 then square ++ multiply else square
  { name := "$finv"
    params := (List.range N).map fun i => (s!"$a{i}", .i64)
    results := List.replicate N .i64
    locals := (List.range N).map fun i => (s!"$r{i}", .i64)
    body := init ++ steps ++ pushR }

def genFinv (p numWords : ℕ) : String := Ast.Func.toString (genFinvAST p numWords)

/-- Generate multi-word arithmetic as AST Func list. -/
def genMultiWordArithAST (p numWords : ℕ) : List Func :=
  [ genMul64x64AST, genFmulAST p numWords, genFaddAST numWords, genFsubAST numWords, genFinvAST p numWords ]

def genMultiWordArith (p numWords : ℕ) : String :=
  let ps := toString p
  let N := numWords
  let nBits := N * 64
  String.intercalate "\n" ([
    s!"  ;; Multi-word field arithmetic for prime {ps} ({N} words, {nBits} bits)"
  ] ++ (genMultiWordArithAST p numWords).map Ast.Func.toString)

def fieldHelpers (p : ℕ) (numWords : ℕ) : String :=
  if numWords = 1 then
    genSingleWordArith p
  else
    genMultiWordArith p numWords

structure VarMap where
  env : List (ℕ × ℕ) := []
  nextLocal : ℕ := 0
  loopIdx : Option ℕ := none
  letBase : ℕ := 0
  numWords : ℕ := 1

def VarMap.init (numInputs : ℕ) (numWords : ℕ := 1) : VarMap :=
  { env := List.range numInputs |>.map fun i => (i, i * numWords)
    nextLocal := numInputs * numWords
    numWords }

def VarMap.lookup (vm : VarMap) (idx : ℕ) : ℕ :=
  match vm.env.find? fun (i, _) => i = idx with | some (_, w) => w | none => idx * vm.numWords

def VarMap.alloc (vm : VarMap) (m : ℕ) (baseVarIdx : ℕ) : VarMap × List ℕ :=
  let nw := vm.numWords
  let wasmLocals := List.range (m * nw) |>.map fun i => vm.nextLocal + i
  let newEnv := (List.range m |>.map fun i => (baseVarIdx + i, vm.nextLocal + i * nw)) ++ vm.env
  ({ env := newEnv, nextLocal := vm.nextLocal + m * nw, loopIdx := vm.loopIdx,
     letBase := vm.letBase, numWords := nw }, wasmLocals)

def pushConst (c : F) (vm : VarMap) (b : Builder) : Builder :=
  let nw := vm.numWords
  let val := FiniteField.val c
  if nw = 1 then
    b.push s!"i64.const {val}"
  else
    List.range nw |>.foldl (fun (b' : Builder) (w : ℕ) =>
      let limb := (val >>> (w * 64)) % (2^64)
      b'.push s!"i64.const {limb}") b

def pushVar (idx : ℕ) (vm : VarMap) (b : Builder) : Builder :=
  let nw := vm.numWords
  let base := vm.lookup idx
  if nw = 1 then
    b.push s!"local.get {base}"
  else
    List.range nw |>.foldl (fun (b' : Builder) (w : ℕ) =>
      b'.push s!"local.get {base + w}") b

mutual
partial def compileFExpr (vm : VarMap) : FExpr F → Builder → Builder
  | .const c, b => pushConst c vm b
  | .add a e, b => let b := compileFExpr vm a b; let b := compileFExpr vm e b; b.push "call $fadd"
  | .mul a e, b => let b := compileFExpr vm a b; let b := compileFExpr vm e b; b.push "call $fmul"
  | .inv a, b => let b := compileFExpr vm a b; b.push "call $finv"
  | .expr (.var i), b => pushVar i.index vm b
  | .expr (.const c), b => pushConst c vm b
  | .expr (.add a e), b => let b := compileFExpr vm (.expr a) b; let b := compileFExpr vm (.expr e) b; b.push "call $fadd"
  | .expr (.mul a e), b => let b := compileFExpr vm (.expr a) b; let b := compileFExpr vm (.expr e) b; b.push "call $fmul"
  | .ite c t e, b =>
    let nw := vm.numWords
    if nw = 1 then
      let b := compileBExpr vm c b
      let b := b.push "(if (result i64) (then"
      let b := Builder.indented 1 (compileFExpr vm t) b
      let b := b.push ") (else"
      let b := Builder.indented 1 (compileFExpr vm e) b; b.push "))"
    else
      -- Multi-word ite not yet supported; push nw zeros
      List.range nw |>.foldl (fun (b' : Builder) _ => b'.push "i64.const 0  ;; ite MW stub") b
  | .ofNat n, b => compileNExpr vm n b
  | .localVar i, b => pushVar (vm.letBase + i) vm b
  | .envGet _, b => b.push "i64.const 0  ;; envGet stub"
  | .listGet _ _, b => b.push "i64.const 0  ;; listGet stub"
  | .dataGet _ _ _ _, b => b.push "i64.const 0  ;; dataGet stub"
  | .hintGet _ _ _ _, b => b.push "i64.const 0  ;; hintGet stub"

partial def compileNExpr (vm : VarMap) : NExpr F → Builder → Builder
  | .const n, b => b.push s!"i64.const {n}"
  | .val x, b => compileFExpr vm x b
  | .idx, b => match vm.loopIdx with | some _ => b.push "local.get $idx" | none => b.push "i64.const 0"
  | .localVar i, b => b.push s!"local.get {vm.lookup (vm.letBase + i)}"
  | .add a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.add"
  | .mul a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.mul"
  | .div a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.div_u"
  | .mod a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.rem_u"
  | .land a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.and"
  | .lor a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.or"
  | .lxor a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.xor"
  | .shiftL a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.shl"
  | .shiftR a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.shr_u"
  | .ite c t e, b =>
    let b := compileBExpr vm c b
    let b := b.push "(if (result i64) (then"
    let b := Builder.indented 1 (compileNExpr vm t) b
    let b := b.push ") (else"
    let b := Builder.indented 1 (compileNExpr vm e) b; b.push "))"

partial def compileBExpr (vm : VarMap) : BExpr F → Builder → Builder
  | .true, b => b.push "i64.const 1"
  | .false, b => b.push "i64.const 0"
  | .feq a e, b => let b := compileFExpr vm a b; let b := compileFExpr vm e b; b.push "i64.eq"
  | .lt a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.lt_u"
  | .neq a e, b => let b := compileNExpr vm a b; let b := compileNExpr vm e b; b.push "i64.eq"
  | .not x, b => let b := compileBExpr vm x b; b.push "i64.eqz"
  | .and a e, b => let b := compileBExpr vm a b; let b := compileBExpr vm e b; b.push "i64.and"
end

/-! ## AST-based expression compilers (for CodeBuilder) -/

def pushConstAST (c : F) (vm : VarMap) (cb : CodeBuilder) : CodeBuilder :=
  let nw := vm.numWords
  let val := FiniteField.val c
  if nw = 1 then cb.push (i64.const val)
  else List.range nw |>.foldl (fun cb' w => cb'.push (i64.const ((val >>> (w * 64)) % (2^64)))) cb

def pushVarAST (idx : ℕ) (vm : VarMap) (cb : CodeBuilder) : CodeBuilder :=
  let nw := vm.numWords
  let base := vm.lookup idx
  if nw = 1 then cb.push (local.get base)
  else List.range nw |>.foldl (fun cb' w => cb'.push (local.get (base + w))) cb

mutual
partial def compileFExprAST (vm : VarMap) : FExpr F → CodeBuilder → CodeBuilder
  | .const c, cb => pushConstAST c vm cb
  | .add a e, cb => let cb := compileFExprAST vm a cb; let cb := compileFExprAST vm e cb; cb.push (call "$fadd")
  | .mul a e, cb => let cb := compileFExprAST vm a cb; let cb := compileFExprAST vm e cb; cb.push (call "$fmul")
  | .inv a, cb => let cb := compileFExprAST vm a cb; cb.push (call "$finv")
  | .expr (.var i), cb => pushVarAST i.index vm cb
  | .expr (.const c), cb => pushConstAST c vm cb
  | .expr (.add a e), cb => let cb := compileFExprAST vm (.expr a) cb; let cb := compileFExprAST vm (.expr e) cb; cb.push (call "$fadd")
  | .expr (.mul a e), cb => let cb := compileFExprAST vm (.expr a) cb; let cb := compileFExprAST vm (.expr e) cb; cb.push (call "$fmul")
  | .ite _ _ _, cb => cb  -- stub for MW
  | .ofNat n, cb => compileNExprAST vm n cb
  | .localVar i, cb => pushVarAST (vm.letBase + i) vm cb
  | .envGet _, cb => cb.push (i64.const 0)
  | .listGet _ _, cb => cb.push (i64.const 0)
  | .dataGet _ _ _ _, cb => cb.push (i64.const 0)
  | .hintGet _ _ _ _, cb => cb.push (i64.const 0)

partial def compileNExprAST (vm : VarMap) : NExpr F → CodeBuilder → CodeBuilder
  | .const n, cb => cb.push (i64.const n)
  | .val x, cb => compileFExprAST vm x cb
  | .idx, cb => match vm.loopIdx with | some _ => cb.push (local.get 0) | none => cb.push (i64.const 0)
  | .localVar i, cb => cb.push (local.get (vm.lookup (vm.letBase + i)))
  | .add a e, cb => let cb := compileNExprAST vm a cb; let cb := compileNExprAST vm e cb; cb.push i64.add
  | .mul a e, cb => let cb := compileNExprAST vm a cb; let cb := compileNExprAST vm e cb; cb.push i64.mul
  | .div a e, cb => let cb := compileNExprAST vm a cb; let cb := compileNExprAST vm e cb; cb.push (.binop .i64 .div_u)
  | .mod a e, cb => let cb := compileNExprAST vm a cb; let cb := compileNExprAST vm e cb; cb.push i64.rem_u
  | .land a e, cb => let cb := compileNExprAST vm a cb; let cb := compileNExprAST vm e cb; cb.push i64.and
  | .lor a e, cb => let cb := compileNExprAST vm a cb; let cb := compileNExprAST vm e cb; cb.push i64.or
  | .lxor a e, cb => let cb := compileNExprAST vm a cb; let cb := compileNExprAST vm e cb; cb.push (.binop .i64 .xor)
  | .shiftL a e, cb => let cb := compileNExprAST vm a cb; let cb := compileNExprAST vm e cb; cb.push i64.shl
  | .shiftR a e, cb => let cb := compileNExprAST vm a cb; let cb := compileNExprAST vm e cb; cb.push i64.shr_u
  | .ite _ _ _, cb => cb  -- stub

partial def compileBExprAST (vm : VarMap) : BExpr F → CodeBuilder → CodeBuilder
  | .true, cb => cb.push (i64.const 1)
  | .false, cb => cb.push (i64.const 0)
  | .feq a e, cb => let cb := compileFExprAST vm a cb; let cb := compileFExprAST vm e cb; cb.push i64.eq
  | .lt a e, cb => let cb := compileNExprAST vm a cb; let cb := compileNExprAST vm e cb; cb.push i64.lt_u
  | .neq a e, cb => let cb := compileNExprAST vm a cb; let cb := compileNExprAST vm e cb; cb.push i64.eq
  | .not x, cb => let cb := compileBExprAST vm x cb; cb.push i64.eqz
  | .and a e, cb => let cb := compileBExprAST vm a cb; let cb := compileBExprAST vm e cb; cb.push i64.and
end

/-! ## Expression flattening (shared by WASM and R1CS compilers) -/

abbrev LinComb := List (ℕ × ℕ)  -- sparse (signalIndex × coefficient) pairs
abbrev Constraint := LinComb × LinComb × LinComb  -- (A, B, C)

structure FlattenState where
  nextSignal : ℕ := 1
  constraints : List Constraint := []

def isConstant (lc : LinComb) : Bool :=
  match lc with | [(0, _)] => true | _ => false

def scaleLinComb (c : ℕ) (lc : LinComb) (p : ℕ) : LinComb :=
  lc.map fun (i, coeff) => (i, (c * coeff) % p)

def addLinCombs (a b : LinComb) (p : ℕ) : LinComb :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | (i1, c1) :: xs, (i2, c2) :: ys =>
    if i1 < i2 then (i1, c1) :: addLinCombs xs ((i2, c2) :: ys) p
    else if i1 = i2 then (i1, (c1 + c2) % p) :: addLinCombs xs ys p
    else (i2, c2) :: addLinCombs ((i1, c1) :: xs) ys p

open Expression (var const add mul) in
partial def flattenExpr (p : ℕ) (vm : VarMap) : Expression F → FlattenState → (LinComb × FlattenState)
  | .var i, st => ([(1 + vm.lookup i.index, 1)], st)  -- R1CS signal = 1 + WASM local
  | .const c, st =>
    let val := FiniteField.val c % p
    ([(0, val)], st)
  | .add a b, st =>
    let (la, st1) := flattenExpr p vm a st
    let (lb, st2) := flattenExpr p vm b st1
    (addLinCombs la lb p, st2)
  | .mul a b, st =>
    let (la, st1) := flattenExpr p vm a st
    let (lb, st2) := flattenExpr p vm b st1
    if isConstant la then
      (scaleLinComb ((la.head?.getD (0,0)).2) lb p, st2)
    else if isConstant lb then
      (scaleLinComb ((lb.head?.getD (0,0)).2) la p, st2)
    else
      let k := st2.nextSignal
      let st3 : FlattenState := { nextSignal := k + 1, constraints := (la, lb, [(k, 1)]) :: st2.constraints }
      ([(k, 1)], st3)

/-! ## WASM code generation for intermediate signals -/

/-- Generate WAT to load signal i from memory as i64. Signal 0 is the constant 1. -/
def loadSignal (i signalBase signalBytes : ℕ) : String :=
  if i = 0 then "i64.const 1"
  else s!"i32.const {signalBase + i * signalBytes}  i32.load  i64.extend_i32_u"

/-- Generate WAT to evaluate a linear combination, leaving the result as i64 on the stack. -/
def compileLinCombWAT (lc : LinComb) (signalBase signalBytes : ℕ) : String :=
  match lc with
  | [] => "i64.const 0"
  | [(0, c)] => s!"i64.const {c}"
  | [(i, c)] =>
    s!"{loadSignal i signalBase signalBytes}\n    i64.const {c}\n    call $fmul"
  | (i1, c1) :: rest =>
    -- Start with first term, then accumulate
    let first := if i1 = 0 then s!"i64.const {c1}"
      else s!"{loadSignal i1 signalBase signalBytes}\n    i64.const {c1}\n    call $fmul"
    let restWAT := rest.map fun (p : ℕ × ℕ) =>
      let i := p.1; let c := p.2
      if i = 0 then s!"    i64.const {c}\n    call $fadd"
      else s!"{loadSignal i signalBase signalBytes}\n    i64.const {c}\n    call $fmul\n    call $fadd"
    String.intercalate "\n" (first :: restWAT)

/--
Discover intermediate signals from assert expressions. Returns:
- numIntermediates: count of extra signals
- intLocals: WAT local declarations for each intermediate
- intComputation: WAT code to compute each intermediate and store to memory
- total extra signals (to add to totalSignals)
-/
def discoverAndCompileIntermediates (p : ℕ) (vm : VarMap) (flatOps : List (FlatOperation F))
    (startSignal signalBase signalBytes : ℕ) : ℕ × List String × List String :=
  -- Walk assert expressions, run flattenExpr to discover intermediates
  let (st, _) := flatOps.foldl (fun (acc : FlattenState × Unit) (op : FlatOperation F) =>
    match op with
    | .assert e =>
      let (_, st') := flattenExpr p vm e acc.1
      (st', ())
    | _ => acc
  ) ({ nextSignal := startSignal }, ())
  let numInt := st.nextSignal - startSignal
  -- Generate WAT for each intermediate constraint (la, lb, [{k, 1}])
  -- Process reversed for oldest-first dependency order
  let intConstraintsRev := List.reverse st.constraints
  -- Recursively build locals and computation lines
  let rec buildWAT (idx : ℕ) (lines : List String) (locals : List String)
      (remaining : List Constraint) : ℕ × List String × List String :=
    match remaining with
    | [] => (idx, lines, locals)
    | (la, lb, [(k, _)]) :: rest =>
      let localName := s!"$int_{idx}"
      let laWAT := compileLinCombWAT la signalBase signalBytes
      let lbWAT := compileLinCombWAT lb signalBase signalBytes
      let computeLine := String.intercalate "\n" [
        s!"{laWAT}",
        s!"{lbWAT}",
        s!"    call $fmul",
        s!"    local.set {localName}",
        s!"    i32.const {signalBase + k * signalBytes}  local.get {localName}  i32.wrap_i64  i32.store"
      ]
      buildWAT (idx + 1) (computeLine :: lines) (s!"(local {localName} i64)" :: locals) rest
    | _ :: rest => buildWAT idx lines locals rest
  let (_, lines, locals) := buildWAT 0 [] [] intConstraintsRev
  (numInt, List.reverse locals, List.reverse lines)

/-! ## Module compilation -/

def compileSteps (vm : VarMap) (vi : ℕ) (steps : List (Step F)) : VarMap × ℕ × List String :=
  steps.foldl (fun ((vm, vi, ls) : VarMap × ℕ × List String) step =>
    match step with
    | .letF e =>
      let eb : Builder := {}
      let eb := compileFExpr vm e eb
      let (vm', locs) := vm.alloc 1 vi
      (vm', vi + 1, ls ++ [eb.build, s!"    local.set {locs.head?.getD 0}"])
    | .letN e =>
      let eb : Builder := {}
      let eb := compileNExpr vm e eb
      let (vm', locs) := vm.alloc 1 vi
      (vm', vi + 1, ls ++ [eb.build, s!"    local.set {locs.head?.getD 0}"])
  ) (vm, vi, [])

def compileLit (vm : VarMap) (vi : ℕ) (acc : List String) (es : List (FExpr F)) : VarMap × ℕ × List String :=
  es.foldl (fun ((vm, vi, ls) : VarMap × ℕ × List String) (e : FExpr F) =>
    let eb : Builder := {}
    let eb := compileFExpr vm e eb
    let (vm', locs) := vm.alloc 1 vi
    (vm', vi + 1, ls ++ [eb.build, s!"    local.set {locs.head?.getD 0}"])
  ) (vm, vi, acc)

def compileVExpr (vm : VarMap) (vi : ℕ) (acc : List String) : {m : ℕ} → VExpr F m → VarMap × ℕ × List String
  | _, .lit es => compileLit vm vi acc es.toList
  | _, .mapRange n body =>
    match body with
    | .envGet _ => (vm, vi, acc)
    | _ =>
      let (vmOut, _) := vm.alloc n vi
      let outBase := vmOut.nextLocal - n
      let ls := (List.range n).foldl (fun (ls : List String) (i : ℕ) =>
        let vmB := { vmOut with loopIdx := some 0 }
        let eb : Builder := {}
        let eb := compileFExpr vmB body eb
        ls ++ [s!"    i64.const {i}", "    local.set $idx", eb.build, s!"    local.set {outBase + i}"]
      ) acc
      ({ vmOut with loopIdx := none }, vi + n, ls)
  | _, .append _ _ => (vm, vi, "    ;; append NYI" :: acc)

def flattenOp : Operation F → List (FlatOperation F)
  | .witness m code => [.witness m code]
  | .assert e => [.assert e]
  | .lookup l => [.lookup l]
  | .interact i => [.interact i]
  | .subcircuit s => s.ops.toFlat

def flattenOps (ops : List (Operation F)) : List (FlatOperation F) :=
  match ops with
  | [] => []
  | op :: rest => flattenOp op ++ flattenOps rest

def processFlatOps (numInputs : ℕ) : List (FlatOperation F) → VarMap → ℕ → List String → VarMap × ℕ × List String
  | [], vm, _, lines => (vm, numInputs, lines)
  | .witness _ (.ir steps vexpr) :: rest, vm, vi, acc =>
    let vmStep := { vm with letBase := vi }
    let (vmS, viS, stepLines) := compileSteps vmStep vi steps
    let (vmOut, viOut, outLines) := compileVExpr vmS viS stepLines vexpr
    processFlatOps numInputs rest vmOut viOut (acc ++ outLines)
  | _ :: rest, vm, vi, acc => processFlatOps numInputs rest vm vi acc

/-- Compile to AST Module (new path). Produces typed WASM AST with struct fields. -/
def compileModuleAST (fieldPrime numInputs : ℕ) (ops : List (Operation F)) (numWords : ℕ := 1) : Module :=
  let nw := numWords
  let vm := VarMap.init numInputs nw
  let flatOps := flattenOps ops
  let (finalVm, _, bodyLines) := processFlatOps numInputs flatOps vm (numInputs * nw) []
  let witnessWords := finalVm.nextLocal - numInputs * nw
  let witnessCount := witnessWords / nw
  let n32 := nw * 2
  let srwmBase := 4
  let signalBase := 4 + n32 * 4
  let signalBytes := n32 * 4
  let startSignal := 1 + finalVm.nextLocal / nw
  let (numInt, intLocals, intCode) :=
    discoverAndCompileIntermediates fieldPrime vm flatOps startSignal signalBase signalBytes
  let totalSignals := startSignal + numInt
  -- build witness computation body as raw WAT
  let outputStores := String.intercalate "\n" (List.range witnessCount >>= fun i =>
    (List.range nw).map fun w =>
      s!"    i32.const {signalBase + (1 + numInputs + i) * signalBytes + w * 4}  local.get {numInputs * nw + i * nw + w}  i32.wrap_i64  i32.store")
  let computeBodyRaw := s!"{String.intercalate "\n" bodyLines}\n{outputStores}"
  -- snarkjs ABI functions as AST
  let abiFuncs : List Func := [
    { name := "$getFieldNumLen32"
      exportName := some "getFieldNumLen32"
      results := [.i32]
      body := [i32.const n32] },
    { name := "$getRawPrime"
      exportName := some "getRawPrime"
      body := (List.range n32) >>= fun w =>
        [ i32.const (srwmBase + w * 4), i32.const ((fieldPrime >>> (w * 32)) % (2^32)), .memStore .i32 0 2 ] },
    { name := "$readSharedRWMemory"
      exportName := some "readSharedRWMemory"
      params := [("", .i32)]
      results := [.i32]
      body := [ i32.const srwmBase, local.get 0, i32.const 4,
                .binop .i32 .mul, .binop .i32 .add, .memLoad .i32 0 2 ] },
    { name := "$writeSharedRWMemory"
      exportName := some "writeSharedRWMemory"
      params := [("$j", .i32), ("$v", .i32)]
      body := [ i32.const srwmBase, local.get 0, i32.const 4,
                .binop .i32 .mul, .binop .i32 .add, local.get 1, .memStore .i32 0 2 ] },
    { name := "$getInputSignalSize"
      exportName := some "getInputSignalSize"
      params := [("", .i32), ("", .i32)]
      results := [.i32]
      body := [i32.const numInputs] },
    { name := "$getInputSize"
      exportName := some "getInputSize"
      results := [.i32]
      body := [i32.const numInputs] },
    { name := "$getWitnessSize"
      exportName := some "getWitnessSize"
      results := [.i32]
      body := [i32.const totalSignals] },
    { name := "$setInputSignal"
      exportName := some "setInputSignal"
      params := [("$hMSB", .i32), ("$hLSB", .i32), ("$idx", .i32)]
      body := [ i32.const (signalBase + signalBytes), local.get 2, i32.const signalBytes,
                .binop .i32 .mul, .binop .i32 .add,
                i32.const srwmBase, .memLoad .i32 0 2, .memStore .i32 0 2 ] },
    { name := "$getWitness"
      exportName := some "getWitness"
      params := [("$i", .i32)]
      locals := [("$tmp", ValType.i32), ("$idx", ValType.i64)]
        ++ ((List.range numInputs).map fun i => (s!"$in_{i}", ValType.i64))
        ++ (List.range (intLocals.length)).map fun idx => (s!"$int_{idx}", ValType.i64)
      body :=
        let inputLoadStr := String.intercalate "\n" ((List.range numInputs).map fun i =>
          s!"      i32.const {signalBase + (1 + i) * signalBytes} i32.load i64.extend_i32_u local.set $in_{i}")
        let inputPushStr := String.intercalate "\n" ((List.range numInputs).map fun i =>
          s!"      local.get $in_{i}")
        let gwBody := s!"{inputLoadStr}\n{inputPushStr}\n      call $compute\n{String.intercalate "\n" intCode}\n      i32.const {signalBase} i32.const 1 i32.store\n      i32.const 0 i32.const 1 i32.store"
        let gwTail := s!"    i32.const 0\n    i32.const {signalBase} local.get $i i32.const {signalBytes} i32.mul i32.add i32.load\n    i32.store offset={srwmBase}"
        [.raw s!"    i32.const 0 i32.load i32.eqz\n    (if (then\n{gwBody}\n    ))\n{gwTail}"] },
    { name := "$getMessageChar"
      exportName := some "getMessageChar"
      results := [.i32]
      body := [i32.const 0] },
    { name := "$getVersion"
      exportName := some "getVersion"
      results := [.i32]
      body := [i32.const 2] },
    { name := "$getMinorVersion"
      exportName := some "getMinorVersion"
      results := [.i32]
      body := [i32.const 0] },
    { name := "$getPatchVersion"
      exportName := some "getPatchVersion"
      results := [.i32]
      body := [i32.const 0] },
    { name := "$init"
      exportName := some "init"
      params := [("", .i32)]
      body := [ i32.const 0, i32.const 0, .memStore .i32 0 2,
                i32.const signalBase, i32.const 1, .memStore .i32 0 2 ] }
  ]
  -- Build the compute function
  let inputParams := (List.range numInputs) >>= fun i =>
    (List.range nw).map fun w => (s!"$in_{i}_{w}", .i64)
  let computeFunc : Func := {
    name := "$compute"
    params := inputParams
    locals := (List.replicate witnessWords ("", .i64)) ++ [("$idx", .i64)]
    body := [.raw computeBodyRaw]
  }
  -- Arithmetic helpers
  let arithFuncs := if nw == 1 then genSingleWordArithAST fieldPrime
    else genMultiWordArithAST fieldPrime nw ++
         -- genMultiWordArithAST doesn't include genFmul (still string-based)
         []
  -- Assemble module
  let signalInit : List ℕ := 1 :: (List.replicate (signalBytes - 1) 0)
  { memoryPages := 1
    dataSegments := [(signalBase, signalInit)]
    funcs := arithFuncs ++ [computeFunc,
      { computeFunc with name := "$witness", exportName := some "witness" }]
      ++ abiFuncs
    }

def compileModuleLegacy (fieldPrime numInputs : ℕ) (ops : List (Operation F)) (numWords : ℕ := 1) : String :=
  let nw := numWords
  let vm := VarMap.init numInputs nw
  let nw := numWords
  let vm := VarMap.init numInputs nw
  let flatOps := flattenOps ops
  let (finalVm, _, bodyLines) := processFlatOps numInputs flatOps vm (numInputs * nw) []
  let witnessWords := finalVm.nextLocal - numInputs * nw
  let witnessCount := witnessWords / nw
  let n32 := nw * 2  -- i32 words per field element
  -- Memory layout: 0=computed_flag, 4=SRWM(n32*4 bytes), 4+n32*4=signal_array(N*n32*4 bytes)
  let srwmBase := 4
  let signalBase := 4 + n32 * 4
  let signalBytes := n32 * 4  -- bytes per signal
  -- Discover R1CS intermediates from assert expressions
  let startSignal := 1 + finalVm.nextLocal / nw  -- next signal index after WASM locals + constant
  let (numInt, intLocals, intCode) :=
    discoverAndCompileIntermediates fieldPrime vm flatOps startSignal signalBase signalBytes
  let totalSignals := startSignal + numInt
  -- $compute params: each input = nw i64 values, no results (stores to memory)
  let inputParams := String.intercalate " " (List.range numInputs  >>= fun i =>
    (List.range nw).map fun w => s!"(param $in_{i}_{w} i64)")
  -- $compute locals: witnesses + idx
  let locals := String.intercalate " "
    ((List.replicate witnessWords "(local i64)") ++ ["(local $idx i64)"])
  -- After witness computation, store each witness word to signal memory
  let outputStoresInCompute := String.intercalate "\n" (List.range witnessCount  >>= fun i =>
    (List.range nw).map fun w =>
      s!"    i32.const {signalBase + (1 + numInputs + i) * signalBytes + w * 4}  local.get {numInputs * nw + i * nw + w}  i32.wrap_i64  i32.store")
  let computeBody := String.intercalate "\n" (bodyLines ++ [outputStoresInCompute])
  let results := "" -- no multi-value returns; results stored to memory
  -- Input loads: read nw i32 values per input, extend to i64, set input word locals
  let inputLoads := String.intercalate "\n" (List.range numInputs  >>= fun i =>
    (List.range nw).map fun w =>
      s!"    i32.const {signalBase + (1 + i) * signalBytes + w * 4} i32.load  i64.extend_i32_u  local.set $in_{i}_{w}")
  -- Push inputs for $compute call
  let inputPush := String.intercalate "\n" (List.range numInputs  >>= fun i =>
    (List.range nw).map fun w => s!"    local.get $in_{i}_{w}")
  -- getWitness: no need for witness locals (results stored to memory by $compute)
  let gwInputLocals := String.intercalate " " (List.range numInputs  >>= fun i =>
    (List.range nw).map fun w => s!"(local $in_{i}_{w} i64)")
  -- snarkjs ABI exports
  let snarkjsExports := String.intercalate "\n\n" [
    s!"  (func (export \"getFieldNumLen32\") (result i32) i32.const {n32})",
    s!"  (func (export \"getRawPrime\")" ++
    (String.intercalate "\n" ((List.range n32).map fun w =>
      s!"    i32.const {srwmBase + w * 4}  i32.const {(fieldPrime >>> (w * 32)) % (2^32)}  i32.store")) ++ ")",
    s!"  (func (export \"readSharedRWMemory\") (param i32) (result i32)",
    s!"    i32.const {srwmBase}  local.get 0  i32.const 4  i32.mul  i32.add  i32.load)",
    s!"  (func (export \"writeSharedRWMemory\") (param $j i32) (param $v i32)",
    s!"    i32.const {srwmBase}  local.get $j  i32.const 4  i32.mul  i32.add  local.get $v  i32.store)",
    s!"  (func (export \"getInputSignalSize\") (param i32) (param i32) (result i32) i32.const {numInputs})",
    s!"  (func (export \"getInputSize\") (result i32) i32.const {numInputs})",
    s!"  (func (export \"getWitnessSize\") (result i32) i32.const {totalSignals})",
    s!"  (func (export \"setInputSignal\") (param $hMSB i32) (param $hLSB i32) (param $idx i32)",
    s!"    i32.const {signalBase + signalBytes}  local.get $idx  i32.const {signalBytes}  i32.mul  i32.add",
    s!"    i32.const {srwmBase}  i32.load",
    s!"    i32.store)",
    s!"  (func (export \"getWitness\") (param $i i32)",
    s!"    (local $tmp i32) {gwInputLocals} {String.intercalate " " intLocals} (local $idx i64)",
    s!"    i32.const 0  i32.load  i32.eqz",
    s!"    (if (then",
    s!"{inputLoads}",
    s!"{inputPush}",
    s!"      call $compute",
    -- Compute and store intermediates (after witnesses are in memory)
    s!"{String.intercalate "\n" intCode}",
    s!"      i32.const {signalBase}  i32.const 1  i32.store",
    s!"      i32.const 0  i32.const 1  i32.store",
    s!"    ))",
    s!"    i32.const 0",
    s!"    i32.const {signalBase}  local.get $i  i32.const {signalBytes}  i32.mul  i32.add  i32.load",
    s!"    i32.store offset={srwmBase})",
    s!"  (func (export \"getMessageChar\") (result i32) i32.const 0)",
    s!"  (func (export \"getVersion\") (result i32) i32.const 2)",
    s!"  (func (export \"getMinorVersion\") (result i32) i32.const 0)",
    s!"  (func (export \"getPatchVersion\") (result i32) i32.const 0)",
    s!"  (func (export \"init\") (param i32) i32.const 0 i32.const 0 i32.store  i32.const {signalBase} i32.const 1 i32.store)"
  ]
  String.intercalate "\n" [
    s!"(module",
    s!"  (memory (export \"memory\") 1)",
    s!"  ;; Pre-initialize signal[0] = 1 (constant)",
    s!"  (data (i32.const {signalBase}) \"\\01{String.join (List.replicate (signalBytes - 1) "\\00")}\")",
    fieldHelpers fieldPrime nw,
    s!"  ;; Internal compute function (our existing witness logic)",
    s!"  (func $compute {inputParams} {results}",
    s!"    {locals}",
    computeBody,
    s!"  )",
    s!"  ;; Direct witness export (for testing)",
    s!"  (func (export \"witness\") {inputParams} {results}",
    s!"    {locals}",
    computeBody,
    s!"  )",
    snarkjsExports,
    s!")"
  ]

def compileModule (fieldPrime numInputs : ℕ) (ops : List (Operation F)) (numWords : ℕ := 1) : String :=
  let modAST := compileModuleAST fieldPrime numInputs ops numWords
  let n32 := numWords * 2
  let signalBytes := n32 * 4
  let signalBase := 4 + n32 * 4
  let dataStr := s!"  ;; Pre-initialize signal[0] = 1 (constant)\n  (data (i32.const {signalBase}) \"\\01{String.join (List.replicate (signalBytes - 1) "\\00")}\")"
  let modLines := (Module.toString modAST).splitOn "\n"
  let finalLines := (modLines.take 2) ++ [dataStr] ++ (modLines.drop 2)
  String.intercalate "\n" finalLines

end Backends.Wasm
