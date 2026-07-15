/-
WASM Compiler: compiles Clean witness-generation IR to WASM modules
with full snarkjs Circom 2 ABI compatibility.

Produces typed WASM AST (Ast.lean) and emits either WAT text or
LEB128-encoded WASM binary (Binary.lean). Supports single-word
(primes < 2^63) and multi-word (BN254-size) field arithmetic.
-/
import Clean.Circuit.WitnessIR
import Clean.Circuit.Expression
import Clean.Circuit.Operations
import Clean.Backends.Wasm.Ast

namespace Backends.Wasm

open Witgen (FExpr NExpr BExpr VExpr Step WitgenIR)
open Ast (ValType Instr Func Module BinOp UnOp RelOp)

variable {F : Type} [FiniteField F]

/-! ## Instruction builder -/

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
def i64.gt_u : Instr := .relop .i64 .gt_u
def i64.eq : Instr := .relop .i64 .eq
def i64.eqz : Instr := .relop .i64 .eqz
def i64.extend_i32_u : Instr := .unop .i64 .extend_i32_u

-- i32 operations
def i32.const (n : ℕ) : Instr := .const .i32 n
def i32.load (off : ℕ := 0) : Instr := .memLoad .i32 off 2
def i32.store (off : ℕ := 0) : Instr := .memStore .i32 off 2
def i32.wrap_i64 : Instr := .unop .i32 .wrap_i64
def i32.eqz : Instr := .relop .i32 .eqz
def i32.mul : Instr := .binop .i32 .mul
def i32.add : Instr := .binop .i32 .add

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
def if_ (t : Option ValType) (thenB elseB : List Instr) : Instr := .ifElse (match t with | some x => [x] | none => []) thenB elseB
def ifNone (thenB elseB : List Instr) : Instr := .ifElse [] thenB elseB
def ifMulti (ts : List ValType) (thenB elseB : List Instr) : Instr := .ifElse ts thenB elseB

/-! ## Single-word field arithmetic (numWords=1) -/

/-- Generate single-word field arithmetic functions. -/
def genSingleWordArith (p : ℕ) : List Func :=
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
               .ifElse [ValType.i64]
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
                   .ifElse [] [] [.localGet 2, .localGet 3, .call "$fmul", .localSet 2],
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

/-! ## Multi-word field arithmetic (numWords > 1) -/

/-- Split a Nat into numWords 64-bit limbs (little-endian). -/
def toLimbs (n numWords : ℕ) : List ℕ :=
  List.range numWords |>.map fun i => (n >>> (i * 64)) % (2^64)

/-- 64×64→128 multiplication helper.
    Locals: a_lo(2), a_hi(3), b_lo(4), b_hi(5), p00(6), p01(7), p10(8), p11(9), lo(10), hi(11), tmp(12) -/
def genMul64x64 : Func :=
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

/-- c[k] += a[i]*b[j] with full carry propagation.
    scratchOff (default 0) sets the base for 4 working locals (lo, hi, carry, sum).
    When 0, uses 2*N..2*N+3. Use a non-zero offset to avoid conflicts
    when using genSchoolbook with different N values in the same function. -/
def genSchoolbookAccum (N i j srcAOff srcBOff destOff : ℕ) (scratchOff : ℕ := 0) : List Instr :=
  let base := if scratchOff = 0 then 2*N else scratchOff
  let k := i + j
  let aIdx := srcAOff + i
  let bIdx := srcBOff + j
  let loIdx := base
  let hiIdx := base + 1
  let carryIdx := base + 2
  let sumIdx := base + 3
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

/-- Full schoolbook for two N-limb operands. scratchOff is forwarded to genSchoolbookAccum. -/
def genSchoolbook (N srcAOff srcBOff destOff : ℕ) (scratchOff : ℕ := 0) : List Instr :=
  (List.range N) >>= fun i =>
    (List.range N) >>= fun j =>
      genSchoolbookAccum N i j srcAOff srcBOff destOff scratchOff

/--
Generate multi-word modular multiplication AST Func with word-aligned Barrett reduction
(HAC Algorithm 14.42). Operates on N 64-bit limbs per field element.

Algorithm for N=4, k=256:
  1. c = a * b (8 limbs, schoolbook)
  2. q1 = c >> 192 (5 limbs)
  3. q2 = q1 * μ (5×5 schoolbook, 9 limbs, μ = floor(2^512 / p))
  4. q3 = q2 >> 320 (4 limbs)
  5. r1 = c mod 2^320 (5 limbs)
  6. r2 = (q3 * p) mod 2^320 (5 limbs)
  7. r = r1 - r2 (5-limb sub, result < 3p by Barrett guarantee)
  8. Conditional subtract p up to 2 times
  9. Return r[0..N-1]

Local layout (N=4):
  params: a[0..3] at 0-3, b[4..7] at 4-7
  scratchN4[lo,hi,carry,sum]: 8-11 (for N=4 schoolbooks)
  scratchN5[lo,hi,carry,sum]: 12-15 (for 5×5 schoolbook, avoids overlap with scratchN4 at 10-11)
  c[0..7]:      16-23 (full a*b product)
  q1[0..4]:     24-28 (c>>192), also q3[0..3]/result[0..3] at 24-27
  q2[0..8]:     29-37 (q1*μ), also r2_full[0..7] at 29-36
  muArr[0..4]:  38-42 (μ = floor(2^512/p), 5 limbs)
  pArr[0..3]:   43-46 (prime p, 4 limbs)
  r1[0..4]:     47-51 (c mod 2^320)
-/
def genFmul (p numWords : ℕ) : Func :=
  let N := numWords
  let limbs2N := 2 * N
  -- Barrett precomputed constant: μ = floor(b^(2k) / p) = floor(2^(2*N*64) / p)
  let mu := (2^(2*N*64)) / p
  let muLimbs := toLimbs mu (N+1)   -- μ has N+1 limbs (5 for N=4)
  let pLimbs := toLimbs p N          -- p has N limbs

  -- Local index layout
  let scratchN5 := 2*N + 4           -- 12 (scratch base for N+1 schoolbook, avoids N=4 at 8-11)
  let cBase := 2*N + 8               -- 16 (a*b: 8 limbs)
  let q1Base := cBase + limbs2N      -- 24 (c>>192: N+1 limbs, also q3[0..N-1] / result[0..N-1])
  -- q2 needs 2*(N+1) limbs (10 for N=4), since 5×5 schoolbook produces up to 10 limbs.
  -- Overlap with mu would corrupt the multiplier during carry propagation.
  let q2Base := q1Base + (N+1)       -- 29 (q1*μ: 2*(N+1) limbs, also r2_full[0..2N-1])
  let muBase := q2Base + 2*(N+1)     -- 39 (μ: N+1 limbs)
  let pBase := muBase + (N+1)        -- 44 (p: N limbs)
  let r1Base := pBase + N            -- 48 (c mod 2^(k+1): N+1 limbs)
  let brIdx := 2*N+2                 -- 10 (borrow flag, reuses scratchN4 carry slot)

  -- Step 1: Initialize working arrays
  let initAll : List Instr :=
    ((muLimbs.zip (List.range (N+1))) >>= fun (val, i) => [ i64.const val, local.set (muBase+i) ]) ++
    ((pLimbs.zip (List.range N)) >>= fun (val, i) => [ i64.const val, local.set (pBase+i) ])

  -- Step 2: c = a * b (N×N schoolbook → 2N limbs, scratch at 8-11)
  let mainSB := genSchoolbook N 0 N cBase

  -- Step 3: q1 = c[3..7] (c >> 192, 5 limbs)
  let extractQ1 : List Instr :=
    (List.range (N+1)) >>= fun i => [ local.get (cBase + 3 + i), local.set (q1Base + i) ]

  -- Step 4: q2 = q1 * μ (5×5 schoolbook → 9 limbs, scratch at 12-15)
  let muMult := genSchoolbook (N+1) q1Base muBase q2Base scratchN5

  -- Step 5: q3 = q2[5..8] (q2 >> 320, 4 limbs), reuse q1Base[0..3]
  let extractQ3 : List Instr :=
    (List.range N) >>= fun i => [ local.get (q2Base + 5 + i), local.set (q1Base + i) ]

  -- Step 6: r1 = c[0..4] (c mod 2^320, 5 limbs)
  let extractR1 : List Instr :=
    (List.range (N+1)) >>= fun i => [ local.get (cBase + i), local.set (r1Base + i) ]

  -- Step 7: r2_full = q3 * p (N×N schoolbook → 8 limbs, scratch at 8-11)
  -- r2 = low 5 limbs at q2Base[0..4]
  -- IMPORTANT: zero q2Base first since genSchoolbook ADDS to destination,
  -- and q2Base still contains the muMult result (q2 = q1*μ).
  let zeroR2 : List Instr :=
    (List.range limbs2N) >>= fun i => [ i64.const 0, local.set (q2Base+i) ]
  let r2Mult := genSchoolbook N q1Base pBase q2Base

  -- Step 8: r = r1 - r2 (5-limb subtraction with borrow, result at q1Base[0..3]).
  -- Barrett guarantees the result fits in 4 limbs (< 3p < 2^256 for N=4),
  -- so limb 4 is computed (for borrow detection) but discarded.
  let sub5Limb : List Instr :=
    -- Limb 0
    [ local.get (r1Base+0), local.get (q2Base+0), i64.sub, local.set (q1Base+0),
      local.get (r1Base+0), local.get (q2Base+0), i64.lt_u, i64.extend_i32_u, local.set brIdx ]
    -- Limbs 1..3
    ++ ((List.range (N-1)) >>= fun i =>
      let idx := i + 1
      [ local.get (r1Base+idx), local.get (q2Base+idx), i64.sub, local.get brIdx, i64.sub, local.set (q1Base+idx),
        local.get (r1Base+idx), local.get (q2Base+idx), i64.lt_u, i64.extend_i32_u,
        local.get (r1Base+idx), local.get (q2Base+idx), i64.eq, i64.extend_i32_u,
        local.get brIdx, i64.and, i64.or, local.set brIdx ])
    -- Limb 4: compute borrow, discard result
    ++ [ local.get (r1Base+4), local.get (q2Base+4), i64.sub, local.get brIdx, i64.sub,
         Instr.drop,
         local.get (r1Base+4), local.get (q2Base+4), i64.lt_u, i64.extend_i32_u,
         local.get (r1Base+4), local.get (q2Base+4), i64.eq, i64.extend_i32_u,
         local.get brIdx, i64.and, i64.or, local.set brIdx ]

  -- Step 9: Conditional subtraction. r = r - p if r >= p, at most 2 times.
  -- Computes r-p at q2Base[0..3], copies back to q1Base[0..3] if no borrow (r >= p).
  let subOneP : List Instr :=
    [ local.get (q1Base+0), local.get (pBase+0), i64.sub, local.set (q2Base+0),
      local.get (q1Base+0), local.get (pBase+0), i64.lt_u, i64.extend_i32_u, local.set brIdx ]
    ++ ((List.range (N-1)) >>= fun i =>
      let idx := i + 1
      [ local.get (q1Base+idx), local.get (pBase+idx), i64.sub, local.get brIdx, i64.sub, local.set (q2Base+idx),
        local.get (q1Base+idx), local.get (pBase+idx), i64.lt_u, i64.extend_i32_u,
        local.get (q1Base+idx), local.get (pBase+idx), i64.eq, i64.extend_i32_u,
        local.get brIdx, i64.and, i64.or, local.set brIdx ])
    ++ [ local.get brIdx, i64.eqz,  -- borrow=0 means r >= p
         .ifElse [] ((List.range N) >>= fun i => [ local.get (q2Base+i), local.set (q1Base+i) ]) [] ]

  -- Build return sequence. In WASM multi-value returns, the first result type
  -- corresponds to the deepest stack value (pushed first). Callers pop top-first,
  -- so we push limbs in reverse order (highest limb first) so that the lowest limb
  -- is popped first and matches the first result type.
  let rets : List Instr := (List.range N) >>= fun i => [ local.get (q1Base+i) ]

  { name := "$fmul"
    params := ((List.range N).map fun i => (s!"$a{i}", ValType.i64))
      ++ ((List.range N).map fun i => (s!"$b{i}", ValType.i64))
    results := List.replicate N ValType.i64
    locals :=
      -- scratchN4 (lo,hi,carry,sum): 4 locals at 8-11
      [("$lo", ValType.i64), ("$hi", ValType.i64), ("$carry", ValType.i64), ("$sum", ValType.i64)]
      -- scratchN5 (lo,hi,carry,sum): 4 locals at 12-15
      ++ [("$lo5", ValType.i64), ("$hi5", ValType.i64), ("$carry5", ValType.i64), ("$sum5", ValType.i64)]
      -- c[0..7]: 8 locals at 16-23
      ++ ((List.range limbs2N).map fun i => (s!"$c{i}", ValType.i64))
      -- q1[0..4] / q3[0..3] / result[0..3]: 5 locals at 24-28
      ++ ((List.range (N+1)).map fun i => (s!"$q1{i}", ValType.i64))
      -- q2[0..2*(N+1)-1] / r2_full[0..2N-1]: 2*(N+1) locals at 29.. for N=4
      ++ ((List.range (2*(N+1))).map fun i => (s!"$q2{i}", ValType.i64))
      -- muArr[0..4]: 5 locals at 38-42
      ++ ((List.range (N+1)).map fun i => (s!"$mu{i}", ValType.i64))
      -- pArr[0..3]: 4 locals at 43-46
      ++ ((List.range N).map fun i => (s!"$pArr{i}", ValType.i64))
      -- r1[0..4]: 5 locals at 47-51
      ++ ((List.range (N+1)).map fun i => (s!"$r1{i}", ValType.i64))
    body := initAll ++ mainSB ++ extractQ1 ++ muMult ++ extractQ3
            ++ extractR1 ++ zeroR2 ++ r2Mult ++ sub5Limb ++ subOneP ++ subOneP ++ rets
    exportName := none
  }

def genFadd (p numWords : ℕ) : Func :=
  let N := numWords
  let pLimbs := toLimbs p N
  let ri (i : ℕ) : ℕ := 2*N + i       -- result limbs at 2*N
  let cIdx : ℕ := 2*N + N              -- carry at 3*N
  let pBase : ℕ := 3*N + 1             -- p limbs at 3*N+1
  let tmpBase : ℕ := pBase + N         -- temp for subtraction at 4*N+1
  let brIdx : ℕ := tmpBase + N         -- borrow at 5*N+1
  -- Limb-by-limb addition
  let addLimb0 : List Instr :=
    [ local.get 0, local.get N, i64.add, local.set (ri 0),
      local.get (ri 0), local.get 0, i64.lt_u, i64.extend_i32_u, local.set cIdx ]
  let addRest : List Instr := (List.range (N-1)) >>= fun i =>
    let idx := i + 1
    [ local.get idx, local.get (N + idx), i64.add, local.get cIdx, i64.add, local.set (ri idx),
      local.get (ri idx), local.get idx, i64.lt_u, i64.extend_i32_u,
      local.get (ri idx), local.get (N + idx), i64.lt_u, i64.extend_i32_u, i64.or, local.set cIdx ]
  -- Init prime limbs
  let initP : List Instr := (pLimbs.zip (List.range N)) >>= fun (val, i) =>
    [ i64.const val, local.set (pBase + i) ]
  -- Conditional subtraction: if r >= p, return r - p; else return r
  let subLimb0 : List Instr :=
    [ local.get (ri 0), local.get (pBase), i64.sub, local.set (tmpBase),
      local.get (ri 0), local.get (pBase), i64.lt_u, i64.extend_i32_u, local.set brIdx ]
  let subRest : List Instr := (List.range (N-1)) >>= fun i =>
    let idx := i + 1
    [ local.get (ri idx), local.get (pBase + idx), i64.sub, local.get brIdx, i64.sub, local.set (tmpBase + idx),
      local.get (ri idx), local.get (pBase + idx), i64.lt_u, i64.extend_i32_u,
      local.get (ri idx), local.get (pBase + idx), i64.eq, i64.extend_i32_u,
      local.get brIdx, i64.and, i64.or, local.set brIdx ]
  -- If no borrow (r >= p), copy tmp to result. Return in reverse order.
  let condSub : List Instr :=
    [ local.get brIdx, i64.eqz,
      .ifElse [] ((List.range N) >>= fun i => [ local.get (tmpBase + i), local.set (ri i) ]) [] ]
  let rets : List Instr := (List.range N) >>= fun i => [ local.get (ri i) ]
  { name := "$fadd"
    params := ((List.range N).map fun i => (s!"$a{i}", .i64)) ++ ((List.range N).map fun i => (s!"$b{i}", .i64))
    results := List.replicate N .i64
    locals := ((List.range N).map fun i => (s!"$r{i}", .i64)) ++ [("$c", .i64)]
      ++ ((List.range N).map fun i => (s!"$pl{i}", .i64))
      ++ ((List.range N).map fun i => (s!"$t{i}", .i64))
      ++ [("$br", .i64)]
    body := initP ++ addLimb0 ++ addRest ++ subLimb0 ++ subRest ++ condSub ++ rets }

/-- Generate multi-word modular subtraction as AST Func. -/
def genFsub (numWords : ℕ) : Func :=
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
  -- Return in reverse order (highest limb first) to match $fmul convention
  let rets : List Instr := (List.range N) >>= fun i => [ local.get (ri i) ]
  { name := "$fsub"
    params := ((List.range N).map fun i => (s!"$a{i}", .i64)) ++ ((List.range N).map fun i => (s!"$b{i}", .i64))
    results := List.replicate N .i64
    locals := ((List.range N).map fun i => (s!"$r{i}", .i64)) ++ [("$br", .i64)]
    body := subLimb0 ++ subRest ++ rets }

/-- Generate multi-word modular inverse as AST Func (Fermat square-and-multiply). -/
def genFinv (p numWords : ℕ) : Func :=
  let N := numWords
  let exp := p - 2
  let bitPositions := List.range (N*64) |>.reverse
  let msb := (bitPositions.find? fun b => (exp >>> b) % 2 = 1).getD (N*64 - 1)
  let ri (i : ℕ) : ℕ := N + i  -- r limbs at offset N (after params a0..a{N-1})
  let pushR : List Instr := (List.range N) >>= fun i => [ local.get (ri i) ]
  let pushA : List Instr := (List.range N) >>= fun i => [ local.get i ]
  -- captureR pops the return values from $fmul (which pushes highest limb first,
  -- lowest limb last). Forward capture: first pop (top=lowest limb) → ri[0].
  let captureR : List Instr := (List.range N).reverse >>= fun i => [ local.set (ri i) ]
  let finvRets : List Instr := (List.range N) >>= fun i => [ local.get (ri i) ]
  let square : List Instr := pushR ++ pushR ++ [ call "$fmul" ] ++ captureR
  let multiply : List Instr := pushR ++ pushA ++ [ call "$fmul" ] ++ captureR
  let init : List Instr :=
    -- Push N limbs: 1 (limb 0, deepest), then N-1 zeros.
    -- Returns are now ascending (limb[0] deepest), captureR is reverse.
    ([i64.const 1] ++ List.replicate (N-1) (i64.const 0)) ++ captureR
  let steps : List Instr := (List.range (msb+1) |>.reverse) >>= fun b =>
    if (exp >>> b) % 2 = 1 then square ++ multiply else square
  { name := "$finv"
    params := (List.range N).map fun i => (s!"$a{i}", .i64)
    results := List.replicate N .i64
    locals := (List.range N).map fun i => (s!"$r{i}", .i64)
    body := init ++ steps ++ finvRets }

/-- Generate multi-word arithmetic as AST Func list. -/
def genMultiWordArith (p numWords : ℕ) : List Func :=
  [ genMul64x64, genFmul p numWords, genFadd p numWords, genFsub numWords, genFinv p numWords ]

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

/-! ## AST-based expression compilers (for CodeBuilder) -/

def pushConst (c : F) (vm : VarMap) (cb : CodeBuilder) : CodeBuilder :=
  let nw := vm.numWords
  let val := FiniteField.val c
  if nw = 1 then cb.push (i64.const val)
  else List.range nw |>.foldl (fun cb' w => cb'.push (i64.const ((val >>> (w * 64)) % (2^64)))) cb

def pushVar (idx : ℕ) (vm : VarMap) (cb : CodeBuilder) : CodeBuilder :=
  let nw := vm.numWords
  let base := vm.lookup idx
  if nw = 1 then cb.push (local.get base)
  else List.range nw |>.foldl (fun cb' w => cb'.push (local.get (base + w))) cb

mutual
partial def compileFExpr (vm : VarMap) : FExpr F → CodeBuilder → CodeBuilder
  | .const c, cb => pushConst c vm cb
  | .add a e, cb => let cb := compileFExpr vm a cb; let cb := compileFExpr vm e cb; cb.push (call "$fadd")
  | .mul a e, cb => let cb := compileFExpr vm a cb; let cb := compileFExpr vm e cb; cb.push (call "$fmul")
  | .inv a, cb => let cb := compileFExpr vm a cb; cb.push (call "$finv")
  | .expr (.var i), cb => pushVar i.index vm cb
  | .expr (.const c), cb => pushConst c vm cb
  | .expr (.add a e), cb => let cb := compileFExpr vm (.expr a) cb; let cb := compileFExpr vm (.expr e) cb; cb.push (call "$fadd")
  | .expr (.mul a e), cb => let cb := compileFExpr vm (.expr a) cb; let cb := compileFExpr vm (.expr e) cb; cb.push (call "$fmul")
  | .ite c t e, cb =>
    let nw := vm.numWords
    let cb := compileBExpr vm c cb
    let thenCB := compileFExpr vm t {}
    let elseCB := compileFExpr vm e {}
    -- compileBExpr pushes i64; ifElse expects i32 condition
    let results := List.replicate nw ValType.i64
    cb.push (.unop .i32 .wrap_i64) |>.push (.ifElse results thenCB.build elseCB.build)
  | .ofNat n, cb => compileNExpr vm n cb
  | .localVar i, cb => pushVar (vm.letBase + i) vm cb
  | .envGet _, cb => cb.push (i64.const 0)
  | .listGet _ _, cb => cb.push (i64.const 0)
  | .dataGet _ _ _ _, cb => cb.push (i64.const 0)
  | .hintGet _ _ _ _, cb => cb.push (i64.const 0)

partial def compileNExpr (vm : VarMap) : NExpr F → CodeBuilder → CodeBuilder
  | .const n, cb => cb.push (i64.const n)
  | .val x, cb => compileFExpr vm x cb
  | .idx, cb => match vm.loopIdx with | some _ => cb.push (local.get 0) | none => cb.push (i64.const 0)
  | .localVar i, cb => cb.push (local.get (vm.lookup (vm.letBase + i)))
  | .add a e, cb => let cb := compileNExpr vm a cb; let cb := compileNExpr vm e cb; cb.push i64.add
  | .mul a e, cb => let cb := compileNExpr vm a cb; let cb := compileNExpr vm e cb; cb.push i64.mul
  | .div a e, cb => let cb := compileNExpr vm a cb; let cb := compileNExpr vm e cb; cb.push (.binop .i64 .div_u)
  | .mod a e, cb => let cb := compileNExpr vm a cb; let cb := compileNExpr vm e cb; cb.push i64.rem_u
  | .land a e, cb => let cb := compileNExpr vm a cb; let cb := compileNExpr vm e cb; cb.push i64.and
  | .lor a e, cb => let cb := compileNExpr vm a cb; let cb := compileNExpr vm e cb; cb.push i64.or
  | .lxor a e, cb => let cb := compileNExpr vm a cb; let cb := compileNExpr vm e cb; cb.push (.binop .i64 .xor)
  | .shiftL a e, cb => let cb := compileNExpr vm a cb; let cb := compileNExpr vm e cb; cb.push i64.shl
  | .shiftR a e, cb => let cb := compileNExpr vm a cb; let cb := compileNExpr vm e cb; cb.push i64.shr_u
  | .ite c t e, cb =>
    let cb := compileBExpr vm c cb
    let thenCB := compileNExpr vm t {}
    let elseCB := compileNExpr vm e {}
    cb.push (.unop .i32 .wrap_i64) |>.push (.ifElse [ValType.i64] thenCB.build elseCB.build)

partial def compileBExpr (vm : VarMap) : BExpr F → CodeBuilder → CodeBuilder
  | .true, cb => cb.push (i64.const 1)
  | .false, cb => cb.push (i64.const 0)
  | .feq a e, cb => let cb := compileFExpr vm a cb; let cb := compileFExpr vm e cb; cb.push i64.eq
  | .lt a e, cb => let cb := compileNExpr vm a cb; let cb := compileNExpr vm e cb; cb.push i64.lt_u
  | .neq a e, cb => let cb := compileNExpr vm a cb; let cb := compileNExpr vm e cb; cb.push i64.eq
  | .not x, cb => let cb := compileBExpr vm x cb; cb.push i64.eqz
  | .and a e, cb => let cb := compileBExpr vm a cb; let cb := compileBExpr vm e cb; cb.push i64.and
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
  | .var i, st => ([(1 + vm.lookup i.index / vm.numWords, 1)], st)  -- R1CS signal = 1 + field element index
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

/-! ## AST-based witness computation helpers -/

/-- Load signal i from memory. Pushes nw i64 limbs (lowest limb on top for multi-word). -/
def loadSignal (i signalBase signalBytes numWords : ℕ) : List Instr :=
  let nw := numWords
  if i = 0 then
    -- Signal 0 is the constant 1: push [1, 0, ..., 0] as nw limbs
    i64.const 1 :: (List.replicate (nw - 1) (i64.const 0))
  else
    -- Load each limb from signal memory: signalBase + i*signalBytes + w*4
    (List.range nw) >>= fun w =>
      [ i32.const (signalBase + i * signalBytes + w * 8), .memLoad .i64 0 3 ]

/-- Push a Nat constant as nw i64 limbs. -/
def pushCoeff (c numWords : ℕ) : List Instr :=
  (List.range numWords).map fun w => i64.const ((c >>> (w * 64)) % (2^64))

/-- Evaluate a linear combination over nw-limb field elements. Leaves nw i64 on the stack. -/
def compileLinComb (lc : LinComb) (signalBase signalBytes numWords : ℕ) : List Instr :=
  let nw := numWords
  match lc with
  | [] => List.replicate nw (i64.const 0)
  | [(0, c)] => pushCoeff c nw
  | [(i, c)] => loadSignal i signalBase signalBytes nw ++ pushCoeff c nw ++ [call "$fmul"]
  | (i1, c1) :: rest =>
    let first := if i1 = 0 then pushCoeff c1 nw
      else loadSignal i1 signalBase signalBytes nw ++ pushCoeff c1 nw ++ [call "$fmul"]
    let restInstrs : List Instr := rest >>= fun (i, c) =>
      if i = 0 then pushCoeff c nw ++ [call "$fadd"]
      else loadSignal i signalBase signalBytes nw ++ pushCoeff c nw ++ [call "$fmul", call "$fadd"]
    first ++ restInstrs

/--
Discover intermediate signals from assert expressions and compile to instructions.
`intLocalBase` is the starting local index for intermediate locals in the calling function.
Returns (numIntermediates, local declarations, computation instructions).
-/
def discoverAndCompileIntermediates (p : ℕ) (vm : VarMap) (flatOps : List (FlatOperation F))
    (startSignal signalBase signalBytes numWords intLocalBase : ℕ) : ℕ × List (String × ValType) × List Instr :=
  let nw := numWords
  let (st, _) := flatOps.foldl (fun (acc : FlattenState × Unit) (op : FlatOperation F) =>
    match op with
    | .assert e =>
      let (_, st') := flattenExpr p vm e acc.1
      (st', ())
    | _ => acc
  ) ({ nextSignal := startSignal }, ())
  let numInt := st.nextSignal - startSignal
  let intConstraintsRev := List.reverse st.constraints
  let rec buildAST (idx : ℕ) (instrs : List Instr) (locals : List (String × ValType))
      (remaining : List Constraint) : ℕ × List (String × ValType) × List Instr :=
    match remaining with
    | [] => (idx, locals, instrs)
    | (la, lb, [(k, _)]) :: rest =>
      let laInstrs := compileLinComb la signalBase signalBytes nw
      let lbInstrs := compileLinComb lb signalBase signalBytes nw
      -- Each intermediate uses nw consecutive locals
      let base := intLocalBase + idx * nw
      let captureAll : List Instr := (List.range nw).reverse.map fun w => local.set (base + w)
      let storeAll : List Instr := (List.range nw) >>= fun w =>
        [ i32.const (signalBase + k * signalBytes + w * 8),
          local.get (base + w), .memStore .i64 0 3 ]
      let localNames : List (String × ValType) :=
        (List.range nw).map fun w => (s!"$int_{idx}_{w}", .i64)
      let computeInstrs : List Instr := laInstrs ++ lbInstrs ++ [call "$fmul"] ++ captureAll ++ storeAll
      buildAST (idx + 1) (computeInstrs ++ instrs) (localNames ++ locals) rest
    | _ :: rest => buildAST idx instrs locals rest
  let (_, locals, instrs) := buildAST 0 [] [] intConstraintsRev
  (numInt, locals.reverse, instrs)

/-- compile let-steps (letF/letN) to instructions. -/
def compileSteps (vm : VarMap) (vi : ℕ) (steps : List (Step F)) : VarMap × ℕ × List Instr :=
  steps.foldl (fun ((vm, vi, instrs) : VarMap × ℕ × List Instr) step =>
    match step with
    | .letF e =>
      let cb := compileFExpr vm e {}
      let (vm', locs) := vm.alloc 1 vi
      -- Capture all nw limbs: forward order pops lowest limb first
      (vm', vi + 1, instrs ++ cb.build ++ locs.reverse.map fun idx => local.set idx)
    | .letN e =>
      let cb := compileNExpr vm e {}
      let (vm', locs) := vm.alloc 1 vi
      (vm', vi + 1, instrs ++ cb.build ++ locs.reverse.map fun idx => local.set idx)
  ) (vm, vi, [])

/-- compile a list of FExpr literals to instructions. -/
def compileLit (vm : VarMap) (vi : ℕ) (acc : List Instr) (es : List (FExpr F)) : VarMap × ℕ × List Instr :=
  es.foldl (fun ((vm, vi, instrs) : VarMap × ℕ × List Instr) (e : FExpr F) =>
    let cb := compileFExpr vm e {}
    let (vm', locs) := vm.alloc 1 vi
    (vm', vi + 1, instrs ++ cb.build ++ locs.reverse.map fun idx => local.set idx)
  ) (vm, vi, acc)

/-- compile a VExpr to instructions. -/
def compileVExpr (vm : VarMap) (vi : ℕ) (acc : List Instr) : {m : ℕ} → VExpr F m → VarMap × ℕ × List Instr
  | _, .lit es => compileLit vm vi acc es.toList
  | _, .mapRange n body =>
    match body with
    | .envGet _ => (vm, vi, acc)
    | _ =>
      let (vmOut, _) := vm.alloc n vi
      let outBase := vmOut.nextLocal - n
      let instrs := (List.range n).foldl (fun (is : List Instr) (i : ℕ) =>
        let vmB := { vmOut with loopIdx := some 0 }
        let cb := compileFExpr vmB body {}
        is ++ [i64.const i, local.set 0] ++ cb.build ++ [local.set (outBase + i)]
      ) acc
      ({ vmOut with loopIdx := none }, vi + n, instrs)
  | _, .append _ _ => (vm, vi, acc)

/-- process flat operations, accumulating instructions. -/
def processFlatOps (numInputs : ℕ) : List (FlatOperation F) → VarMap → ℕ → List Instr → VarMap × ℕ × List Instr
  | [], vm, _, instrs => (vm, numInputs, instrs)
  | .witness _ (.ir steps vexpr) :: rest, vm, vi, acc =>
    let vmStep := { vm with letBase := vi }
    let (vmS, viS, stepInstrs) := compileSteps vmStep vi steps
    let (vmOut, viOut, outInstrs) := compileVExpr vmS viS stepInstrs vexpr
    processFlatOps numInputs rest vmOut viOut (acc ++ outInstrs)
  | _ :: rest, vm, vi, acc => processFlatOps numInputs rest vm vi acc

/-- Flatten a nested Operation into a list of FlatOperations. -/
def flattenOp : Operation F → List (FlatOperation F)
  | .witness m code => [.witness m code]
  | .assert e => [.assert e]
  | .lookup l => [.lookup l]
  | .interact i => [.interact i]
  | .subcircuit s => s.ops.toFlat

/-- Flatten a list of Operations. -/
def flattenOps (ops : List (Operation F)) : List (FlatOperation F) :=
  match ops with
  | [] => []
  | op :: rest => flattenOp op ++ flattenOps rest

/-- Compile to a WASM Module. This is the main entry point. -/
def compileModule (fieldPrime numInputs : ℕ) (ops : List (Operation F)) (numWords : ℕ := 1) : String :=
  let nw := numWords
  let vm := VarMap.init numInputs nw
  let flatOps := flattenOps ops
  -- vi starts at numInputs so that circuit variable indices (which start at 0 for
  -- inputs) align with VarMap entries. vm.alloc adds (vi, local) for each witness,
  -- and pushVar uses the circuit variable index from the witness IR directly.
  let (finalVm, _, bodyInstrs) := processFlatOps numInputs flatOps vm numInputs []
  let witnessWords := finalVm.nextLocal - numInputs * nw
  let witnessCount := witnessWords / nw
  let n32 := nw * 2
  let srwmBase := 4
  -- Signal array must be 8-byte aligned for i64.store/i64.load
  let signalBaseRaw := 4 + n32 * 4
  let signalBase := ((signalBaseRaw + 7) / 8) * 8
  let signalBytes := n32 * 4
  let startSignal := 1 + finalVm.nextLocal / nw
  -- Local index base for intermediates in getWitness: param $i(0), $tmp(1), $idx(2), $in_*(3..)
  -- For multi-word, each input has nw limbs; locals are $in_{i}_{w}
  -- Each intermediate uses nw consecutive locals
  let intLocalBase := 3 + numInputs * nw
  let (numInt, intLocals, intCode) :=
    discoverAndCompileIntermediates fieldPrime vm flatOps startSignal signalBase signalBytes nw intLocalBase
  let totalSignals := startSignal + numInt
  -- Build witness output stores: write each 64-bit limb to signal memory.
  -- Witness i is stored at local (numInputs*nw + i*nw) since witnesses are
  -- allocated sequentially starting from numInputs*nw via vm.alloc.
  let outputStores : List Instr := (List.range witnessCount) >>= fun i =>
    (List.range nw) >>= fun w =>
      [ i32.const (signalBase + (1 + numInputs + i) * signalBytes + w * 8),
        local.get (numInputs * nw + i * nw + w),
        .memStore .i64 0 3 ]
  -- Build the compute function
  let inputParams := (List.range numInputs) >>= fun i =>
    (List.range nw).map fun w => (s!"$in_{i}_{w}", .i64)
  let computeFunc : Func := {
    name := "$compute"
    params := inputParams
    locals := (List.replicate witnessWords ("", .i64)) ++ [("$idx", .i64)]
    body := bodyInstrs ++ outputStores
  }
  -- Build getWitness body
  let gwInputLocals : List (String × ValType) :=
    (List.range numInputs) >>= fun i =>
      (List.range nw).map fun w => (s!"$in_{i}_{w}", ValType.i64)
  -- Input loads: for each input i and limb w, read i64 from signal memory
  let inputLoads : List Instr := (List.range numInputs) >>= fun i =>
    (List.range nw) >>= fun w =>
      [ i32.const (signalBase + (1 + i) * signalBytes + w * 8),
        .memLoad .i64 0 3,
        local.set (3 + i * nw + w) ]
  -- Input push: push all nw limbs per input
  let inputPush : List Instr := (List.range numInputs) >>= fun i =>
    (List.range nw) >>= fun w =>
      [ local.get (3 + i * nw + w) ]
  -- Tail: copy all n32 32-bit words of signal $i to SRWM[0..n32-1].
  let gwTail : List Instr := (List.range n32) >>= fun w =>
    [ i32.const (srwmBase + w * 4),
      i32.const signalBase, local.get 0, i32.const signalBytes, .binop .i32 .mul, .binop .i32 .add,
      i32.const (w * 4), .binop .i32 .add,
      i32.load 0,
      .memStore .i32 0 2 ]
  -- Build the getWitness function body
  let gwBody : List Instr :=
    [ i32.const 0, i32.load 0, i32.eqz ]  -- check computed flag
    ++ [ if_ none
          (inputLoads ++ inputPush ++ [call "$compute"] ++ intCode
           ++ [ i32.const signalBase, i32.const 1, i32.store 0,  -- store constant 1
                i32.const 0, i32.const 1, i32.store 0 ])           -- set computed flag
          [] ]
    ++ gwTail
  -- snarkjs ABI functions
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
      body := [i32.const (n32 / 2)] },
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
      -- For multi-word, idx ranges over nw limbs per input. Compute which
      -- element and which limb, then store the 64-bit value at the right offset.
      body := [
        -- Compute target address: signalBase + signalBytes + (idx/nw)*signalBytes + (idx%nw)*8
        i32.const (signalBase + signalBytes),
        local.get 2, i32.const nw, .binop .i32 .div_u, i32.const signalBytes, .binop .i32 .mul, .binop .i32 .add,
        local.get 2, i32.const nw, .binop .i32 .rem_u, i32.const 8, .binop .i32 .mul, .binop .i32 .add,
        -- Read 64-bit value from SRWM: low 32 bits at srwmBase, high 32 at srwmBase+4
        i32.const srwmBase, .memLoad .i32 0 2, .unop .i64 .extend_i32_u,
        i32.const (srwmBase + 4), .memLoad .i32 0 2, .unop .i64 .extend_i32_u,
        i64.const 32, i64.shl, i64.or,
        .memStore .i64 0 3
      ] },
    { name := "$getWitness"
      exportName := some "getWitness"
      params := [("$i", .i32)]
      locals := [("$tmp", ValType.i32), ("$idx", ValType.i64)]
        ++ gwInputLocals ++ intLocals
      body := gwBody },
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
  -- Arithmetic helpers
  let arithFuncs := if nw == 1 then genSingleWordArith fieldPrime
    else genMultiWordArith fieldPrime nw
  -- Assemble module. Compute required memory pages for the signal array.
  let signalInit : List ℕ := 1 :: (List.replicate (signalBytes - 1) 0)
  let memNeeded := signalBase + totalSignals * signalBytes
  let memPages := (memNeeded + 65535) / 65536  -- ceil division
  let module : Ast.Module := {
    memoryPages := memPages
    dataSegments := [(signalBase, signalInit)]
    funcs := arithFuncs ++ [computeFunc,
      { computeFunc with name := "$witness", exportName := some "witness" }]
      ++ abiFuncs
  }
  Module.toString module
