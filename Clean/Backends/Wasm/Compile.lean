/-
WASM Compiler: compiles Clean witness-generation IR to WASM modules
with full snarkjs Circom 2 ABI compatibility.

Produces a typed WASM AST (Ast.lean) and emits a binary WASM module
(Binary.lean). Supports single-word (primes ≤ 2^32, so products fit in
an i64 before modular reduction) and multi-word (BN254-size) field
arithmetic using CIOS Montgomery reduction with 64-bit limbs
(operands and results in Montgomery form).

All compilation entry points return `Except String _`: inputs the
compiler does not support produce an error with a reason.
-/
import Clean.Circuit.WitnessIR
import Clean.Circuit.Expression
import Clean.Circuit.Operations
import Clean.Backends.Wasm.Ast
import Clean.Backends.Wasm.Binary

namespace Backends.Wasm

open Witgen (FExpr U64Expr BExpr VExpr Step)
open Ast (ValType Instr Func Module BinOp UnOp RelOp)

variable {F : Type} [FiniteField F]

/-! ## Named constants -/

-- Memory / signal layout
private def srwmBaseAddress  : ℕ := 4   -- offset past 4-byte computed flag
private def bytesPerI32      : ℕ := 4   -- 32-bit word width in bytes
private def bytesPerI64      : ℕ := 8   -- 64-bit word width in bytes
private def alignmentI32     : ℕ := 2   -- i32 alignment exponent (2^2 = 4)
private def alignmentI64     : ℕ := 3   -- i64 alignment exponent (2^3 = 8)
private def wasmPageSize     : ℕ := 65536
private def wasmPageMask     : ℕ := 65535
private def computedFlagAddr : ℕ := 0   -- byte 0 = "witness computed" flag
private def computedFlagSet  : ℕ := 1
private def constSignalValue : ℕ := 1   -- signal 0 (the constant 1)

-- Multi-word arithmetic layout
private def i32PerLimb        : ℕ := 2  -- 64-bit limbs per 32-bit word
private def accumScratchSlots : ℕ := 4  -- lo, hi, carry, sum in genSchoolbookAccum
private def minMultiWordWords : ℕ := 2  -- numWords minimum when the prime needs multi-word

-- Limb / word arithmetic
private def limbBits         : ℕ := 64
private def limbModulus      : ℕ := 2^64
private def low32Mask        : ℕ := 0xFFFFFFFF
private def hiWordShift      : ℕ := 32

-- Validation
private def singleWordPrimeMax : ℕ := 2^32

-- snarkjs ABI
private def snarkjsProtocolVersion : ℕ := 2
private def snarkjsMinorVersion    : ℕ := 0
private def snarkjsPatchVersion    : ℕ := 0

-- WASM locals layout
private def getWitnessFixedLocals : ℕ := 3  -- $i(0), $tmp(1), $idx(2)
-- One extra i64 local above the shared scratch region holds the runtime
-- `listGet` index (element subexpressions would clobber it inside the region).
private def listGetIdxSlots : ℕ := 1
-- Size of the SHARED scratch region reserved at `vm.scratchBase` for
-- expression compilers. `.flt`/`.feq` (multi-word) capture both operands
-- (2*nw locals); `.ite`/`.bit`/`listGet`/`.bitsOf` use nw (or 1). Single-word
-- still needs 1 local (`.ite`/`.bit`/`listGet` capture at `scratchBase`).
-- Keeping this small lets large circuits (e.g. Keccak's 31K witnesses) stay
-- within the WASM 50K-local limit.
private def scratchReserve (nw : ℕ) : ℕ := if nw = 1 then 1 else 2 * nw
-- getInputSignalSize returns -1 (0xFFFFFFFF) for unknown input names.
private def signalNotFound : ℕ := 2^32 - 1

/-! ## Instruction builder -/

structure CodeBuilder where
  instrs : List Instr := []
deriving Inhabited

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
def i64.gt_u : Instr := .relop .i64 .gt_u
def i64.eq : Instr := .relop .i64 .eq
def i64.eqz : Instr := .relop .i64 .eqz
def i64.extend_i32_u : Instr := .unop .i64 .extend_i32_u

-- i32 operations
def i32.const (n : ℕ) : Instr := .const .i32 n
def i32.load (off : ℕ := 0) : Instr := .memLoad .i32 off alignmentI32
def i32.store (off : ℕ := 0) : Instr := .memStore .i32 off alignmentI32
def i32.wrap_i64 : Instr := .unop .i32 .wrap_i64
def i32.eqz : Instr := .relop .i32 .eqz
def i32.eq : Instr := .relop .i32 .eq
def i32.and : Instr := .binop .i32 .and

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
def if_ (t : Option ValType) (thenB elseB : List Instr) : Instr := .ifElse "" t thenB elseB

/-! ## Single-word field arithmetic (numWords=1) -/

/-- Generate single-word field arithmetic functions. -/
def genSingleWordArith (p : ℕ) : List Func :=
  let pVal : ℕ := p
  let pm2 : ℕ := p - 2
  [
    { name := "$fadd"
      params := [("", .i64), ("", .i64)]
      results := [.i64]
      body := [local.get 0, local.get 1, i64.add,
               i64.const pVal, i64.rem_u] }
    ,
    { name := "$fmul"
      params := [("", .i64), ("", .i64)]
      results := [.i64]
      body := [local.get 0, local.get 1, i64.mul,
               i64.const pVal, i64.rem_u] }
    ,
    { name := "$fpow"
      params := [("", .i64), ("", .i64)]
      results := [.i64]
      locals := [("$r", .i64), ("$b", .i64), ("$e", .i64)]
      body := [i64.const 1, local.set 2,
               local.get 0, local.set 3,
               local.get 1, local.set 4,
               block "done" [
                 loop "loop" [
                   local.get 4, i64.eqz, br_if "done",
                   local.get 4, i64.const 1, i64.and,
                   i64.eqz,
                   .ifElse "" none [] [local.get 2, local.get 3, call "$fmul", local.set 2],
                   local.get 3, local.get 3, call "$fmul", local.set 3,
                   local.get 4, i64.const 1, i64.shr_u, local.set 4,
                   br "loop"
                 ]
               ],
               local.get 2] }
    ,
    { name := "$finv"
      params := [("", .i64)]
      results := [.i64]
      body := [local.get 0, i64.const pm2, call "$fpow"] }
  ]

/-! ## Multi-word field arithmetic (numWords > 1) -/

/-- Split a Nat into numWords 64-bit limbs (little-endian). -/
def toLimbs (n numWords : ℕ) : List ℕ :=
  List.range numWords |>.map fun i => (n >>> (i * limbBits)) % limbModulus

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
      [ local.get _a, i64.const low32Mask, i64.and, local.set a_lo,
        local.get _a, i64.const hiWordShift, i64.shr_u, local.set a_hi,
        local.get _b, i64.const low32Mask, i64.and, local.set b_lo,
        local.get _b, i64.const hiWordShift, i64.shr_u, local.set b_hi ]
      ++ [ local.get a_lo, local.get b_lo, i64.mul, local.set p00 ]
      ++ [ local.get a_lo, local.get b_hi, i64.mul, local.set p01 ]
      ++ [ local.get a_hi, local.get b_lo, i64.mul, local.set p10 ]
      ++ [ local.get a_hi, local.get b_hi, i64.mul, local.set p11 ]
      -- tmp = (p01<<32) + (p10<<32); detect overflow into hi
      ++ [ local.get p01, i64.const low32Mask, i64.and, i64.const hiWordShift, i64.shl,
           local.get p10, i64.const low32Mask, i64.and, i64.const hiWordShift, i64.shl,
           i64.add, local.tee tmp,
           local.get p01, i64.const low32Mask, i64.and, i64.const hiWordShift, i64.shl,
           i64.lt_u, i64.extend_i32_u, local.set hi ]
      -- lo = p00 + tmp; detect overflow and add it to hi
      ++ [ local.get p00, local.get tmp, i64.add, local.set lo,
           local.get lo, local.get p00, i64.lt_u, i64.extend_i32_u,
           local.get hi, i64.add, local.set hi ]
      -- Add high parts: hi += p11 + (p01>>32) + (p10>>32)
      ++ [ local.get hi, local.get p11, i64.add,
           local.get p01, i64.const hiWordShift, i64.shr_u, i64.add,
           local.get p10, i64.const hiWordShift, i64.shr_u, i64.add,
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

/-- Push a Nat constant as nw i64 limbs (limb 0 deepest). -/
def pushCoeff (c numWords : ℕ) : List Instr :=
  (List.range numWords).map fun w => i64.const ((c >>> (w * limbBits)) % limbModulus)

/-- Montgomery constant n' = -p⁻¹ mod 2^64, computed via Newton iteration
    (x_{k+1} = x_k·(2 − p·x_k) mod 2^64, 6 iterations double precision to 2^64).
    Requires p odd (true for all field primes used here).
    Returns n' = -p⁻¹ mod 2^64 (i.e. 2^64 − p⁻¹, since p⁻¹ ≠ 0 for odd p). -/
def montNPrime (p : ℕ) : ℕ :=
  let m : ℕ := limbModulus
  let x1 := (1 * (2 - (p : ℤ) * 1)) % m
  let x2 := (x1 * (2 - (p : ℤ) * x1)) % m
  let x3 := (x2 * (2 - (p : ℤ) * x2)) % m
  let x4 := (x3 * (2 - (p : ℤ) * x3)) % m
  let x5 := (x4 * (2 - (p : ℤ) * x4)) % m
  let x6 := (x5 * (2 - (p : ℤ) * x5)) % m
  -- n' = -p⁻¹ mod 2^64 = 2^64 − p⁻¹ (p⁻¹ ≠ 0 since p is odd)
  (m - Int.toNat (x6 % m)) % m

/-- Montgomery radix R = 2^(N*limbBits) mod p (the Montgomery form of 1). -/
def montR (p numWords : ℕ) : ℕ := (2^(numWords * limbBits)) % p

/-- R² mod p — the constant to convert a normal-form value to Montgomery form
    (montMul(x, R²) = x·R²·R⁻¹ = x·R). -/
def montR2 (p numWords : ℕ) : ℕ := (2^(2 * numWords * limbBits)) % p

/--
Generate multi-word modular multiplication AST Func using CIOS Montgomery
reduction with 64-bit limbs (HAC Algorithm 14.36, CIOS variant). Operands are
in Montgomery form (x·R mod p); the result is in Montgomery form.

Algorithm:
  1. c = a * b (2N limbs, schoolbook)
  2. For i in 0..N-1 (Montgomery reduction):
       m = c[i] * n' mod 2^64        (n' = -p⁻¹ mod 2^64)
       c[i..i+N] += m * p            (schoolbook accumulate, carry propagates)
     After N steps c[0..N-1] = 0 and c[N..2N-1] ≡ a·b·R⁻¹ (mod p), value < 2p.
  3. Conditional subtract p once → result in [0, p).
  4. Return c[N..2N-1].

Local layout (N=4):
  params: a[0..3] at 0-3, b[4..7] at 4-7
  schoolbook scratch lo,hi,carry,sum: 8-11 (genSchoolbookAccum's default 2N..2N+3)
  c[0..8]:  12-20 (full a*b product, 2N+1 limbs for carry headroom)
  pArr:     21-24 (prime p, N limbs)
  m:        25   (Montgomery quotient)
  lo,hi,carry,sum: 26-29 (Montgomery reduction accumulate scratch)
  br:       30   (borrow flag)
-/
def genFmul (p numWords : ℕ) : Func :=
  let N := numWords
  let nPrime := montNPrime p
  let pLimbs := toLimbs p N

  -- Local index layout. NOTE: cBase must be past the schoolbook scratch
  -- (genSchoolbookAccum uses 2N..2N+3 by default), so start c at 2N+4.
  let cBase := 2*N + accumScratchSlots  -- past the schoolbook scratch (2N..2N+3)
  let pBase := cBase + 2*N + 1  -- 21 (p: N limbs)
  let mIdx := pBase + N       -- 25
  let loIdx := mIdx + 1       -- 26
  let hiIdx := loIdx + 1      -- 27
  let carryIdx := hiIdx + 1   -- 28
  let sumIdx := carryIdx + 1  -- 29
  let brIdx := sumIdx + 1     -- 30

  -- Initialize p limbs
  let initP : List Instr :=
    (pLimbs.zip (List.range N)) >>= fun (val, i) => [ i64.const val, local.set (pBase+i) ]

  -- c = a * b (N×N schoolbook → 2N limbs). genSchoolbookAccum adds into c, so pre-zero it.
  let zeroC : List Instr :=
    (List.range (2*N+1)) >>= fun i => [ i64.const 0, local.set (cBase+i) ]
  let mainSB := genSchoolbook N 0 N cBase

  -- Montgomery reduction: N steps. Step i zeroes c[i] and shifts the reduction.
  let redStep (i : ℕ) : List Instr :=
    -- m = c[i] * n' mod 2^64
    [ local.get (cBase+i), i64.const nPrime, i64.mul, local.set mIdx ]
    -- for j in 0..N-1: c[i+j] += m * p[j] (via $mul64x64), carry propagates to c[2N]
    ++ ((List.range N) >>= fun j =>
      [ local.get mIdx, local.get (pBase+j), call "$mul64x64", local.set hiIdx, local.set loIdx,
        local.get (cBase+i+j), local.get loIdx, i64.add, local.tee (cBase+i+j),
        local.get loIdx, i64.lt_u, i64.extend_i32_u, local.set carryIdx,
        local.get hiIdx, local.get carryIdx, i64.add, local.tee sumIdx,
        local.get hiIdx, i64.lt_u, i64.extend_i32_u, local.set carryIdx,
        local.get (cBase+i+j+1), local.get sumIdx, i64.add, local.tee (cBase+i+j+1),
        local.get sumIdx, i64.lt_u, i64.extend_i32_u,
        local.get carryIdx, i64.or, local.set carryIdx ]
      -- propagate carry through remaining limbs up to c[2N]
      ++ ((List.range (2*N + 1 - (i+j+2))) >>= fun d =>
        let k := i + j + 2 + d
        [ local.get (cBase+k), local.get carryIdx, i64.add, local.tee (cBase+k),
          local.get carryIdx, i64.lt_u, i64.extend_i32_u, local.set carryIdx ]))
  let redSteps := (List.range N) >>= redStep

  -- Conditional subtraction: c[N..2N-1] -= p if >= p. Result lands back in c[N..2N-1].
  -- Uses c[0..N-1] (all zero after reduction) as scratch for the trial subtraction.
  let subOneP : List Instr :=
    [ local.get (cBase+N+0), local.get (pBase+0), i64.sub, local.set (cBase+0),
      local.get (cBase+N+0), local.get (pBase+0), i64.lt_u, i64.extend_i32_u, local.set brIdx ]
    ++ ((List.range (N-1)) >>= fun i =>
      let idx := i + 1
      [ local.get (cBase+N+idx), local.get (pBase+idx), i64.sub, local.get brIdx, i64.sub, local.set (cBase+idx),
        local.get (cBase+N+idx), local.get (pBase+idx), i64.lt_u, i64.extend_i32_u,
        local.get (cBase+N+idx), local.get (pBase+idx), i64.eq, i64.extend_i32_u,
        local.get brIdx, i64.and, i64.or, local.set brIdx ])
    ++ [ local.get brIdx, i64.eqz,  -- borrow=0 means r >= p
         .ifElse "" none ((List.range N) >>= fun i => [ local.get (cBase+i), local.set (cBase+N+i) ]) [] ]

  -- Return c[N..2N-1] (lowest limb first, matching the caller convention)
  let rets : List Instr := (List.range N) >>= fun i => [ local.get (cBase+N+i) ]

  { name := "$fmul"
    params := ((List.range N).map fun i => (s!"$a{i}", ValType.i64))
      ++ ((List.range N).map fun i => (s!"$b{i}", ValType.i64))
    results := List.replicate N ValType.i64
    locals :=
      -- Declare all locals from index 2N (after 2N params) up to brIdx = 5*N+10.
      -- Layout: c[0..2N] at 2N+4..4N+4, p[0..N-1] at 4N+5..5N+4,
      -- m at 5N+5, lo 5N+6, hi 5N+7, carry 5N+8, sum 5N+9, br 5N+10.
      let totalLocals := (5*N + 11) - (2*N)
      (List.range totalLocals).map fun i => (s!"$l{i}", ValType.i64)
    body := initP ++ zeroC ++ mainSB ++ redSteps ++ subOneP ++ rets
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
  -- Two-operand adds so each carry-out is detected individually:
  --   t = a + b;  carry1 = t < a;  r = t + c;  carry2 = r < t;  carry = carry1 | carry2
  -- (The single-step `(r < a) | (r < b)` test misses a = b = 2^64-1 with
  -- carry-in 1, where r = 2^64-1 = a = b but the true carry-out is 1.)
  -- `tmpBase` holds the transient `t`; the conditional subtraction later
  -- overwrites the whole tmp region before reading it.
  let addRest : List Instr := (List.range (N-1)) >>= fun i =>
    let idx := i + 1
    [ local.get idx, local.get (N + idx), i64.add, local.tee tmpBase,
      local.get idx, i64.lt_u, i64.extend_i32_u,
      local.get tmpBase, local.get cIdx, i64.add, local.set (ri idx),
      local.get (ri idx), local.get tmpBase, i64.lt_u, i64.extend_i32_u,
      i64.or, local.set cIdx ]
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
  -- If no borrow (r >= p), copy tmp to result. Return limbs in ascending order
  -- (limb 0 deepest), matching the $fmul convention.
  let condSub : List Instr :=
    [ local.get brIdx, i64.eqz,
      .ifElse "" none ((List.range N) >>= fun i => [ local.get (tmpBase + i), local.set (ri i) ]) [] ]
  let rets : List Instr := (List.range N) >>= fun i => [ local.get (ri i) ]
  { name := "$fadd"
    params := ((List.range N).map fun i => (s!"$a{i}", .i64)) ++ ((List.range N).map fun i => (s!"$b{i}", .i64))
    results := List.replicate N .i64
    locals := ((List.range N).map fun i => (s!"$r{i}", .i64)) ++ [("$c", .i64)]
      ++ ((List.range N).map fun i => (s!"$pl{i}", .i64))
      ++ ((List.range N).map fun i => (s!"$t{i}", .i64))
      ++ [("$br", .i64)]
    body := initP ++ addLimb0 ++ addRest ++ subLimb0 ++ subRest ++ condSub ++ rets }

/-- Generate multi-word modular inverse as AST Func (Fermat square-and-multiply).
    Operates on Montgomery-form values: starting from mont(1) = R mod p, repeated
    montMul (x·y·R⁻¹) gives mont(a^e), so mont(a^(p-2)) = mont(a⁻¹). -/
def genFinv (p numWords : ℕ) : Func :=
  let N := numWords
  let exp := p - 2
  let bitPositions := List.range (N*limbBits) |>.reverse
  let msb := (bitPositions.find? fun b => (exp >>> b) % 2 = 1).getD (N*limbBits - 1)
  let ri (i : ℕ) : ℕ := N + i  -- r limbs at offset N (after params a0..a{N-1})
  let pushR : List Instr := (List.range N) >>= fun i => [ local.get (ri i) ]
  let pushA : List Instr := (List.range N) >>= fun i => [ local.get i ]
  -- $fmul pushes the lowest limb first (deepest) and the highest limb last
  -- (top of stack). captureR pops in reverse: first pop (highest limb) → ri[N-1],
  -- last pop (lowest limb) → ri[0].
  let captureR : List Instr := (List.range N).reverse >>= fun i => [ local.set (ri i) ]
  let finvRets : List Instr := (List.range N) >>= fun i => [ local.get (ri i) ]
  let square : List Instr := pushR ++ pushR ++ [ call "$fmul" ] ++ captureR
  let multiply : List Instr := pushR ++ pushA ++ [ call "$fmul" ] ++ captureR
  let init : List Instr :=
    -- Push the N limbs of R mod p (the Montgomery form of 1), limb 0 deepest;
    -- captureR stores them so ri[i] = limb i.
    (pushCoeff (montR p N) N) ++ captureR
  let steps : List Instr := (List.range (msb+1) |>.reverse) >>= fun b =>
    if (exp >>> b) % 2 = 1 then square ++ multiply else square
  { name := "$finv"
    params := (List.range N).map fun i => (s!"$a{i}", .i64)
    results := List.replicate N .i64
    locals := (List.range N).map fun i => (s!"$r{i}", .i64)
    body := init ++ steps ++ finvRets }

/-- Generate multi-word arithmetic as AST Func list. -/
def genMultiWordArith (p numWords : ℕ) : List Func :=
  [ genMul64x64, genFmul p numWords, genFadd p numWords, genFinv p numWords ]

/-- Maps circuit variable indices to WASM local indices.
    The layout is unconditional: circuit variable `i` maps to WASM local
    `i * numWords`. This holds for inputs (set up by `init`) and for witness
    outputs, which `alloc` lays out sequentially: `nextLocal` starts at
    `numInputs * numWords` and only ever advances through `alloc` (by
    `m * numWords` per `m` witnesses), in lockstep with the variable counter,
    so `nextLocal = vi * numWords` at every allocation and the mapping
    `(i, i * numWords)` is exact.

    Let-steps do NOT advance `nextLocal`: they live in a separate local-index
    space starting at `stepNext` (the witness region end, see `compileModule`),
    allocated cumulatively and never reused. They are accessed via
    `FExpr.localVar` / `U64Expr.localVar` using a direct offset from `letBase`,
    never through `lookup`. -/
structure VarMap where
  /-- Number of public input signals. -/
  numInputs : ℕ := 0
  /-- Next free WASM local index for witness outputs (grows contiguously). -/
  nextLocal : ℕ := 0
  /-- Next free WASM local index for let-step slots. Steps are dead after
      their enclosing op, but their locals are still allocated cumulatively
      (never reused), so `stepNext` grows monotonically. -/
  stepNext : ℕ := 0
  /-- Inside a `mapRange` body, the (compile-time constant) index of the current
      unrolled iteration; `none` outside of any `mapRange`. -/
  loopIdx : Option ℕ := none
  /-- WASM local index of the first let-step of the current witness op.
      `FExpr.localVar i` reads `nw` locals at `letBase + i * numWords`;
      `U64Expr.localVar i` reads the low limb at the same position.
      Steps are dead after their enclosing op, so this is set fresh per op. -/
  letBase : ℕ := 0
  numWords : ℕ := 1
  /-- The field prime, for computing Montgomery-form constants. -/
  prime : ℕ := 0
  /-- Fixed base of the SHARED scratch region (above all witness and step
      locals). Multi-word expression compilers (`.flt`/`.feq`/`.ite`/`.bit`,
      `listGet`) use `scratchBase .. scratchBase + 2*nw` as temporary locals.
      Sharing one region keeps the total local count low enough for the
      WASM 50K-local limit even with tens of thousands of witnesses. -/
  scratchBase : ℕ := 0
  /-- Number of declared output witnesses (0 when `outputVars` is empty). -/
  numOutputs : ℕ := 0
  /-- Circuit-variable indices of the circuit's output witnesses, in output
      order. When non-empty, the signal layout is outputs-first:
      signal 0 = constant, 1..numOutputs = outputs, then inputs, then the
      remaining witnesses (see `signalOfVar`). -/
  outputVars : List ℕ := []
deriving Inhabited

def VarMap.init (numInputs : ℕ) (numWords : ℕ) (prime : ℕ := 0) : VarMap :=
  { numInputs
    nextLocal := numInputs * numWords
    numWords
    prime }

/-- Look up the WASM local index for a circuit variable: `idx * numWords`
    (see the layout invariant in the `VarMap` doc comment). -/
def VarMap.lookup (vm : VarMap) (idx : ℕ) : ℕ := idx * vm.numWords

def VarMap.alloc (vm : VarMap) (m : ℕ) : VarMap × List ℕ :=
  let nw := vm.numWords
  let wasmLocals := List.range (m * nw) |>.map fun i => vm.nextLocal + i
  ({ numInputs := vm.numInputs, nextLocal := vm.nextLocal + m * nw, stepNext := vm.stepNext,
     loopIdx := vm.loopIdx, letBase := vm.letBase, numWords := nw, prime := vm.prime,
     scratchBase := vm.scratchBase, numOutputs := vm.numOutputs, outputVars := vm.outputVars },
    wasmLocals)

/-- The R1CS signal number of circuit variable `v` in the outputs-first layout:
    signal 0 = the constant 1, signals 1..numOutputs = the declared output
    witnesses (in `outputVars` order), then the inputs, then the remaining
    witnesses in variable order. With no outputs declared this is the plain
    `1 + v` layout. -/
def signalOfVar (vm : VarMap) (v : ℕ) : ℕ :=
  match vm.outputVars.findIdx? (fun o => o = v) with
  | some j => 1 + j
  | none =>
    if v < vm.numInputs then 1 + vm.numOutputs + v
    else 1 + vm.numOutputs + vm.numInputs + (v - vm.numInputs) - (vm.outputVars.countP (fun o => o < v))

/-- 64-bit FNV-1a hash (offset basis 0xCBF29CE484222325, prime 0x100000001B3),
    matching the `fnvHash` in circom_runtime (snarkjs). Input names must be
    ASCII: circom hashes UTF-16 code units, which equal the UTF-8 bytes for
    ASCII strings. -/
def fnv1a64 (s : String) : ℕ :=
  s.toUTF8.foldl (fun h b => ((h ^^^ b.toNat) * 0x100000001B3) % limbModulus) 0xCBF29CE484222325

/-! ## AST-based expression compilers (for CodeBuilder) -/

/-- Push a field constant. In multi-word (Montgomery) mode the constant is
    multiplied by R mod p so arithmetic can operate in Montgomery form. -/
def pushConst (c : F) (vm : VarMap) (cb : CodeBuilder) : CodeBuilder :=
  let nw := vm.numWords
  let p := vm.prime
  let val := if nw = 1 then FiniteField.val c else (FiniteField.val c * montR p nw) % p
  if nw = 1 then cb.push (i64.const val)
  else List.range nw |>.foldl (fun cb' w => cb'.push (i64.const ((val >>> (w * limbBits)) % limbModulus))) cb

def pushVar (idx : ℕ) (vm : VarMap) (cb : CodeBuilder) : CodeBuilder :=
  let nw := vm.numWords
  let base := vm.lookup idx
  if nw = 1 then cb.push (local.get base)
  else List.range nw |>.foldl (fun cb' w => cb'.push (local.get (base + w))) cb

/-- Push `nw` limbs from a given WASM local base index (no VarMap lookup).
    Used by `FExpr.localVar` and `U64Expr.localVar` for let-step access. -/
def pushStepVar (baseWasm nw : ℕ) (cb : CodeBuilder) : CodeBuilder :=
  if nw = 1 then cb.push (local.get baseWasm)
  else List.range nw |>.foldl (fun cb' w => cb'.push (local.get (baseWasm + w))) cb

/-- Compile an `Expression F` (var, const, add, mul) to WASM instructions.
    Structurally recursive on the expression tree, mirroring `Expression.eval`. -/
def compileExpr (vm : VarMap) : Expression F → CodeBuilder → Except String CodeBuilder
  | .var i, cb => pure (pushVar i.index vm cb)
  | .const c, cb => pure (pushConst c vm cb)
  | .add a e, cb => do
    let cb ← compileExpr vm a cb
    let cb ← compileExpr vm e cb
    pure (cb.push (call "$fadd"))
  | .mul a e, cb => do
    let cb ← compileExpr vm a cb
    let cb ← compileExpr vm e cb
    pure (cb.push (call "$fmul"))

/-! Whether a witness expression contains a `.listGet` anywhere, used to reject
    nested listGet (the runtime index slot is shared). -/
mutual
  def containsListGet (e : FExpr F) : Bool :=
    match e with
    | .expr _ | .const _ | .localVar _ => false
    | .add x y | .mul x y => containsListGet x || containsListGet y
    | .inv x => containsListGet x
    | .ofU64 n => containsListGetU n
    | .ite c t e' => containsListGetB c || containsListGet t || containsListGet e'
    | .listGet _ _ => true
    | .dataGet _ _ _ _ | .hintGet _ _ _ _ => false

  def containsListGetU (e : U64Expr F) : Bool :=
    match e with
    | .const _ | .idx | .localVar _ => false
    | .val x => containsListGet x
    | .add x y | .mul x y | .div x y | .mod x y | .land x y | .lor x y | .lxor x y
    | .shiftL x y | .shiftR x y => containsListGetU x || containsListGetU y
    | .ite c t e' => containsListGetB c || containsListGetU t || containsListGetU e'

  def containsListGetB (b : BExpr F) : Bool :=
    match b with
    | .true | .false => false
    | .feq x y | .flt x y => containsListGet x || containsListGet y
    | .neq x y | .lt x y => containsListGetU x || containsListGetU y
    | .bit x _ => containsListGet x
    | .not b' => containsListGetB b'
    | .and x y => containsListGetB x || containsListGetB y
end

mutual
/-- Compile a list of FExprs into a select-sum chain for `listGet`.
    Structurally recursive on the list, mirroring `FExpr.evalList`. -/
def compileFExprList (vm : VarMap) (idxLocal nw : ℕ) : (k : ℕ) → List (FExpr F) → Except String (List Instr)
  | _, [] => pure []
  | k, e :: es => do
    let elemCB ← compileFExpr vm e {}
    -- isK = (idx == k), a plain 0/1 i64.
    let isK : List Instr := [local.get idxLocal, i64.const k, i64.eq, i64.extend_i32_u]
    -- The selector is a field operand of $fmul, so in Montgomery mode it must
    -- be montR (the Montgomery form of 1) when selected, 0 otherwise — a raw 1
    -- would silently scale the element by R⁻¹. Recompute isK per limb so no
    -- extra local is needed.
    let selAsField : List Instr := if nw = 1 then isK
      else (List.range nw) >>= fun w =>
        isK ++ [i64.const ((montR vm.prime nw >>> (w * limbBits)) % limbModulus), i64.mul]
    let accumulate := if k = 0 then [] else [call "$fadd"]
    let rest ← compileFExprList vm idxLocal nw (k + 1) es
    pure (elemCB.build ++ selAsField ++ [call "$fmul"] ++ accumulate ++ rest)

def compileFExpr (vm : VarMap) : FExpr F → CodeBuilder → Except String CodeBuilder
  | .const c, cb => pure (pushConst c vm cb)
  | .add a e, cb => do
    let cb ← compileFExpr vm a cb
    let cb ← compileFExpr vm e cb
    pure (cb.push (call "$fadd"))
  | .mul a e, cb => do
    let cb ← compileFExpr vm a cb
    let cb ← compileFExpr vm e cb
    pure (cb.push (call "$fmul"))
  | .inv a, cb => do
    let cb ← compileFExpr vm a cb
    pure (cb.push (call "$finv"))
  | .expr e, cb => compileExpr vm e cb
  | .ite c t e, cb => do
    let nw := vm.numWords
    let cond ← compileBExpr vm c cb
    let thenCB ← compileFExpr vm t {}
    let elseCB ← compileFExpr vm e {}
    -- Capture each branch's nw-limb result to temporary locals at the shared
    -- `vm.scratchBase` region.
    -- The stack has limbs in ascending order (limb₀ deepest, limb_{nw-1} top),
    -- so `.reverse` stores limbᵢ at `tmpBase + i`.
    let tmpBase := vm.scratchBase
    let captureAll : List Instr := (List.range nw).reverse.map fun w => local.set (tmpBase + w)
    -- Load the chosen branch's result back onto the stack (lowest limb first).
    let loadBack : List Instr := (List.range nw).map fun w => local.get (tmpBase + w)
    pure (cond.push (.ifElse "" none (thenCB.build ++ captureAll) (elseCB.build ++ captureAll)) |>.pushList loadBack)
  | .ofU64 n, cb => do
    let nw := vm.numWords
    let cb ← compileU64Expr vm n cb
    -- U64Expr produces a single i64.
    if nw = 1 then
      -- Reduce mod p via $fadd with 0.
      pure (cb.push (i64.const 0) |>.push (call "$fadd"))
    else do
      -- Zero-extend to nw limbs (limb 0 = the u64, rest 0). Since n < 2^64 ≤ p,
      -- n mod p = n; convert to Montgomery form via montMul(n, R²) = n·R.
      let cb := (List.replicate (nw-1) (i64.const 0)).foldl (fun cb' _ => cb'.push (i64.const 0)) cb
      let cb := pushCoeff (montR2 vm.prime nw) nw |> fun instrs =>
        instrs.foldl (fun cb' i => cb'.push i) cb
      pure (cb.push (call "$fmul"))
  | .localVar i, cb => pure (pushStepVar (vm.letBase + i * vm.numWords) vm.numWords cb)
  | .listGet xs i, cb => do
    -- Read element `xs[i]` at a runtime u64 index `i`.
    -- Emit a chain of field selects: for each k, sel_k = (i == k ? xs[k] : 0),
    -- summed. (Indices outside the list read 0, matching `FExpr.eval`.)
    let nw := vm.numWords
    -- The index is captured ABOVE the shared scratch region: element
    -- subexpressions (.ite/.bit/.flt/.feq) write scratchBase..scratchBase+2nw
    -- and would clobber a captured index inside it. Nested listGet cannot
    -- reuse the single slot, so it is rejected at compile time.
    if xs.any fun e => containsListGet e then
      .error "compileFExpr: nested listGet is not supported (the index slot is shared)"
    else do
      -- Compile the index once, capture to the dedicated slot so each element can re-push it.
      let idxCB ← compileU64Expr vm i cb
      let idxLocal := vm.scratchBase + scratchReserve nw
      let captureIdx : List Instr := [local.set idxLocal]
      -- Compile each element (via the non-mutual list helper, so termination holds)
      -- and emit the select-sum chain.
      let selInstrs ← compileFExprList vm idxLocal nw 0 xs
      pure (idxCB.pushList captureIdx |>.pushList selInstrs)
  | .dataGet _ _ _ _, _ => .error "compileFExpr: dataGet is not yet supported"
  | .hintGet _ _ _ _, _ => .error "compileFExpr: hintGet is not yet supported"

def compileU64Expr (vm : VarMap) : U64Expr F → CodeBuilder → Except String CodeBuilder
  | .const n, cb => pure (cb.push (i64.const n.toNat))
  | .val x, cb =>
    -- Extracts the integer representative of a field element.
    -- For multi-word, convert from Montgomery form first (montMul(x, 1) = x),
    -- then keep only limb 0 (the lowest 64 bits of the representative).
    if vm.numWords = 1 then compileFExpr vm x cb
    else do
      let cb ← compileFExpr vm x cb
      -- fromMontgomery: montMul(x, 1) = x·R·1·R⁻¹ = x
      let cb := cb.pushList (pushCoeff 1 vm.numWords) |>.push (call "$fmul")
      -- Drop upper nw-1 limbs, keeping only limb 0 on the stack
      let drops := List.replicate (vm.numWords - 1) Instr.drop
      pure (cb.pushList drops)
  | .idx, cb =>
    -- mapRange loops are unrolled at compile time, so the index is a constant.
    match vm.loopIdx with
    | some i => pure (cb.push (i64.const i))
    | none => .error "compileU64Expr: idx used outside of a mapRange loop"
  | .localVar i, cb => pure (cb.push (local.get (vm.letBase + i * vm.numWords)))
  | .add a e, cb => do
    let cb ← compileU64Expr vm a cb; let cb ← compileU64Expr vm e cb; pure (cb.push i64.add)
  | .mul a e, cb => do
    let cb ← compileU64Expr vm a cb; let cb ← compileU64Expr vm e cb; pure (cb.push i64.mul)
  | .div a e, cb => do
    let cb ← compileU64Expr vm a cb; let cb ← compileU64Expr vm e cb; pure (cb.push (.binop .i64 .div_u))
  | .mod a e, cb => do
    let cb ← compileU64Expr vm a cb; let cb ← compileU64Expr vm e cb; pure (cb.push i64.rem_u)
  | .land a e, cb => do
    let cb ← compileU64Expr vm a cb; let cb ← compileU64Expr vm e cb; pure (cb.push i64.and)
  | .lor a e, cb => do
    let cb ← compileU64Expr vm a cb; let cb ← compileU64Expr vm e cb; pure (cb.push i64.or)
  | .lxor a e, cb => do
    let cb ← compileU64Expr vm a cb; let cb ← compileU64Expr vm e cb; pure (cb.push (.binop .i64 .xor))
  | .shiftL a e, cb => do
    let cb ← compileU64Expr vm a cb; let cb ← compileU64Expr vm e cb; pure (cb.push i64.shl)
  | .shiftR a e, cb => do
    let cb ← compileU64Expr vm a cb; let cb ← compileU64Expr vm e cb; pure (cb.push i64.shr_u)
  | .ite c t e, cb => do
    let cond ← compileBExpr vm c cb
    let thenCB ← compileU64Expr vm t {}
    let elseCB ← compileU64Expr vm e {}
    pure (cond.push (.ifElse "" (some .i64) thenCB.build elseCB.build))

/-- Conditions compile to `i32`, the native WASM boolean type.
    WASM relops on i64 operands already return i32, so no conversions are needed. -/
def compileBExpr (vm : VarMap) : BExpr F → CodeBuilder → Except String CodeBuilder
  | .true, cb => pure (cb.push (i32.const 1))
  | .false, cb => pure (cb.push (i32.const 0))
  | .feq a e, cb => do
    let nw := vm.numWords
    if nw = 1 then do
      let cb ← compileFExpr vm a cb
      let cb ← compileFExpr vm e cb
      pure (cb.push i64.eq)
    else do
      -- Multi-word: compile both operands first (both stay on the stack, `a`
      -- deepest), then capture the top operand (`e`) first and `a` second, so
      -- no nested comparison inside `e` can clobber a captured operand — the
      -- shared scratch region is only written between the captures and the reads.
      let tmpBase := vm.scratchBase
      let aCB ← compileFExpr vm a {}
      let eCB ← compileFExpr vm e {}
      -- Capture: highest limb first (reverse order matches stack top)
      let captureE : List Instr := (List.range nw).reverse.map fun w => local.set (tmpBase + w)
      let captureA : List Instr := (List.range nw).reverse.map fun w => local.set (tmpBase + nw + w)
      -- Compare pairwise: a_i vs e_i, producing i32 results (i64.eq gives i32)
      let cmpAll : List Instr := (List.range nw) >>= fun i =>
        [ local.get (tmpBase + nw + i), local.get (tmpBase + i), i64.eq ]
      -- AND-reduce the i32 comparison results
      let andAll : List Instr := (List.range (nw-1)).map fun _ => i32.and
      pure (cb.pushList aCB.build |>.pushList eCB.build |>.pushList captureE
              |>.pushList captureA |>.pushList cmpAll |>.pushList andAll)
  | .lt a e, cb => do
    let cb ← compileU64Expr vm a cb
    let cb ← compileU64Expr vm e cb
    pure (cb.push i64.lt_u)
  | .neq a e, cb => do
    -- NOTE: despite the name, `BExpr.neq` is u64 *equality* (see `BExpr.eval`).
    let cb ← compileU64Expr vm a cb
    let cb ← compileU64Expr vm e cb
    pure (cb.push i64.eq)
  | .flt a e, cb => do
    -- Field-sorted less-than over the integer representatives.
    -- For single-word: i64.lt_u works. For multi-word: convert both operands
    -- from Montgomery form (montMul(x, 1) = x — Montgomery representatives are
    -- permuted, so `<` on them is not the field-sorted order), then compare
    -- limb-wise from the highest limb down (unsigned comparison).
    let nw := vm.numWords
    if nw = 1 then do
      let cb ← compileFExpr vm a cb
      let cb ← compileFExpr vm e cb
      pure (cb.push i64.lt_u)
    else do
      -- Convert both operands from Montgomery on the stack (montMul(x, 1) = x),
      -- then capture to temp locals, compare highest limb first.
      -- Both operands are compiled before anything is captured: `e` sits on top
      -- of the stack, so it is converted and captured first, then `a`. A nested
      -- comparison inside `e` uses the shared scratch region before the outer
      -- captures are written, so it cannot clobber them.
      let tmpBase := vm.scratchBase
      let aCB ← compileFExpr vm a {}
      let eCB ← compileFExpr vm e {}
      let fromMont : List Instr := pushCoeff 1 nw ++ [call "$fmul"]
      let captureE : List Instr := (List.range nw).reverse.map fun w => local.set (tmpBase + w)
      let captureA : List Instr := (List.range nw).reverse.map fun w => local.set (tmpBase + nw + w)
      -- Multi-limb unsigned comparison, highest limb first, as nested ifElse:
      --   if a_{nw-1} < e_{nw-1} then 1
      --   else if a_{nw-1} > e_{nw-1} then 0
      --   else <recurse on lower limbs>
      -- Base case (all higher limbs equal): a_0 < e_0 ? 1 : 0.
      let rec cmpChain (i : ℕ) : List Instr :=
        if i = 0 then
          [ local.get (tmpBase + nw + 0), local.get (tmpBase + 0), i64.lt_u,
            .ifElse "" (some .i32) [i32.const 1] [i32.const 0] ]
        else
          [ local.get (tmpBase + nw + i), local.get (tmpBase + i), i64.lt_u,
            .ifElse "" (some .i32) [i32.const 1]
              ([ local.get (tmpBase + nw + i), local.get (tmpBase + i), i64.gt_u,
                 .ifElse "" (some .i32) [i32.const 0] (cmpChain (i - 1)) ]) ]
      pure (cb.pushList aCB.build |>.pushList eCB.build |>.pushList fromMont
              |>.pushList captureE |>.pushList fromMont |>.pushList captureA
              |>.pushList (cmpChain (nw - 1)))
  | .bit x i, cb => do
    -- Test bit `i` of `FiniteField.val x`: limb i/64, bit i%64 (constant i).
    -- Multi-word: convert from Montgomery first (montMul(x, 1) = x).
    let nw := vm.numWords
    let limbIdx := i / limbBits
    let bitIdx := i % limbBits
    if limbIdx ≥ nw then
      -- Bit index beyond the field width: always 0 (val < 2^(nw*64)).
      pure (cb.push (i32.const 0))
    else do
      -- Capture the field value to locals, then extract the limb and test the bit.
      let tmpBase := vm.scratchBase
      let xCB ← compileFExpr vm x {}
      let fromMont : List Instr := if nw = 1 then []
        else pushCoeff 1 nw ++ [call "$fmul"]
      let capture : List Instr := (List.range nw).reverse.map fun w => local.set (tmpBase + w)
      -- a_i & (1 << bit): if zero, the bit is not set (→ 0); else it is set (→ 1).
      -- i64.eqz gives i32 = 1 when the bit is NOT set; ifElse (result i32):
      --   then-branch (bit not set): 0, else-branch (bit set): 1
      let testInstrs : List Instr :=
        [ local.get (tmpBase + limbIdx), i64.const (2^bitIdx), i64.and, i64.eqz,
          .ifElse "" (some .i32) [i32.const 0] [i32.const 1] ]
      pure (cb.pushList xCB.build |>.pushList fromMont |>.pushList capture |>.pushList testInstrs)
  | .not x, cb => do
    let cb ← compileBExpr vm x cb
    pure (cb.push i32.eqz)
  | .and a e, cb => do
    let cb ← compileBExpr vm a cb
    let cb ← compileBExpr vm e cb
    pure (cb.push i32.and)
end

/-! ## Expression flattening (shared by WASM and R1CS compilers) -/

-- sparse (signalIndex × fieldCoefficient) pairs
def LinComb (F : Type) := List (ℕ × F)
def Constraint (F : Type) := List (ℕ × F) × List (ℕ × F) × List (ℕ × F)

structure FlattenState (F : Type) where
  nextSignal : ℕ := 1
  constraints : List (Constraint F) := []

def isConstant (lc : List (ℕ × F)) : Bool :=
  match lc with | [(0, _)] => true | _ => false

def scaleLinComb (c : F) (lc : List (ℕ × F)) : List (ℕ × F) :=
  lc.map fun (i, coeff) => (i, c * coeff)

def addLinCombs (a b : List (ℕ × F)) : List (ℕ × F) :=
  match a, b with
  | [], _ => b
  | _, [] => a
  | (i1, c1) :: xs, (i2, c2) :: ys =>
    if i1 < i2 then (i1, c1) :: addLinCombs xs ((i2, c2) :: ys)
    else if i1 = i2 then
      let s := c1 + c2
      if s = 0 then addLinCombs xs ys else (i1, s) :: addLinCombs xs ys
    else (i2, c2) :: addLinCombs ((i1, c1) :: xs) ys

open Expression (var const add mul) in
def flattenExpr (vm : VarMap) : (e : Expression F) → FlattenState F → (List (ℕ × F) × FlattenState F)
  | .var i, st =>
    -- R1CS signal = the variable's position in the outputs-first signal layout.
    ([(signalOfVar vm i.index, (1 : F))], st)
  | .const c, st => ([(0, c)], st)
  | .add a b, st =>
    let (la, st1) := flattenExpr vm a st
    let (lb, st2) := flattenExpr vm b st1
    (addLinCombs la lb, st2)
  | .mul a b, st =>
    let (la, st1) := flattenExpr vm a st
    let (lb, st2) := flattenExpr vm b st1
    if isConstant la then
      (scaleLinComb ((la.head?.getD (0,0)).2) lb, st2)
    else if isConstant lb then
      (scaleLinComb ((lb.head?.getD (0,0)).2) la, st2)
    else
      let k := st2.nextSignal
      let st3 : FlattenState F := { nextSignal := k + 1, constraints := (la, lb, [(k, (1 : F))]) :: st2.constraints }
      ([(k, (1 : F))], st3)

/-! ## AST-based witness computation helpers -/

/-- Load signal i from memory and convert to Montgomery form (multi-word).
    Signal 0 is the constant 1 — in Montgomery form that is R mod p.
    Other signals are stored in normal form in memory, so they are converted
    by montMul(x, R²). Single-word mode loads raw. -/
def loadSignal (i signalBase signalBytes numWords prime : ℕ) : List Instr :=
  let nw := numWords
  if i = 0 then
    if nw = 1 then [i64.const 1]
    else pushCoeff (montR prime nw) nw
  else
    -- Load each limb from signal memory (normal form), then convert to Montgomery
    let load : List Instr := (List.range nw) >>= fun w =>
      [ i32.const (signalBase + i * signalBytes + w * bytesPerI64), .memLoad .i64 0 alignmentI64 ]
    if nw = 1 then load
    else load ++ pushCoeff (montR2 prime nw) nw ++ [call "$fmul"]

/-- Push a field element as nw i64 limbs.
    In multi-word (Montgomery) mode the coefficient is multiplied by R mod p. -/
def pushCoeffF (c : F) (numWords prime : ℕ) : List Instr :=
  let val := if numWords = 1 then FiniteField.val c else (FiniteField.val c * montR prime numWords) % prime
  pushCoeff val numWords

/-- Evaluate a linear combination over nw-limb field elements (in Montgomery
    form). Leaves nw i64 on the stack. -/
def compileLinComb (lc : List (ℕ × F)) (signalBase signalBytes numWords prime : ℕ) : List Instr :=
  let nw := numWords
  match lc with
  | [] => List.replicate nw (i64.const 0)
  | [(0, c)] => pushCoeffF c nw prime
  | [(i, c)] => loadSignal i signalBase signalBytes nw prime ++ pushCoeffF c nw prime ++ [call "$fmul"]
  | (i1, c1) :: rest =>
    let first := if i1 = 0 then pushCoeffF c1 nw prime
      else loadSignal i1 signalBase signalBytes nw prime ++ pushCoeffF c1 nw prime ++ [call "$fmul"]
    let restInstrs : List Instr := rest >>= fun (i, c) =>
      if i = 0 then pushCoeffF c nw prime ++ [call "$fadd"]
      else loadSignal i signalBase signalBytes nw prime ++ pushCoeffF c nw prime ++ [call "$fmul", call "$fadd"]
    first ++ restInstrs

/--
Discover intermediate signals from assert expressions and compile to instructions.
`intLocalBase` is the starting local index for intermediate locals in the calling function.
Returns (numIntermediates, local declarations, computation instructions).
-/
def discoverAndCompileIntermediates (vm : VarMap) (flatOps : List (FlatOperation F))
    (startSignal signalBase signalBytes numWords intLocalBase : ℕ) : ℕ × List (String × ValType) × List Instr :=
  let nw := numWords
  let (st, _) := flatOps.foldl (fun (acc : FlattenState F × Unit) (op : FlatOperation F) =>
    match op with
    | .assert e =>
      let (_, st') := flattenExpr vm e acc.1
      (st', ())
    | _ => acc
  ) (({ nextSignal := startSignal, constraints := [] } : FlattenState F), ())
  let numInt := st.nextSignal - startSignal
  let intConstraintsRev := List.reverse st.constraints
  let rec buildAST (idx : ℕ) (instrs : List Instr) (locals : List (String × ValType))
      (remaining : List (Constraint F)) : ℕ × List (String × ValType) × List Instr :=
    match remaining with
    | [] => (idx, locals, instrs)
    | (la, lb, [(k, _)]) :: rest =>
      let laInstrs := compileLinComb la signalBase signalBytes nw vm.prime
      let lbInstrs := compileLinComb lb signalBase signalBytes nw vm.prime
      -- Each intermediate uses nw consecutive locals
      let base := intLocalBase + idx * nw
      let captureAll : List Instr := (List.range nw).reverse.map fun w => local.set (base + w)
      -- Convert from Montgomery form back to normal form before storing
      -- (memory holds normal form; snarkjs reads it directly).
      -- montMul(mont(x), 1) = x·R·1·R⁻¹ = x. Single-word mode needs no conversion.
      let fromMont : List Instr := if nw = 1 then []
        else ((List.range nw) >>= fun w => [ local.get (base + w) ])
             ++ pushCoeff 1 nw ++ [call "$fmul"]
      let captureFromMont : List Instr := if nw = 1 then []
        else (List.range nw).reverse.map fun w => local.set (base + w)
      let storeAll : List Instr := (List.range nw) >>= fun w =>
        [ i32.const (signalBase + k * signalBytes + w * bytesPerI64),
          local.get (base + w), .memStore .i64 0 alignmentI64 ]
      let localNames : List (String × ValType) :=
        (List.range nw).map fun w => (s!"$int_{idx}_{w}", .i64)
      let computeInstrs : List Instr :=
        laInstrs ++ lbInstrs ++ [call "$fmul"] ++ captureAll
        ++ fromMont ++ captureFromMont ++ storeAll
      buildAST (idx + 1) (computeInstrs ++ instrs) (localNames ++ locals) rest
    | _ :: rest => buildAST idx instrs locals rest
  let (_, locals, instrs) := buildAST 0 [] [] intConstraintsRev
  (numInt, locals.reverse, instrs)

/-- compile let-steps (letF/letN) to instructions.
    Steps are allocated in the dedicated step region at `vm.stepNext` (direct
    WASM local allocation, NOT through `vm.alloc` — they are not circuit
    variables and must not advance `nextLocal`).
    Sets `letBase` to the first step's WASM local index.
    Returns the updated VarMap (its `stepNext` advanced past the step slots).
    Step-expression scratch uses the shared `vm.scratchBase`, so steps allocate
    only their own `nw`-limb slots. -/
def compileSteps (vm : VarMap) (steps : List (Step F)) :
    Except String (VarMap × CodeBuilder) := do
  let nw := vm.numWords
  -- Steps live in their own local region (see the `VarMap` doc comment), so
  -- they never disturb the `i * numWords` witness layout.
  let stepBase := vm.stepNext
  let vmInit : VarMap := steps.foldl (fun v _ =>
    { v with stepNext := v.stepNext + nw, letBase := stepBase }) vm
  let vmB := { vmInit with letBase := stepBase }
  let (vmF, _, acc) ← steps.foldlM (fun ((vm, idx, acc) : VarMap × ℕ × CodeBuilder) step => do
    let wasmBase := stepBase + idx * nw
    let locs := List.range nw |>.map fun w => wasmBase + w
    match step with
    | .letF e =>
      let cb ← compileFExpr vm e {}
      -- Capture all nw limbs: the stack has limb₀ deepest, so `.reverse`
      -- stores limbᵢ at `wasmBase + i` (pops the highest limb first).
      pure (vm, idx + 1, acc.pushList (cb.build ++ (locs.reverse.map fun w => local.set w)))
    | .letU e =>
      let cb ← compileU64Expr vm e {}
      -- A u64 is a single i64: store it in the low limb and zero the rest.
      let capture := match locs with
        | [] => []
        | base :: highs => local.set base :: (highs >>= fun idx' => [i64.const 0, local.set idx'])
      pure (vm, idx + 1, acc.pushList (cb.build ++ capture))
  ) (vmB, 0, {})
  pure (vmF, acc)

/-- compile a list of FExpr literals to instructions.
    Expression scratch uses the shared `vm.scratchBase`; each output slot is
    just `nw` locals allocated contiguously. -/
def compileLit (vm : VarMap) (vi : ℕ) (acc : CodeBuilder) (es : List (FExpr F)) :
    Except String (VarMap × ℕ × CodeBuilder) :=
  es.foldlM (fun ((vm, vi, acc) : VarMap × ℕ × CodeBuilder) (e : FExpr F) => do
    let cb ← compileFExpr vm e {}
    let (vm', locs) := vm.alloc 1
    pure (vm', vi + 1, acc.pushList (cb.build ++ (locs.reverse.map fun idx => local.set idx)))
  ) (vm, vi, acc)

/-- compile a VExpr to instructions. -/
def compileVExpr (vm : VarMap) (vi : ℕ) (acc : CodeBuilder) :
    {m : ℕ} → VExpr F m → Except String (VarMap × ℕ × CodeBuilder)
  | _, .lit es => compileLit vm vi acc es.toList
  | _, .mapRange n body => do
    let nw := vm.numWords
    let (vmOut, _) := vm.alloc n
    let outBase := vmOut.nextLocal - n * nw
    let instrs ← (List.range n).foldlM (fun (acc : CodeBuilder) (i : ℕ) => do
      -- The loop is unrolled at compile time; `idx` in the body is the constant `i`.
      -- Body scratch uses the shared `vm.scratchBase`.
      let cb ← compileFExpr { vmOut with loopIdx := some i } body {}
      -- Capture all nw limbs of element i: the stack has limb₀ deepest, so
      -- `.reverse` stores limbᵢ at `elemBase + i` (pops the highest limb first).
      let elemBase := outBase + i * nw
      let capture := (List.range nw).reverse.map fun w => local.set (elemBase + w)
      pure (acc.pushList (cb.build ++ capture))
    ) acc
    pure (vmOut, vi + n, instrs)
  | n, .envRange offset => do
    -- `n` consecutive environment cells at `offset + i`, witnessed as fresh outputs.
    -- During witness generation the environment cells are inputs and earlier
    -- witnesses, which live in WASM locals — so each cell is a `local.get` via
    -- `vm.lookup`, captured into the new witness slot.
    let nw := vm.numWords
    let (vmOut, _) := vm.alloc n
    let outBase := vmOut.nextLocal - n * nw
    let instrs := (List.range n).foldl (fun (acc : CodeBuilder) (i : ℕ) =>
      let elemBase := outBase + i * nw
      let srcBase := vm.lookup (offset + i)
      let load : List Instr := (List.range nw) >>= fun w => [ local.get (srcBase + w) ]
      let capture := (List.range nw).reverse.map fun w => local.set (elemBase + w)
      acc.pushList (load ++ capture)
    ) acc
    pure (vmOut, vi + n, instrs)
  | n, .bitsOf x => do
    -- The `n` low bits of `FiniteField.val x`, each as field 0 or 1.
    -- Compile `x` ONCE into the shared scratch region, then per-bit tests
    -- read from it (the region is above all output slots, so the per-bit
    -- tests never overwrite earlier outputs).
    let nw := vm.numWords
    let (vmOut, _) := vm.alloc n
    let outBase := vmOut.nextLocal - n * nw
    -- Multi-word: convert from Montgomery first (montMul(x, 1) = x).
    let xCB ← compileFExpr vm x {}
    let fromMont : List Instr := if nw = 1 then []
      else pushCoeff 1 nw ++ [call "$fmul"]
    let scratchBase := vm.scratchBase
    let captureX : List Instr := (List.range nw).reverse.map fun w => local.set (scratchBase + w)
    let instrs ← (List.range n).foldlM (fun (acc : CodeBuilder) (i : ℕ) => do
      let limbIdx := i / limbBits
      let bitIdx := i % limbBits
      let elemBase := outBase + i * nw
      -- Bit i of the field representative: limb i/limbBits, bit i%limbBits (constant i).
      -- Bits beyond the field width are always 0.
      let testInstrs : List Instr := if limbIdx ≥ nw then
          [i32.const 0]
        else
          [ local.get (scratchBase + limbIdx), i64.const (2^bitIdx), i64.and, i64.eqz,
            .ifElse "" (some .i32) [i32.const 0] [i32.const 1] ]
      -- testInstrs leaves i32 (0/1); zero-extend to i64 then to nw limbs
      let extend : List Instr := [i64.extend_i32_u] ++ List.replicate (nw - 1) (i64.const 0)
      let capture := (List.range nw).reverse.map fun w => local.set (elemBase + w)
      pure (acc.pushList (testInstrs ++ extend ++ capture))
    ) (acc.pushList (xCB.build ++ fromMont ++ captureX))
    pure (vmOut, vi + n, instrs)
  | _, .append a b => do
    -- Compile first segment (produces m elements at vi..vi+m-1),
    -- then second segment (produces n elements at vi+m..vi+m+n-1).
    let (vm', vi', instrs') ← compileVExpr vm vi acc a
    compileVExpr vm' vi' instrs' b

/-- process flat operations, accumulating instructions.
    `vi` tracks the next circuit-variable index (input count + sum of witness sizes).
    This is NOT advanced by let-steps, which live in a separate local-index space. -/
def processFlatOps :
    List (FlatOperation F) → VarMap → ℕ → CodeBuilder → Except String (VarMap × ℕ × CodeBuilder)
  | [], vm, finalVarIdx, acc => pure (vm, finalVarIdx, acc)
  | .witness _ (.ir steps vexpr) :: rest, vm, vi, acc => do
    let (vmS, stepCB) ← compileSteps vm steps
    let (vmOut, viOut, outCB) ← compileVExpr vmS vi stepCB vexpr
    processFlatOps rest vmOut viOut (acc.pushList outCB.build)
  | .witness _ (.native _) :: _, _, _, _ =>
    .error "processFlatOps: cannot compile a `native` witness (arbitrary Lean closure); rewrite it as structured witness IR"
  | .assert _ :: rest, vm, vi, acc =>
    -- Asserts allocate no witnesses and need no code here; intermediate signals
    -- they induce are compiled separately by `discoverAndCompileIntermediates`.
    processFlatOps rest vm vi acc
  | .lookup _ :: rest, vm, vi, acc =>
    -- Lookups constrain existing values and allocate no witnesses,
    -- so witness generation ignores them.
    processFlatOps rest vm vi acc
  | .interact _ :: rest, vm, vi, acc =>
    -- Interactions constrain values through channels but allocate no witnesses,
    -- so witness generation ignores them (like lookups).
    processFlatOps rest vm vi acc

/-- Compile to a WASM binary module (LEB128-encoded WASM).
    `numWords` must be at least `ceil(bitLength(fieldPrime) / limbBits)`, and
    `numWords = 1` additionally requires `fieldPrime ≤ 2^32` so that products
    of two field elements fit in an i64 before modular reduction.
    `inputNames` enables strict snarkjs input validation: when non-empty (one
    name per input) the module matches the FNV-1a hash of each input.json key
    and rejects unknown keys, like circom. When empty, any key is accepted
    (the value array must hold all `numInputs` elements).
    `outputVarIdx` (circuit-variable indices of the outputs) switches the
    signal layout to outputs-first — signal 0 = constant, 1..nOutputs = the
    outputs, then inputs, then remaining witnesses — so snarkjs's public
    signals match the circuit's real outputs. Empty keeps the plain layout.
    Returns an error for inputs the compiler does not support. -/
def compileModule (fieldPrime numInputs : ℕ) (inputNames : List String := []) (outputVarIdx : List ℕ := []) (ops : List (Operation F)) (numWords : ℕ) :
    Except String ByteArray := do
  let nw := numWords
  -- Validate that numWords is sufficient for the prime.
  -- For single-word (nw=1), the prime must satisfy (p-1)^2 < 2^64
  -- to avoid i64.mul overflow, i.e., p <= 2^32.
  let primeBits := Nat.log2 fieldPrime + 1
  let minWords := (primeBits + limbBits - 1) / limbBits
  if nw = 1 ∧ fieldPrime > singleWordPrimeMax then
    throw s!"compileModule: numWords=1 requires a prime <= 2^32 to avoid i64.mul overflow; got a {primeBits}-bit prime, use numWords = {max minWords minMultiWordWords}"
  if nw * limbBits < primeBits then
    throw s!"compileModule: numWords={nw} is insufficient for a {primeBits}-bit prime; need at least {minWords} words"
  if !inputNames.isEmpty ∧ inputNames.length ≠ numInputs then
    throw s!"compileModule: {inputNames.length} input names for {numInputs} inputs (either none, or one per input)"
  if outputVarIdx.length ≠ outputVarIdx.eraseDups.length then
    throw "compileModule: outputVarIdx must not contain duplicate variables"
  if !(outputVarIdx.all fun v => v ≥ numInputs) then
    throw "compileModule: outputVarIdx must be witness circuit variables (indices ≥ numInputs)"
  let numOutputs := outputVarIdx.length
  let flatOps := Operations.toFlat ops
  -- Pre-pass: count the total witness slots (per flat op) and the TOTAL
  -- number of let-steps across all ops. The witness region spans
  -- `[numInputs*nw, witnessEnd)`; the step region `[witnessEnd, stepEnd)`
  -- above it is where compileSteps allocates cumulatively (never reused), so
  -- the sum — not the max — determines how far the locals extend; the SHARED
  -- scratch region must sit above all witness and step locals or later
  -- outputs land inside it.
  let (witnessTotal, stepTotal) := flatOps.foldl
    (fun ((w, s) : ℕ × ℕ) (op : FlatOperation F) =>
      match op with
      | .witness m (.ir steps _) => (w + m, s + steps.length)
      | .witness m (.native _) => (w + m, s)
      | _ => (w, s))
    (0, 0)
  let witnessEnd := numInputs * nw + witnessTotal * nw
  let stepEnd := witnessEnd + stepTotal * nw
  -- vi starts at numInputs so that circuit variable indices (which start at 0 for
  -- inputs) align with the VarMap layout (variable i lives at local i * numWords),
  -- and pushVar uses the circuit variable index from the witness IR directly.
  let baseVm : VarMap := VarMap.init numInputs nw fieldPrime
  let vm := { baseVm with stepNext := witnessEnd, scratchBase := stepEnd, numOutputs := numOutputs, outputVars := outputVarIdx }
  let (finalVm, finalVarIdx, bodyCB) ← processFlatOps flatOps vm numInputs {}
  -- finalVarIdx = numInputs + total witness outputs (steps don't count)
  let witnessCount := finalVarIdx - numInputs
  if !(outputVarIdx.all fun v => v < finalVarIdx) then
    throw "compileModule: outputVarIdx contains a variable outside the witness range"
  let n32 := nw * i32PerLimb
  let srwmBase := srwmBaseAddress
  -- Signal array must be 8-byte aligned for i64.store/i64.load
  let signalBaseRaw := srwmBaseAddress + n32 * bytesPerI32
  let signalBase := ((signalBaseRaw + bytesPerI64 - 1) / bytesPerI64) * bytesPerI64
  let signalBytes := n32 * bytesPerI32
  let startSignal := 1 + numInputs + witnessCount  -- signal 0 = constant 1, then inputs, then witnesses
  -- Local index base for intermediates in getWitness: param $i(0), $tmp(1), $idx(2), $in_*(3..)
  -- For multi-word, each input has nw limbs; locals are $in_{i}_{w}
  -- Each intermediate uses nw consecutive locals
  let intLocalBase := getWitnessFixedLocals + numInputs * nw
  let (numInt, intLocals, intCode) :=
    discoverAndCompileIntermediates vm flatOps startSignal signalBase signalBytes nw intLocalBase
  let totalSignals := startSignal + numInt
  -- Build witness output stores: write each 64-bit limb to signal memory.
  -- Witness values are in Montgomery form in locals; convert back to normal
  -- form (montMul(x, 1) = x) before storing, since memory/snarkjs use normal form.
  let outputStores : List Instr := (List.range witnessCount) >>= fun i =>
    let elemIdx := numInputs + i  -- circuit variable index of this witness
    let wasmBase := finalVm.lookup elemIdx
    -- Each witness is stored at its outputs-first signal position.
    let signalIdx := signalOfVar finalVm elemIdx
    if nw = 1 then
      (List.range nw) >>= fun w =>
        [ i32.const (signalBase + signalIdx * signalBytes + w * bytesPerI64),
          local.get (wasmBase + w),
          .memStore .i64 0 alignmentI64 ]
    else
      -- Push the value (limb 0 deepest), multiply by 1 to leave Montgomery form
      -- (montMul(x, 1) = x), capture result limbs to the shared scratch block,
      -- then store. Capture order: after $fmul the stack has limb0 deepest,
      -- so popping top-first (reverse) stores limb w at tmpBase+w.
      let tmpBase := finalVm.scratchBase
      let pushVal := (List.range nw) >>= fun w => [ local.get (wasmBase + w) ]
      let convert := pushCoeff 1 nw ++ [call "$fmul"]
      let capture := (List.range nw).reverse.map fun w => local.set (tmpBase + w)
      let storeAll := (List.range nw) >>= fun w =>
        [ i32.const (signalBase + signalIdx * signalBytes + w * bytesPerI64),
          local.get (tmpBase + w), .memStore .i64 0 alignmentI64 ]
      pushVal ++ convert ++ capture ++ storeAll
  -- Build the compute function
  let inputParams := (List.range numInputs) >>= fun i =>
    (List.range nw).map fun w => (s!"$in_{i}_{w}", .i64)
  let computeFunc : Func := {
    name := "$compute"
    params := inputParams
    -- The tail of the scratch region is used by outputStores for the
    -- from-Montgomery conversion of each witness before storing, and one
    -- extra slot above it holds the runtime `listGet` index.
    -- Declare locals up to the end of the shared scratch region plus the
    -- index slot (scratchBase + scratchReserve nw + listGetIdxSlots),
    -- minus the params (numInputs*nw).
    locals := (List.replicate (finalVm.scratchBase + scratchReserve nw + listGetIdxSlots - numInputs*nw) ("", .i64)) ++ [("$idx", .i64)]
    body := bodyCB.build ++ outputStores
  }
  -- Build getWitness body
  let gwInputLocals : List (String × ValType) :=
    (List.range numInputs) >>= fun i =>
      (List.range nw).map fun w => (s!"$in_{i}_{w}", ValType.i64)
  -- Input loads: for each input i and limb w, read i64 from signal memory
  -- (normal form), then convert to Montgomery form (montMul(x, R²) = x·R)
  -- for the multi-word compute function.
  let inputLoads : List Instr := (List.range numInputs) >>= fun i =>
    -- Inputs sit after the outputs in the outputs-first signal layout.
    let loadAll := (List.range nw) >>= fun w =>
      [ i32.const (signalBase + (1 + numOutputs + i) * signalBytes + w * bytesPerI64),
        .memLoad .i64 0 alignmentI64,
        local.set (getWitnessFixedLocals + i * nw + w) ]
    let convert := if nw = 1 then []
      else ((List.range nw) >>= fun w => [ local.get (getWitnessFixedLocals + i * nw + w) ])
           ++ pushCoeff (montR2 fieldPrime nw) nw ++ [call "$fmul"]
    let capture := if nw = 1 then [] else (List.range nw).reverse.map fun w => local.set (getWitnessFixedLocals + i * nw + w)
    loadAll ++ convert ++ capture
  -- Input push: push all nw limbs per input
  let inputPush : List Instr := (List.range numInputs) >>= fun i =>
    (List.range nw) >>= fun w =>
      [ local.get (getWitnessFixedLocals + i * nw + w) ]
  -- Tail: copy all n32 32-bit words of signal $i to SRWM[0..n32-1].
  let gwTail : List Instr := (List.range n32) >>= fun w =>
    [ i32.const (srwmBase + w * bytesPerI32),
      i32.const signalBase, local.get 0, i32.const signalBytes, .binop .i32 .mul, .binop .i32 .add,
      i32.const (w * bytesPerI32), .binop .i32 .add,
      i32.load 0,
      .memStore .i32 0 alignmentI32 ]
  -- Build the getWitness function body
  let gwBody : List Instr :=
    [ i32.const computedFlagAddr, i32.load 0, i32.eqz ]  -- check computed flag
    ++ [ if_ none
          (inputLoads ++ inputPush ++ [call "$compute"] ++ intCode
           ++ [ i32.const signalBase, i32.const constSignalValue, i32.store 0,  -- signal 0 = constant 1
                i32.const computedFlagAddr, i32.const computedFlagSet, i32.store 0 ])  -- set computed flag
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
        [ i32.const (srwmBase + w * bytesPerI32), i32.const ((fieldPrime >>> (w * hiWordShift)) % (2^hiWordShift)), .memStore .i32 0 alignmentI32 ] },
    { name := "$readSharedRWMemory"
      exportName := some "readSharedRWMemory"
      params := [("", .i32)]
      results := [.i32]
      body := [ i32.const srwmBase, local.get 0, i32.const bytesPerI32,
                .binop .i32 .mul, .binop .i32 .add, .memLoad .i32 0 alignmentI32 ] },
    { name := "$writeSharedRWMemory"
      exportName := some "writeSharedRWMemory"
      params := [("$j", .i32), ("$v", .i32)]
      body := [ i32.const srwmBase, local.get 0, i32.const bytesPerI32,
                .binop .i32 .mul, .binop .i32 .add, local.get 1, .memStore .i32 0 alignmentI32 ] },
    { name := "$getInputSignalSize"
      exportName := some "getInputSignalSize"
      params := [("", .i32), ("", .i32)]
      results := [.i32]
      -- Strict mode (inputNames provided): match the FNV-1a hash of each input
      -- name; every named input holds 1 field element. An unknown key returns
      -- -1, so snarkjs errors "Signal not found" (like circom).
      -- Lenient mode (no names): return numInputs for any key — the value
      -- count of a single key holding all inputs.
      body := if inputNames.isEmpty then [i32.const numInputs]
        else List.foldr (fun (hmsb, hlsb) acc =>
          [local.get 0, i32.const hmsb, i32.eq, local.get 1, i32.const hlsb, i32.eq, i32.and,
           .ifElse "" (some .i32) [i32.const 1] acc])
          [i32.const signalNotFound]
          (inputNames.map fun n => let h := fnv1a64 n; (h >>> 32, h % 2^32)) },
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
      locals := [("$addr", .i32)]
      -- The Circom 2 ABI calls setInputSignal(hMSB, hLSB, i) once per FIELD
      -- ELEMENT i (not per limb). snarkjs writes the value to SRWM via
      --   writeSharedRWMemory(j, arrFr[n32-1-j])
      -- where toArray32 produces MOST-significant word first (res.unshift),
      -- so SRWM word j = the j-th least significant word of the value, i.e.
      -- SRWM is LSW-first. Limb w (bits 64w..64w+63) = SRWM[2w] | SRWM[2w+1]<<32.
      -- The input's signal address is resolved into $addr, then all nw limbs
      -- are stored there. Strict mode: match the FNV-1a hash of the input name
      -- (trap on an unknown hash — snarkjs never sends one after the size
      -- check). Lenient mode: element index $idx selects the input directly.
      -- The input slot sits after the outputs in the outputs-first layout.
      body :=
        let addrIdx : ℕ := 3  -- first local after the three params
        let storeLimbs : List Instr := (List.range nw) >>= fun w =>
          [ local.get addrIdx, i32.const (w * bytesPerI64), .binop .i32 .add,
            i32.const (srwmBase + 2*w*bytesPerI32), .memLoad .i32 0 alignmentI32, .unop .i64 .extend_i32_u,
            i32.const (srwmBase + (2*w+1)*bytesPerI32), .memLoad .i32 0 alignmentI32, .unop .i64 .extend_i32_u,
            i64.const hiWordShift, i64.shl, i64.or,
            .memStore .i64 0 alignmentI64 ]
        if inputNames.isEmpty then
          [ i32.const (signalBase + (1 + numOutputs) * signalBytes),
            local.get 2, i32.const signalBytes, .binop .i32 .mul, .binop .i32 .add,
            local.set addrIdx ] ++ storeLimbs
        else
          let addrChain := (List.zip (List.range inputNames.length) inputNames).foldr (fun (j, n) acc =>
            let h := fnv1a64 n
            [local.get 0, i32.const (h >>> 32), i32.eq, local.get 1, i32.const (h % 2^32), i32.eq, i32.and,
             .ifElse "" (some .i32) [i32.const (signalBase + (1 + numOutputs + j) * signalBytes)] acc])
            [.unreachable]
          (addrChain ++ [local.set addrIdx]) ++ storeLimbs
    },
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
      body := [i32.const snarkjsProtocolVersion] },
    { name := "$getMinorVersion"
      exportName := some "getMinorVersion"
      results := [.i32]
      body := [i32.const snarkjsMinorVersion] },
    { name := "$getPatchVersion"
      exportName := some "getPatchVersion"
      results := [.i32]
      body := [i32.const snarkjsPatchVersion] },
    { name := "$init"
      exportName := some "init"
      params := [("", .i32)]
      body := [ i32.const computedFlagAddr, i32.const 0, .memStore .i32 0 alignmentI32,  -- clear computed flag
                i32.const signalBase, i32.const constSignalValue, .memStore .i32 0 alignmentI32 ] }  -- signal 0 = constant 1
  ]
  -- Arithmetic helpers
  let arithFuncs := if nw == 1 then genSingleWordArith fieldPrime
    else genMultiWordArith fieldPrime nw
  -- Assemble module. Compute required memory pages for the signal array.
  let signalInit : List ℕ := 1 :: (List.replicate (signalBytes - 1) 0)
  let memNeeded := signalBase + totalSignals * signalBytes
  let memPages := (memNeeded + wasmPageMask) / wasmPageSize  -- ceil division
  -- The Circom 2 ABI's `witness()` takes no arguments (inputs live in memory
  -- after setInputSignal); it runs the same compute path as getWitness's
  -- recompute branch. (circom_runtime never calls it — generation is driven by
  -- init + setInputSignal + getWitness — but keep the export ABI-correct.)
  let witnessFunc : Func := {
    name := "$witness"
    exportName := some "witness"
    params := []
    results := []
    -- Keep the local layout identical to getWitness (which has the `$i` param
    -- at index 0): a dummy slot at 0, then $tmp(1), $idx(2), inputs, ints —
    -- inputLoads/inputPush index them via getWitnessFixedLocals.
    locals := [("", ValType.i32), ("$tmp", ValType.i32), ("$idx", ValType.i64)] ++ gwInputLocals ++ intLocals
    body := inputLoads ++ inputPush ++ [call "$compute"] ++ intCode
      ++ [ i32.const signalBase, i32.const constSignalValue, i32.store 0,
           i32.const computedFlagAddr, i32.const computedFlagSet, i32.store 0 ]
  }
  let module : Ast.Module := {
    memoryPages := memPages
    dataSegments := [(signalBase, signalInit)]
    funcs := arithFuncs ++ [computeFunc, witnessFunc] ++ abiFuncs
  }
  Binary.Module.toBinary module
