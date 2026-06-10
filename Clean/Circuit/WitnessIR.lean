import Clean.Circuit.Expression
import Clean.Utils.Field
import Clean.Utils.FiniteField
import Clean.Utils.Vector

/-!
# Witness-generation IR (phase 1 sketch)

A deep-embedded IR for witness-generation callbacks, replacing shallow Lean closures
`ProverEnvironment F → Vector F m`. Goal: witgen becomes serializable data that Rust
proving backends can interpret or compile, mirroring how constraints already export
(see `doc/witgen-ir-plan.md` and `doc/witgen-ir-requirements.md`).

## Design

A witness program (`WitgenIR F m`) is either
- `native f` — an arbitrary Lean closure, the migration escape hatch. Not serializable.
  `eval (native f) = f` holds definitionally, which is what lets phase 2 wrap all
  existing callbacks without touching any gadget or proof.
- `prog steps out` — straight-line code: a list of scalar `let`-steps (for sharing,
  e.g. the 32-bit sum in SHA256 `Add32` that all output bits reference), followed by a
  vector-shaped output expression.

Scalar expressions come in two sorts, reflecting the codebase's pervasive
`field → ZMod.val → Nat ops → cast → field` pattern (requirements B.4/B.5, risk E.1):
- `FExpr` — field-sorted: embedded circuit `Expression`s (which is how callbacks read
  inputs and earlier witnesses), env reads at computed indices, arithmetic, inverse
  (IsZeroField), conditionals, constant-table reads, prover-data/hint reads.
- `NExpr` — Nat-sorted: arithmetic, div/mod, bitwise ops, shifts; bridges are
  `NExpr.val : FExpr → NExpr` and `FExpr.ofNat : NExpr → FExpr`.
- `BExpr` — conditions: field equality and Nat comparison (requirement B.7).

The output is a `VExpr`: a literal list, a `mapRange n body` (body may reference the
running index via `NExpr.idx`) — kept as a *loop* rather than unrolled, per the
PR #401 lessons — or an append.

## Requirements mapping (doc/witgen-ir-requirements.md, sections B/C)

- B.1 env reads ............ `FExpr.expr` (embeds `Expression F`), `FExpr.envGet`
- B.2 field arithmetic ..... `FExpr.add/mul/const` (+ `sub/neg` smart constructors)
- B.3 field inversion ...... `FExpr.inv`
- B.4 val/cast round trip .. `NExpr.val`, `FExpr.ofNat` (via `FiniteField.val`/`fromNat`,
                             so the bridge is also correct on binary fields)
- B.5 Nat-domain ops ....... `NExpr.add/mul/div/mod/land/lor/lxor/shiftL/shiftR`
                             (`2^k` = `shiftL 1 k`, `testBit i` = `shiftR · i % 2`)
- B.6 vector construction .. `VExpr.lit/mapRange/append` (`set`/`rotate` from the
                             requirements appear only in circuit-level composition of
                             expression vectors, not inside callbacks — not needed here)
- B.7 conditionals ......... `FExpr.ite`/`NExpr.ite` over `BExpr`
- B.8 let-bindings ......... `Step.letF/letN` + `localVar` references
- B.9 struct packing ....... authoring-layer concern: structs flatten to `VExpr.lit`
                             in `ProvableType.toElements` order (phase 4/5)
- B.10 constant tables ..... `FExpr.arrGet` (getD-0 semantics)
- C.1 inverse intrinsic .... first-class as `FExpr.inv`
- C.3 hint nondeterminism .. `FExpr.dataGet`/`FExpr.hintGet`, keyed like `ProverData`

## Open design questions (for review)

1. **(resolved)** Evaluating `NExpr.val` needs `F → ℕ`. We use the existing
   `FiniteField` class (issue #154), whose canonical `val : F → ℕ` embedding is designed
   to cover both prime fields (`ZMod.val`) and binary fields `GF(2^n)`. `eval` requires
   only `[FiniteField F]`: field equality in `BExpr.feq` is decided via `val` using
   `val_injective`, so no separate `[DecidableEq F]` is needed. The class gained a
   `fromNat` inverse of `val` (= `Nat.cast` on prime fields) so that the Nat→F bridge
   is also meaningful on binary fields, where `Nat.cast` collapses mod 2. Phase 2 threads
   `FiniteField` through the witgen-touching parts of core — fine per review, since
   Clean only ever targets finite fields and `FiniteField` was meant for gadgets anyway.
2. **One index binder.** `NExpr.idx` refers to the innermost enclosing `VExpr.mapRange`;
   nesting shadows. No surveyed gadget nests mapRanges inside a single callback. If that
   changes, `idx` generalizes to de Bruijn levels.
3. **Untyped locals.** `localVar i` is resolved in an `F ⊕ ℕ` array with a 0 default on
   sort mismatch / out of range, keeping `eval` total without intrinsically-typed
   syntax. A decidable well-sortedness check can be layered on top later (it will be
   needed for serialization anyway).
4. **General intrinsic registry deferred.** The surveyed gadgets need exactly two
   nondeterministic primitives (`dataGet`, `hintGet`), so those are built in. A general
   named-intrinsic registry (sorts, decompositions as opaque ops) is deferred to the
   export phase; until then `native` covers anything unusual.
-/

variable {F : Type}

namespace Witgen

mutual

/-- Field-sorted witness expressions. -/
inductive FExpr (F : Type) where
  /-- Embedded circuit expression; this is how callbacks read input vars and earlier
  witnesses (`env x`). -/
  | expr (e : Expression F)
  /-- Read the environment at a computed index (e.g. consecutive vars in a mapRange). -/
  | envGet (i : NExpr F)
  | const (c : F)
  /-- Reference to an earlier `Step` result (must be a `letF` step). -/
  | localVar (i : ℕ)
  | add (x y : FExpr F)
  | mul (x y : FExpr F)
  /-- Field inverse, with `0⁻¹ = 0` (the `IsZeroField` witness). -/
  | inv (x : FExpr F)
  /-- Cast from the Nat sort via `FiniteField.fromNat` (the inverse of `val`;
  equals `Nat.cast` on prime fields, but interprets binary digits as coefficients
  on binary fields, where `Nat.cast` would collapse via the characteristic). -/
  | ofNat (n : NExpr F)
  | ite (c : BExpr F) (t e : FExpr F)
  /-- Read a constant table at a computed index, 0 if out of range
  (FemtoCairo program, SHA/Poseidon round constants when dynamically indexed). -/
  | arrGet (xs : Array F) (i : NExpr F)
  /-- Read committed prover data (`Environment.data`), keyed like `ProverData`:
  row `row` of table `key` with rows of width `n`, projected at column `col`.
  Missing rows read as 0. The nondeterministic escape hatch (FemtoCairo memory). -/
  | dataGet (key : String) (n : ℕ) (row : NExpr F) (col : Fin n)
  /-- Same as `dataGet` but reads the uncommitted `ProverEnvironment.hint`. -/
  | hintGet (key : String) (n : ℕ) (row : NExpr F) (col : Fin n)

/-- Nat-sorted witness expressions. -/
inductive NExpr (F : Type) where
  | const (n : ℕ)
  /-- The field→Nat bridge (`ZMod.val`). -/
  | val (x : FExpr F)
  /-- The index of the innermost enclosing `VExpr.mapRange` (0 outside). -/
  | idx
  /-- Reference to an earlier `Step` result (must be a `letN` step). -/
  | localVar (i : ℕ)
  | add (x y : NExpr F)
  | mul (x y : NExpr F)
  | div (x y : NExpr F)
  | mod (x y : NExpr F)
  | land (x y : NExpr F)
  | lor (x y : NExpr F)
  | lxor (x y : NExpr F)
  | shiftL (x y : NExpr F)
  | shiftR (x y : NExpr F)
  | ite (c : BExpr F) (t e : NExpr F)

/-- Conditions. -/
inductive BExpr (F : Type) where
  | feq (x y : FExpr F)
  | lt (x y : NExpr F)
  | not (b : BExpr F)

end

/-- `x - y` as a derived field expression. -/
@[reducible] def FExpr.sub [Field F] (x y : FExpr F) : FExpr F := .add x (.mul (.const (-1)) y)

/-- `-x` as a derived field expression. -/
@[reducible] def FExpr.neg [Field F] (x : FExpr F) : FExpr F := .mul (.const (-1)) x

/-- `2^k` as a derived Nat expression. -/
@[reducible] def NExpr.pow2 (k : NExpr F) : NExpr F := .shiftL (.const 1) k

/-- `Nat.testBit x i` as a derived Nat expression, valued in {0, 1}. -/
@[reducible] def NExpr.testBit (x i : NExpr F) : NExpr F := .mod (.shiftR x i) (.const 2)

/-- Evaluation context: the prover environment, the values of the `let`-steps computed
so far, and the innermost `mapRange` index. -/
structure Ctx (F : Type) where
  env : ProverEnvironment F
  locals : Array (F ⊕ ℕ) := #[]
  idx : ℕ := 0

section Eval
variable [FiniteField F]

mutual

@[circuit_norm]
def FExpr.eval (ctx : Ctx F) : FExpr F → F
  | .expr e => e.eval ctx.env.toEnvironment
  | .envGet i => ctx.env.get (i.eval ctx)
  | .const c => c
  | .localVar i =>
    match ctx.locals[i]? with
    | some (.inl x) => x
    | _ => 0
  | .add x y => x.eval ctx + y.eval ctx
  | .mul x y => x.eval ctx * y.eval ctx
  | .inv x => (x.eval ctx)⁻¹
  | .ofNat n => FiniteField.fromNat (n.eval ctx)
  | .ite c t e => if c.eval ctx then t.eval ctx else e.eval ctx
  | .arrGet xs i => xs[i.eval ctx]?.getD 0
  | .dataGet key n row col =>
    ((ctx.env.data key n)[row.eval ctx]?.getD (.replicate n 0))[col.val]'col.isLt
  | .hintGet key n row col =>
    ((ctx.env.hint key n)[row.eval ctx]?.getD (.replicate n 0))[col.val]'col.isLt

@[circuit_norm]
def NExpr.eval (ctx : Ctx F) : NExpr F → ℕ
  | .const n => n
  | .val x => FiniteField.val (x.eval ctx)
  | .idx => ctx.idx
  | .localVar i =>
    match ctx.locals[i]? with
    | some (.inr n) => n
    | _ => 0
  | .add x y => x.eval ctx + y.eval ctx
  | .mul x y => x.eval ctx * y.eval ctx
  | .div x y => x.eval ctx / y.eval ctx
  | .mod x y => x.eval ctx % y.eval ctx
  | .land x y => x.eval ctx &&& y.eval ctx
  | .lor x y => x.eval ctx ||| y.eval ctx
  | .lxor x y => x.eval ctx ^^^ y.eval ctx
  | .shiftL x y => x.eval ctx <<< y.eval ctx
  | .shiftR x y => x.eval ctx >>> y.eval ctx
  | .ite c t e => if c.eval ctx then t.eval ctx else e.eval ctx

@[circuit_norm]
def BExpr.eval (ctx : Ctx F) : BExpr F → Bool
  | .feq x y => FiniteField.val (x.eval ctx) = FiniteField.val (y.eval ctx)
  | .lt x y => x.eval ctx < y.eval ctx
  | .not b => !b.eval ctx

end

end Eval

/-- Vector-shaped output of a witness program. `mapRange` is kept as a loop (not
unrolled); its body may reference the running index via `NExpr.idx`. -/
inductive VExpr (F : Type) where
  | lit (es : List (FExpr F))
  | mapRange (n : ℕ) (body : FExpr F)
  | append (a b : VExpr F)

/-- Static length of a vector expression. -/
def VExpr.length : VExpr F → ℕ
  | .lit es => es.length
  | .mapRange n _ => n
  | .append a b => a.length + b.length

def VExpr.eval [FiniteField F] (ctx : Ctx F) :
    (v : VExpr F) → Vector F v.length
  | .lit es => ⟨(es.map (FExpr.eval ctx)).toArray, by simp [VExpr.length]⟩
  | .mapRange n body => .mapRange n fun i => body.eval { ctx with idx := i }
  | .append a b => a.eval ctx ++ b.eval ctx

/-- A scalar `let`-step: computes one field or Nat value from the environment and
earlier steps. Referenced by position via `localVar`. -/
inductive Step (F : Type) where
  | letF (e : FExpr F)
  | letN (e : NExpr F)

/-- Evaluate the `let`-steps left to right, accumulating their values. -/
def evalSteps [FiniteField F] (env : ProverEnvironment F)
    (steps : List (Step F)) : Array (F ⊕ ℕ) :=
  steps.foldl (init := #[]) fun locals step =>
    match step with
    | .letF e => locals.push (.inl (e.eval { env, locals }))
    | .letN e => locals.push (.inr (e.eval { env, locals }))

/-- A witness-generation program producing `m` field elements. -/
inductive WitgenIR (F : Type) (m : ℕ) where
  /-- Arbitrary Lean closure — migration escape hatch, not serializable.
  `eval (native f) = f` holds definitionally. -/
  | native (f : ProverEnvironment F → Vector F m)
  /-- Structured straight-line program: `let`-steps, then a vector output. -/
  | prog (steps : List (Step F)) (out : VExpr F) (length_eq : out.length = m)

def WitgenIR.eval {m : ℕ} [FiniteField F] :
    WitgenIR F m → ProverEnvironment F → Vector F m
  | .native f => f
  | .prog steps out length_eq => fun env =>
    .cast length_eq (out.eval { env, locals := evalSteps env steps })

@[circuit_norm]
theorem WitgenIR.eval_native {m : ℕ} [FiniteField F]
    (f : ProverEnvironment F → Vector F m) : (WitgenIR.native f).eval = f := rfl

@[circuit_norm]
theorem WitgenIR.eval_native_apply {m : ℕ} [FiniteField F]
    (f : ProverEnvironment F → Vector F m) (env : ProverEnvironment F) :
    (WitgenIR.native f).eval env = f env := rfl

/-!
## Smart constructors

The base building blocks used by the IR-based witness entry points
(`witnessField`, `witnessVector`, `ProvableType.witness`) and by `<==`.
Their `eval` lemmas are tagged `circuit_norm` so that IR-built witnesses
simp-normalize to exactly the same hypothesis shapes as the closures they replace.
-/

/-- Witness program producing a single scalar from a field-sorted IR expression. -/
def WitgenIR.ofFExpr (e : FExpr F) : WitgenIR F 1 := .prog [] (.lit [e]) rfl

/-- Witness program computing each output element from its own IR expression. -/
def WitgenIR.ofFExprs {n : ℕ} (es : Vector (FExpr F) n) : WitgenIR F n :=
  .prog [] (.lit es.toList) (by simp [VExpr.length])

/-- Witness program copying the values of given circuit expressions (used by `<==`). -/
def WitgenIR.ofExprs {n : ℕ} (es : Vector (Expression F) n) : WitgenIR F n :=
  .prog [] (.lit (es.toList.map .expr)) (by simp [VExpr.length])

theorem WitgenIR.eval_ofFExpr [FiniteField F] (e : FExpr F) (env : ProverEnvironment F) :
    (ofFExpr e).eval env = #v[e.eval { env }] := rfl

theorem WitgenIR.eval_ofExprs [FiniteField F] {n : ℕ} (es : Vector (Expression F) n)
    (env : ProverEnvironment F) :
    (ofExprs es).eval env = es.map (Expression.eval env.toEnvironment) := by
  ext i hi
  simp [ofExprs, WitgenIR.eval, VExpr.eval, FExpr.eval, evalSteps, Vector.cast]

/-- Scalar witness programs evaluate elementwise to their IR expression. -/
@[circuit_norm ↓]
theorem WitgenIR.getElem_eval_ofFExpr [FiniteField F] (e : FExpr F)
    (env : ProverEnvironment F) (i : ℕ) (hi : i < 1) :
    ((ofFExpr e).eval env)[i] = e.eval { env := env } := by
  rcases Nat.lt_one_iff.mp hi
  rfl

/-- Elementwise evaluation of multi-element witness programs, keyed on `getElem`. -/
@[circuit_norm ↓]
theorem WitgenIR.getElem_eval_ofFExprs [FiniteField F] {n : ℕ} (es : Vector (FExpr F) n)
    (env : ProverEnvironment F) (i : ℕ) (hi : i < n) :
    ((ofFExprs es).eval env)[i] = es[i].eval { env := env } := by
  simp [ofFExprs, WitgenIR.eval, VExpr.eval, evalSteps, Vector.cast]

/-- Field-equality conditions decide propositional equality (via the injective
`ℕ` embedding). -/
@[circuit_norm]
theorem BExpr.eval_feq_iff [FiniteField F] (x y : FExpr F) (ctx : Ctx F) :
    (BExpr.feq x y).eval ctx = true ↔ x.eval ctx = y.eval ctx := by
  simp only [BExpr.eval, decide_eq_true_eq]
  exact FiniteField.ext_iff.symm

/-- Shape-exact evaluation for expression-copying scalar witnesses (`<==`):
produces the same normal form as the closure it replaced. -/
@[circuit_norm]
theorem WitgenIR.eval_ofFExpr_expr [FiniteField F] (e : Expression F)
    (env : ProverEnvironment F) :
    (ofFExpr (.expr e)).eval env = #v[e.eval env.toEnvironment] := rfl

/-- Elementwise evaluation of expression-copying witnesses, keyed on `getElem` so it
fires regardless of how the expression vector was built (matches the codebase's
getElem-first simp discipline). -/
@[circuit_norm ↓]
theorem WitgenIR.getElem_eval_ofExprs [FiniteField F] {n : ℕ}
    (es : Vector (Expression F) n) (env : ProverEnvironment F) (i : ℕ) (hi : i < n) :
    ((ofExprs es).eval env)[i] = es[i].eval env.toEnvironment := by
  rw [eval_ofExprs]
  simp

/-!
## Expressibility checks

The four key callbacks from the requirements doc (`IsZeroField`, Keccak `Xor64`,
SHA256 `Add32`, FemtoCairo memory read), expressed as IR programs. Where the agreement
proof with the original lambda is cheap, we prove it; the rest are constructions whose
ports (phase 5) will carry the proofs.
-/

section Examples
variable [FiniteField F]

/-- Deciding field equality via the `ℕ` embedding agrees with propositional equality. -/
theorem val_eq_zero_iff (x : F) : FiniteField.val x = 0 ↔ x = 0 := by
  rw [← FiniteField.val_zero (F := F)]
  exact FiniteField.ext_iff.symm

/-- `IsZeroField` witness: `fun env => if env x ≠ 0 then (env x)⁻¹ else 0`. -/
def isZeroWitness (x : Expression F) : WitgenIR F 1 :=
  .prog [] (.lit [.ite (.feq (.expr x) (.const 0)) (.const 0) (.inv (.expr x))]) rfl

example [DecidableEq F] (x : Expression F) (env : ProverEnvironment F) :
    (isZeroWitness x).eval env = #v[if x.eval env.toEnvironment ≠ 0
      then (x.eval env.toEnvironment)⁻¹ else 0] := by
  ext i hi
  simp [isZeroWitness, WitgenIR.eval, VExpr.eval, FExpr.eval, BExpr.eval,
    evalSteps, Vector.cast, ← FiniteField.ext_iff, ite_not]

/-- One byte of the Keccak `Xor64` witness: `((env x).val ^^^ (env y).val : F)`. -/
def xorByteWitness (x y : Expression F) : WitgenIR F 1 :=
  .prog [] (.lit [.ofNat (.lxor (.val (.expr x)) (.val (.expr y)))]) rfl

example (x y : Expression F) (env : ProverEnvironment F) :
    (xorByteWitness x y).eval env
      = #v[FiniteField.fromNat
        (FiniteField.val (x.eval env.toEnvironment) ^^^ FiniteField.val (y.eval env.toEnvironment))] := by
  ext i hi
  simp [xorByteWitness, WitgenIR.eval, VExpr.eval, FExpr.eval, NExpr.eval,
    evalSteps, Vector.cast]

/-- `Σ i, (env a[i]).val * 2^i` — the Nat value of a vector of bit-variables
(SHA256 `Add32.evalBitsNat`), folded into an `NExpr` at authoring time. -/
def bitsValExpr (a : Vector (Expression F) 32) : NExpr F :=
  Fin.foldl 32 (fun acc i =>
    .add acc (.shiftL (.val (.expr a[i.val])) (.const i.val))) (.const 0)

/-- SHA256 `Add32` sum witness:
`let s := (evalBitsNat a + evalBitsNat b) % 2^32; Vector.ofFn fun i => (s / 2^i % 2 : F)`.
The shared sum `s` becomes a `letN` step; the 32 output bits a `mapRange` loop. -/
def add32Witness (a b : Vector (Expression F) 32) : WitgenIR F 32 :=
  .prog [.letN (.mod (.add (bitsValExpr a) (bitsValExpr b)) (.const (2^32)))]
    (.mapRange 32 (.ofNat (.mod (.shiftR (.localVar 0) .idx) (.const 2))))
    rfl

/-- FemtoCairo-style nondeterministic memory read:
`if (env addr).val < memSize then (data "Memory")[addr.val].value else 0`,
with rows laid out as `(address, value)` pairs. -/
def memReadWitness (addr : Expression F) (memSize : ℕ) : WitgenIR F 1 :=
  .prog []
    (.lit [.ite (.lt (.val (.expr addr)) (.const memSize))
      (.dataGet "Memory" 2 (.val (.expr addr)) 1)
      (.const 0)])
    rfl

/-- `fieldToBits`-style decomposition (`Gadgets.ToBits`): bit `i` is
`(x.val >>> i) % 2`, as a `mapRange` loop over the index. -/
def toBitsWitness (n : ℕ) (x : Expression F) : WitgenIR F n :=
  .prog [] (.mapRange n (.ofNat (.testBit (.val (.expr x)) .idx))) rfl

end Examples

end Witgen

export Witgen (WitgenIR)
