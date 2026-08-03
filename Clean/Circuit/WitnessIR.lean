import Clean.Circuit.Expression
import Clean.Utils.Field
import Clean.Utils.FiniteField
import Clean.Utils.Vector
import Clean.Circuit.Provable

/-!
# Witness-generation IR

A deep-embedded IR for witness-generation callbacks

## Design

A witness program (`WitgenIR F m`) is either
- `native f` — an arbitrary Lean closure, the migration escape hatch. Not serializable.
  `eval (native f) = f` holds definitionally, which is what lets phase 2 wrap all
  existing callbacks without touching any gadget or proof.
- `ir steps out` — structured IR: a list of scalar `let`-steps, followed by a
  vector-shaped output expression.

Scalar expressions come in 3 sorts, reflecting the codebase's pervasive
`field → ZMod.val → integer ops → cast → field` pattern:
- `FExpr` — field-sorted: embedded circuit `Expression`s (which is how callbacks read
  inputs and earlier witnesses), arithmetic, inverse (IsZeroField), conditionals,
  bit extraction, constant-table reads, prover-data/hint reads.
- `UExpr` — **u64-sorted** (bounded nat): arithmetic, div/mod, bitwise ops, shifts;
  bridges are `UExpr.val : FExpr → UExpr` and `FExpr.ofU64 : UExpr → FExpr`.
- `BExpr` — conditions: field equality and u64 comparison (requirement B.7).

The output is a `VExpr`: a literal list, a `mapRange n body` (body may reference the
running index via `UExpr.idx`) — kept as a *loop* rather than unrolled — an environment
range, a field-element bit decomposition, or an append.

## Why u64 and not `ℕ`

Arbitrary-precision naturals are not what a witness-generation backend wants to run
(issue #429): they are expensive, awkward to implement outside Lean, and operations like
unbounded `mul`/`add` have no counterpart in real code. The integer sort is therefore
`UInt64` throughout, with **wrapping** semantics that mirror Rust's `u64`:

- `UExpr.val x` is `FiniteField.val x` truncated to 64 bits (`UInt64.ofNat`, i.e. `mod 2^64`),
- `FExpr.ofU64 n` casts back through `FiniteField.fromNat n.toNat`,
- `UExpr.const n` truncates its `ℕ` payload the same way.

Two operations that genuinely need more than 64 bits are kept at the *field* level
instead of being expressed through the integer sort, so no gadget has to assume that a
254-bit field element fits in a `u64`:

- `FExpr.bitOf x i` — bit `i` of `FiniteField.val x` (a static bit index),
- `VExpr.bitsOf` — the `n` low bits of `FiniteField.val x` (bit-decomposition gadgets).

Similarly `VExpr.envRange offset` replaces per-element environment reads at computed
indices, so witness offsets never round-trip through `u64`.

## TOOD Potential open issues

1. **One index binder.** `UExpr.idx` refers to the innermost enclosing `VExpr.mapRange`;
   nesting shadows. No surveyed gadget nests mapRanges inside a single callback. If that
   changes, `idx` generalizes to de Bruijn levels.
2. **Untyped locals.** `localVar i` is resolved in an `F ⊕ UInt64` array with a 0 default
   on sort mismatch / out of range, keeping `eval` total without intrinsically-typed
   syntax. A decidable well-sortedness check can be layered on top later (it will be
   needed for serialization anyway).
-/

variable {F : Type}

namespace Witgen

mutual

/-- Field-sorted witness expressions. -/
inductive FExpr (F : Type) where
  /-- Embedded circuit expression; this is how callbacks read input vars and earlier
  witnesses (`env x`). -/
  | expr (e : Expression F)
  | const (c : F)
  /-- Reference to an earlier `Step` result (must be a `letF` step). -/
  | localVar (i : ℕ)
  | add (x y : FExpr F)
  | mul (x y : FExpr F)
  /-- Field inverse, with `0⁻¹ = 0` (the `IsZeroField` witness). -/
  | inv (x : FExpr F)
  /-- Cast from the u64 sort via `FiniteField.fromNat` (the inverse of `val`;
  equals `Nat.cast` on prime fields, but interprets binary digits as coefficients
  on binary fields, where `Nat.cast` would collapse via the characteristic). -/
  | ofU64 (n : UExpr F)
  /-- Bit `i` of `FiniteField.val x`, as the field element `0` or `1`. Kept at the
  field level (rather than `(x.val >>> i) % 2`) so that bit indices beyond 64 stay
  meaningful on large fields. -/
  | bitOf (x : FExpr F) (i : ℕ)
  | ite (c : BExpr F) (t e : FExpr F)
  /-- Read an expression list at a computed index, 0 if out of range -/
  | listGet (xs : List (FExpr F)) (i : UExpr F)
  /-- Read committed prover data (`Environment.data`), keyed like `ProverData`:
  row `row` of table `key` with rows of width `n`, projected at column `col`.
  Missing rows read as 0. The nondeterministic escape hatch (FemtoCairo memory). -/
  | dataGet (key : String) (n : ℕ) (row : UExpr F) (col : Fin n)
  /-- Same as `dataGet` but reads the uncommitted `ProverEnvironment.hint`. -/
  | hintGet (key : String) (n : ℕ) (row : UExpr F) (col : Fin n)

/-- u64-sorted (bounded-nat) witness expressions. All operations wrap modulo `2^64`,
matching Rust's `u64`. -/
inductive UExpr (F : Type) where
  /-- A `ℕ` literal, truncated to 64 bits. -/
  | const (n : ℕ)
  /-- The field→u64 bridge: `ZMod.val` truncated to 64 bits. -/
  | val (x : FExpr F)
  /-- The index of the innermost enclosing `VExpr.mapRange` (0 outside). -/
  | idx
  /-- Reference to an earlier `Step` result (must be a `letU` step). -/
  | localVar (i : ℕ)
  | add (x y : UExpr F)
  | mul (x y : UExpr F)
  | div (x y : UExpr F)
  | mod (x y : UExpr F)
  | land (x y : UExpr F)
  | lor (x y : UExpr F)
  | lxor (x y : UExpr F)
  | shiftL (x y : UExpr F)
  | shiftR (x y : UExpr F)
  | ite (c : BExpr F) (t e : UExpr F)

/-- Conditions. -/
inductive BExpr (F : Type) where
  | true
  | false
  /-- Field equality condition (decided via the injective `ℕ` embedding). -/
  | feq (x y : FExpr F)
  /-- u64 equality condition. -/
  | neq (x y : UExpr F)
  /-- u64-sorted less-than condition. -/
  | lt (x y : UExpr F)
  /-- Negation of a condition. -/
  | not (b : BExpr F)
  /-- Conjunction of conditions. -/
  | and (x y : BExpr F)

end

/-- `x - y` as a derived field expression. -/
@[reducible] def FExpr.sub [Field F] (x y : FExpr F) : FExpr F := .add x (.mul (.const (-1)) y)

/-- `-x` as a derived field expression. -/
@[reducible] def FExpr.neg [Field F] (x : FExpr F) : FExpr F := .mul (.const (-1)) x

/-- `2^k` as a derived u64 expression. -/
@[reducible] def UExpr.pow2 (k : UExpr F) : UExpr F := .shiftL (.const 1) k

/-- `Nat.testBit x i` as a derived u64 expression, valued in {0, 1}. -/
@[reducible] def UExpr.testBit (x i : UExpr F) : UExpr F := .mod (.shiftR x i) (.const 2)

/-- Evaluation context: the prover environment, the values of the `let`-steps computed
so far, and the innermost `mapRange` index. -/
structure Ctx (F : Type) where
  env : ProverEnvironment F
  locals : Array (F ⊕ UInt64) := #[]
  idx : ℕ := 0

section Eval
variable [FiniteField F]

mutual

@[circuit_norm]
def FExpr.eval (ctx : Ctx F) : FExpr F → F
  | .expr e => e.eval ctx.env.toEnvironment
  | .const c => c
  | .localVar i =>
    match ctx.locals[i]? with
    | some (.inl x) => x
    | _ => 0
  | .add x y => x.eval ctx + y.eval ctx
  | .mul x y => x.eval ctx * y.eval ctx
  | .inv x => (x.eval ctx)⁻¹
  | .ofU64 n => FiniteField.fromNat (n.eval ctx).toNat
  | .bitOf x i => FiniteField.fromNat (FiniteField.val (x.eval ctx) >>> i % 2)
  | .ite c t e => if c.eval ctx then t.eval ctx else e.eval ctx
  | .listGet xs i => FExpr.evalList ctx (i.eval ctx).toNat xs
  | .dataGet key n row col =>
    ((ctx.env.data key n)[(row.eval ctx).toNat]?.getD default)[col.val]'col.isLt
  | .hintGet key n row col =>
    ((ctx.env.hint key n)[(row.eval ctx).toNat]?.getD default)[col.val]'col.isLt

@[circuit_norm]
def FExpr.evalList (ctx : Ctx F) : ℕ → List (FExpr F) → F
  | _, [] => 0
  | 0, x :: _ => x.eval ctx
  | i + 1, _ :: xs => FExpr.evalList ctx i xs

@[circuit_norm]
def UExpr.eval (ctx : Ctx F) : UExpr F → UInt64
  | .const n => UInt64.ofNat n
  | .val x => UInt64.ofNat (FiniteField.val (x.eval ctx))
  | .idx => UInt64.ofNat ctx.idx
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
  | .true => true
  | .false => false
  | .feq x y => x.eval ctx = y.eval ctx
  | .neq x y => x.eval ctx = y.eval ctx
  | .lt x y => x.eval ctx < y.eval ctx
  | .not b => !b.eval ctx
  | .and x y => x.eval ctx && y.eval ctx

end

/-! ### `u64` normalization

Witness-IR proofs live in `ℕ`: every u64-sorted subterm reaches the field via
`FExpr.ofU64`, which applies `UInt64.toNat`. Pushing `toNat` through the operations turns
a `UExpr` evaluation into ordinary `ℕ` arithmetic with explicit `% 2^64` wraps, which
`omega` / `Nat.mod_eq_of_lt` discharge whenever the gadget's own bounds make the
operation non-wrapping. -/
attribute [circuit_norm]
  UInt64.toNat_add UInt64.toNat_mul UInt64.toNat_div UInt64.toNat_mod
  UInt64.toNat_and UInt64.toNat_or UInt64.toNat_xor
  UInt64.toNat_shiftLeft UInt64.toNat_shiftRight
  UInt64.toNat_ofNat' UInt64.toNat_ofNat UInt64.lt_iff_toNat_lt

/-- `u64` equality is `ℕ` equality of the truncations — the shape the `toNat`-pushing
`circuit_norm` lemmas above leave the rest of a condition in. -/
@[circuit_norm]
theorem UInt64.eq_iff_toNat_eq {a b : UInt64} : a = b ↔ a.toNat = b.toNat :=
  UInt64.toNat_inj.symm

variable {M : TypeMap} [ProvableType M]

/-- Evaluation for higher-level provable types. -/
def eval (ctx : Ctx F) (x : M (Witgen.FExpr F)) : M F :=
  toElements x |> Vector.map (FExpr.eval ctx) |> fromElements

@[circuit_norm]
lemma eval_field (ctx : Ctx F) (x : FExpr F) :
    Witgen.eval (M := field) ctx x = FExpr.eval ctx x := by
  simp [Witgen.eval, explicit_provable_type]

end Eval

/-- Vector-shaped output of a witness program. The length index makes malformed
output-length proofs unnecessary. `mapRange` is kept as a loop (not unrolled);
its body may reference the running index via `NExpr.idx`.

TODO WITGENIR add fold/scan loops (an accumulator-carrying `mapRange`). This is the
one known expressiveness gap, established by porting a full production circuit code
base (Zcash Orchard, PR #409): every witness left on the closure-based `witnessNative`
escape hatch there is a *recursive accumulator* — row `r`'s value chains `r` prior
steps, so it has no compact `VExpr`/`FExpr` form, and unrolled per-row expansion would
be O(n²) term size (n = 254 rounds for EC scalar multiplication). The blocked shapes:
running-sum decompositions and double-and-add accumulators of variable-base scalar mul
(each row chains EC additions with inverses, plus the packed scalar-bit hints whose
only consumers are those accumulators), and Sinsemilla hash chains (each piece chains
incomplete additions). A `scanRange`-style former (body sees `NExpr.idx` plus one
`localVar`-like accumulator slot, producing all intermediate values) would cover every
known site; evaluation and `circuit_norm` lemmas can mirror `mapRange`'s. Caveat from
the halo2 source design: the Sinsemilla y-accumulator is *deliberately* kept off the
constraint system — porting its computation to the IR must keep it a hint. -/
inductive VExpr (F : Type) : ℕ → Type where
  | lit {n : ℕ} (es : Vector (FExpr F) n) : VExpr F n
  | mapRange (n : ℕ) (body : FExpr F) : VExpr F n
  /-- `n` consecutive environment cells starting at `offset` — the "witness a fresh
  variable per cell" former (`witnessAny`, table rows). The offset is a static `ℕ`, so
  witness offsets never round-trip through the u64 sort. -/
  | envRange {n : ℕ} (offset : ℕ) : VExpr F n
  /-- The `n` low bits of `FiniteField.val x`, each as the field element `0` or `1` —
  the bit-decomposition former. Kept at the field level so that `n` may exceed 64. -/
  | bitsOf {n : ℕ} (x : FExpr F) : VExpr F n
  | append {m n : ℕ} (a : VExpr F m) (b : VExpr F n) : VExpr F (m + n)

instance {n} : Coe (Vector (FExpr F) n) (VExpr F n) where
  coe es := .lit es

def VExpr.eval [FiniteField F] (ctx : Ctx F) : {n : ℕ} → VExpr F n → Vector F n
  | _, .lit es => es.map (FExpr.eval ctx)
  | _, .mapRange n body => .mapRange n fun i => body.eval { ctx with idx := i }
  | n, .envRange offset => .mapRange n fun i => ctx.env.get (offset + i)
  | n, .bitsOf x => .mapRange n fun i =>
      FiniteField.fromNat (FiniteField.val (x.eval ctx) >>> i % 2)
  | _, .append a b => a.eval ctx ++ b.eval ctx

/-- A scalar `let`-step: computes one field or u64 value from the environment and
earlier steps. Referenced by position via `localVar`. -/
inductive Step (F : Type) where
  | letF (e : FExpr F)
  | letU (e : UExpr F)

/-- Evaluate the `let`-steps left to right, accumulating their values. -/
@[circuit_norm]
def evalSteps [FiniteField F] (env : ProverEnvironment F)
    (steps : List (Step F)) (locals : Array (F ⊕ UInt64) := #[]) : Array (F ⊕ UInt64) :=
  match steps with
  | [] => locals
  | .letF e :: steps => evalSteps env steps (locals.push (.inl (e.eval { env, locals })))
  | .letU e :: steps => evalSteps env steps (locals.push (.inr (e.eval { env, locals })))

/-- A witness-generation program producing `m` field elements. -/
inductive WitgenIR (F : Type) : ℕ → Type where
  /-- Arbitrary Lean closure — migration escape hatch, not serializable.
  `eval (native f) = f` holds definitionally. -/
  | native {m : ℕ} (f : ProverEnvironment F → Vector F m) : WitgenIR F m
  /-- Structured straight-line program: `let`-steps, then a vector output. -/
  | ir {m : ℕ} (steps : List (Step F)) (out : VExpr F m) : WitgenIR F m

def WitgenIR.eval {m : ℕ} [FiniteField F] :
    WitgenIR F m → ProverEnvironment F → Vector F m
  | .native f => f
  | .ir steps out => fun env =>
    out.eval { env, locals := evalSteps env steps }

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
(`witnessField`, `witnessVector`, `witnessIR`) and by `<==`.
Their `eval` lemmas are tagged `circuit_norm` so that IR-built witnesses
simp-normalize to exactly the same hypothesis shapes as the closures they replace.
-/

/-- Witness program producing a single scalar from a field-sorted IR expression. -/
def WitgenIR.ofFExpr (e : FExpr F) : WitgenIR F 1 := .ir [] (.lit #v[e])

/-- Witness program computing each output element from its own IR expression. -/
def WitgenIR.ofFExprs {n : ℕ} (es : Vector (FExpr F) n) : WitgenIR F n :=
  .ir [] (.lit es)

/-- Witness program computing a whole provable value from a native Lean closure — the
payload of `witnessNative`. A named definition (rather than an inline `.native` lambda)
so that the completeness obligation of `witnessNative` stays recognizable and can be
rewritten at the level of provable values (`ProverEnvironment.extendsVector_nativeValue`
in `Clean.Circuit.Basic`) instead of unfolding element-wise into `toElements` internals.
For the same reason, this is deliberately not tagged `@[circuit_norm]`. -/
def WitgenIR.nativeValue {value : TypeMap} [ProvableType value]
    (compute : ProverEnvironment F → value F) : WitgenIR F (size value) :=
  .native fun env => compute env |> toElements

theorem WitgenIR.eval_nativeValue [FiniteField F] {value : TypeMap} [ProvableType value]
    (compute : ProverEnvironment F → value F) (env : ProverEnvironment F) :
    (WitgenIR.nativeValue compute).eval env = toElements (compute env) := rfl

/-- `Witgen.eval` on `fields n` is elementwise evaluation (the witgen analogue of
`ProvableType.eval_fields`). -/
theorem eval_fields' [FiniteField F] {n : ℕ} (ctx : Ctx F) (xs : Vector (FExpr F) n) :
    Witgen.eval (M := fields n) ctx xs = xs.map (FExpr.eval ctx) := rfl

/-- Vector analogue of the `evalProjection` simproc: evaluating one element of a vector
of IR expressions is one element of the evaluated vector. Lifts stuck element reads of
*opaque* vectors (e.g. per-index reads of an `Unconstrained (fields n)` hint) to the
vector level, where row-level facts (`h_input` equations) can consume them. Stated as a
post-rewrite so that literal vectors reduce first (`Vector.getElem_ofFn` etc.) and never
reach this lemma. -/
@[circuit_norm]
theorem FExpr.eval_getElem [FiniteField F] {n : ℕ} (ctx : Ctx F)
    (xs : Vector (FExpr F) n) (i : ℕ) (hi : i < n) :
    FExpr.eval ctx xs[i] = (Witgen.eval (M := fields n) ctx xs)[i] := by
  rw [eval_fields', Vector.getElem_map]

/-- Witness program copying the values of given circuit expressions (used by `<==`). -/
def WitgenIR.ofExprs {n : ℕ} (es : Vector (Expression F) n) : WitgenIR F n :=
  .ir [] (.lit (es.map .expr))

@[circuit_norm]
theorem WitgenIR.eval_ofFExpr [FiniteField F] (e : FExpr F) (env : ProverEnvironment F) :
    (ofFExpr e).eval env = #v[e.eval { env }] := by
  ext i hi
  rcases Nat.lt_one_iff.mp hi
  simp [ofFExpr, WitgenIR.eval, VExpr.eval, evalSteps]

theorem WitgenIR.eval_ofExprs [FiniteField F] {n : ℕ} (es : Vector (Expression F) n)
    (env : ProverEnvironment F) :
    (ofExprs es).eval env = es.map (Expression.eval env.toEnvironment) := by
  ext i hi
  simp [ofExprs, WitgenIR.eval, VExpr.eval, FExpr.eval, evalSteps]

attribute [circuit_norm] Array.getElem?_singleton

/- Witness-IR `BExpr` conditions surface in goals as `decide P = true` (via the
`Bool → Prop` coercion in `FExpr.eval`'s `.ite` case), with the `Decidable` instance
baked at `BExpr.eval`'s definition site — which is *not* syntactically the instance a
user writes at a concrete field, so `decide`-spelled proof patterns never match.
Normalizing to the propositional form in `circuit_norm` removes the instance from the
condition entirely (it survives only as the `ite`'s instance argument, where
instance-polymorphic lemmas like `if_pos`/`if_neg`/`by_cases` handle it); together with
`FiniteField.val_inj` this gives `.feq` conditions the plain `x = y` shape. -/
attribute [circuit_norm] decide_eq_true_eq

/-- Elementwise evaluation of `mapRange` vector outputs, keyed on the eval term. -/
@[circuit_norm ↓]
theorem VExpr.getElem_eval_mapRange [FiniteField F] (ctx : Ctx F) (n : ℕ) (body : FExpr F)
    (i : ℕ) (hi : i < n) :
    (VExpr.eval ctx (.mapRange n body))[i] = body.eval { ctx with idx := i } := by
  simp [VExpr.eval, Vector.getElem_mapRange]

/-- Elementwise evaluation of environment ranges, keyed on the eval term. -/
@[circuit_norm ↓]
theorem VExpr.getElem_eval_envRange [FiniteField F] (ctx : Ctx F) {n : ℕ} (offset : ℕ)
    (i : ℕ) (hi : i < n) :
    (VExpr.eval ctx (.envRange (n := n) offset))[i] = ctx.env.get (offset + i) := by
  simp [VExpr.eval, Vector.getElem_mapRange]

/-- Elementwise evaluation of bit decompositions, keyed on the eval term. -/
@[circuit_norm ↓]
theorem VExpr.getElem_eval_bitsOf [FiniteField F] (ctx : Ctx F) {n : ℕ} (x : FExpr F)
    (i : ℕ) (hi : i < n) :
    (VExpr.eval ctx (.bitsOf (n := n) x))[i]
      = FiniteField.fromNat (FiniteField.val (x.eval ctx) >>> i % 2) := by
  simp [VExpr.eval, Vector.getElem_mapRange]

/-- Elementwise evaluation of literal vector outputs, keyed on the eval term. -/
@[circuit_norm ↓]
theorem VExpr.getElem_eval_lit [FiniteField F] {n : ℕ} (ctx : Ctx F)
    (es : Vector (FExpr F) n) (i : ℕ) (hi : i < n) :
    (VExpr.eval ctx (.lit es))[i] = es[i].eval ctx := by
  simp [VExpr.eval]

/-- Elementwise evaluation of general witness programs, keyed on `getElem`:
reduces to the output vector expression evaluated with the `let`-steps in scope. -/
@[circuit_norm ↓]
theorem WitgenIR.getElem_eval_ir [FiniteField F] {n : ℕ} (steps : List (Step F))
    (out : VExpr F n) (env : ProverEnvironment F)
    (i : ℕ) (hi : i < n) :
    ((WitgenIR.ir steps out).eval env)[i]
      = (out.eval { env := env, locals := evalSteps env steps })[i] := by
  rfl

/-- Scalar witness programs evaluate elementwise to their IR expression. -/
@[circuit_norm ↓]
theorem WitgenIR.getElem_eval_ofFExpr [FiniteField F] (e : FExpr F)
    (env : ProverEnvironment F) (i : ℕ) (hi : i < 1) :
    ((ofFExpr e).eval env)[i] = e.eval { env } := by
  rcases Nat.lt_one_iff.mp hi
  simp [ofFExpr, WitgenIR.eval, VExpr.eval, evalSteps]

/-- Elementwise evaluation of multi-element witness programs, keyed on `getElem`. -/
@[circuit_norm ↓]
theorem WitgenIR.getElem_eval_ofFExprs [FiniteField F] {n : ℕ} (es : Vector (FExpr F) n)
    (env : ProverEnvironment F) (i : ℕ) (hi : i < n) :
    ((ofFExprs es).eval env)[i] = es[i].eval { env } := by
  simp [ofFExprs, WitgenIR.eval, VExpr.eval, evalSteps]

@[circuit_norm]
theorem WitgenIR.eval_ofFExprs_singleton {F: Type} [FiniteField F]
    (x : FExpr F) (env : ProverEnvironment F) :
    (WitgenIR.ofFExprs (toElements (M:=field) x)).eval env = #v[x.eval { env }] := by
  with_unfolding_all rfl

/-- Field-equality conditions decide propositional equality (via the injective
`ℕ` embedding). -/
@[circuit_norm]
theorem BExpr.eval_feq_iff [FiniteField F] (x y : FExpr F) (ctx : Ctx F) :
    (BExpr.feq x y).eval ctx = Bool.true ↔ x.eval ctx = y.eval ctx := by
  simp only [BExpr.eval, decide_eq_true_eq]

/-- Shape-exact evaluation for expression-copying scalar witnesses (`<==`):
produces the same normal form as the closure it replaced. -/
@[circuit_norm]
theorem WitgenIR.eval_ofFExpr_expr [FiniteField F] (e : Expression F)
    (env : ProverEnvironment F) :
    (ofFExpr (.expr e)).eval env = #v[e.eval env.toEnvironment] := by
  ext i hi
  rcases Nat.lt_one_iff.mp hi
  simp [ofFExpr, WitgenIR.eval, VExpr.eval, FExpr.eval, evalSteps]

/-- Elementwise evaluation of expression-copying witnesses, keyed on `getElem` so it
fires regardless of how the expression vector was built (matches the codebase's
getElem-first simp discipline). -/
@[circuit_norm ↓]
theorem WitgenIR.getElem_eval_ofExprs [FiniteField F] {n : ℕ}
    (es : Vector (Expression F) n) (env : ProverEnvironment F) (i : ℕ) (hi : i < n) :
    ((ofExprs es).eval env)[i] = es[i].eval env.toEnvironment := by
  rw [eval_ofExprs]
  simp

/-- Shape-exact evaluation for expression-copying struct witnesses (`<==`):
produces the same normal form as the closure it replaced. -/
@[circuit_norm]
theorem WitgenIR.eval_ofExprs_toElements [FiniteField F] {M : TypeMap} [ProvableType M]
    (x : M (Expression F)) (env : ProverEnvironment F) :
    (WitgenIR.ofExprs (toElements x)).eval env
      = toElements (Eval.eval env.toEnvironment x) := by
  rw [WitgenIR.eval_ofExprs, ProvableType.toElements_eval]

/-!
## Eval-simplification tooling
-/

section Eval
variable [FiniteField F] {M : TypeMap} [ProvableStruct M]

namespace StructEval
/-- Struct-preserving evaluation for witness-IR expressions. -/
@[circuit_norm]
def eval (ctx : Ctx F) (var : M (FExpr F)) : M F :=
  toComponents var |> go (components M) |> fromComponents
where
  @[circuit_norm]
  go : (cs : List _root_.ProvableStruct.WithProvableType) →
      _root_.ProvableStruct.ProvableTypeList (FExpr F) cs →
        _root_.ProvableStruct.ProvableTypeList F cs
    | [], .nil => .nil
    | _ :: cs, .cons a as => .cons (Witgen.eval ctx a) (go cs as)

theorem eval_eq_eval {M : TypeMap} [ProvableStruct M] (ctx : Ctx F) (x : M (FExpr F)) :
    Witgen.eval ctx x = StructEval.eval ctx x := by
  symm
  simp only [Witgen.eval, eval, fromElements, toElements, size]
  congr 1
  apply eval_eq_eval_aux
where
  eval_eq_eval_aux (ctx : Ctx F) : (cs : List _root_.ProvableStruct.WithProvableType) →
      (as : _root_.ProvableStruct.ProvableTypeList (FExpr F) cs) →
    eval.go ctx cs as =
      (_root_.ProvableStruct.componentsToElements cs as |> Vector.map (FExpr.eval ctx) |>
        _root_.ProvableStruct.componentsFromElements cs)
  | [], .nil => rfl
  | c :: cs, .cons a as => by
    simp only [_root_.ProvableStruct.componentsToElements,
      _root_.ProvableStruct.componentsFromElements, eval.go,
      _root_.ProvableStruct.combinedSize', List.map_cons, List.sum_cons]
    simp only [Vector.map_append, Vector.cast_take_append_of_eq_length,
      Vector.cast_drop_append_of_eq_length]
    congr
    apply eval_eq_eval_aux
end StructEval

open Lean Meta Simp in
/--
Normalize witness-IR evaluation of projections out of provable structs.

The motivating term comes from typed table reads such as
`MemoryTable.dataGet row : MemoryEntry (FExpr F)`.  When a circuit witnesses only one field, Lean
sees a scalar expression:

```
FExpr.eval ctx (MemoryTable.dataGet row).value
```

The row-level theorem `Table.eval_dataGet` cannot fire on that term, because the projection has
already selected one `FExpr`.  This simproc recovers the row-level shape by rewriting projections:

```
FExpr.eval ctx r.value  ~~>  (Witgen.eval ctx r).value
```

After that, ordinary `circuit_norm` can use row-level lemmas, and normal projection reduction gives
the field that the proof actually needs.

This is a simproc rather than a lemma because Lean lemmas cannot quantify over an arbitrary
structure projection like `.value`, `.address`, etc.  The meta code recognizes projection
applications, rebuilds the same projection on the evaluated row, then proves the rewrite by
simplifying the generated RHS with the small struct-evaluation theorem set below.
-/
private def evalProjectionSimproc (e : Expr) : SimpM Simp.Step := do
  -- The simproc is registered on `Witgen.FExpr.eval _ _`; the last two explicit arguments are
  -- the evaluation context and the scalar expression being evaluated.
  let args := e.getAppArgs
  unless e.getAppFn.isConstOf ``Witgen.FExpr.eval && args.size >= 2 do
    return .continue
  let ctx := args[args.size - 2]!
  let projected := args[args.size - 1]!

  -- Try to view the scalar expression as a projection `base.field`.
  --
  -- Lean can represent projections either as a dedicated `.proj` node or as an application of the
  -- projection function.  In both cases we return the projected base and a function that rebuilds
  -- the same projection on a new base.
  let view? : Option (Expr × (Expr → MetaM Expr)) ←
      match projected with
      | .proj structName idx base =>
        pure <| some (base, fun evalBase => pure <| mkProj structName idx evalBase)
      | _ =>
        let .const projName _ := projected.getAppFn | pure none
        let some pinfo ← getProjectionFnInfo? projName | pure none
        let projArgs := projected.getAppArgs
        if h : pinfo.numParams < projArgs.size then
          pure <| some (projArgs[pinfo.numParams],
            fun evalBase => mkProjection evalBase (Name.mkSimple projName.getString!))
        else
          pure none
  let some (base, mkRhs) := view?
    | return Simp.Step.continue

  -- Build the candidate RHS `(Witgen.eval ctx base).field`.  `mkAppM` also ensures that this is
  -- only used when the base type has the required `ProvableType` instance.
  let evalBase ← try
      withDefault <| mkAppM ``Witgen.eval #[ctx, base]
    catch _ =>
      return Simp.Step.continue
  let rhs ← mkRhs evalBase

  -- Prove that the candidate RHS reduces back to the original scalar evaluation.  This internal
  -- simp set is intentionally small: using the ambient `circuit_norm` set here would let row-level
  -- lemmas such as `Table.eval_dataGet` fire too early, before this simproc returns the row-level
  -- term to the outer simplifier.
  let mut thms : SimpTheorems := {}
  thms ← thms.addConst ``Witgen.StructEval.eval_eq_eval
  thms ← thms.addConst ``Witgen.eval_field
  thms ← thms.addDeclToUnfold ``Witgen.StructEval.eval
  thms ← thms.addDeclToUnfold ``Witgen.StructEval.eval.go
  thms ← thms.addDeclToUnfold ``ProvableStruct.components
  thms ← thms.addDeclToUnfold ``ProvableStruct.toComponents
  thms ← thms.addDeclToUnfold ``ProvableStruct.fromComponents
  let simpCtx ← Simp.mkContext (simpTheorems := #[thms])
  let (rhsSimp, _) ← Meta.simp rhs simpCtx #[]
  unless ← withDefault <| isDefEq rhsSimp.expr e do
    return Simp.Step.continue

  -- `rhsSimp` proves `rhs = e`; the simproc must return a proof of `e = rhs`.
  -- Return `.done` rather than `.visit` so the outer simplifier keeps the row-level shape and can
  -- continue from there, instead of immediately descending back into scalar projections.
  let result ← rhsSimp.mkEqSymm rhs
  return .done result

simproc evalProjection (Witgen.FExpr.eval _ _) := evalProjectionSimproc
attribute [circuit_norm] evalProjection

open Lean Meta Simp in
/--
Evaluate witness-IR *struct literals* component-wise.

`Witgen.eval ctx s`, where `s` is a literal constructor application of a `ProvableStruct`
type, decomposes into per-component evaluations (via `StructEval.eval`) — mirroring the
component-preserving normal form of the regular `ProvableStruct.eval`. This is the shape
produced by struct-valued `witnessProgram`s whose `do`-block assembles an output record
(e.g. Poseidon's `Permute.State`), where the proof needs the per-component values.

*Opaque* values (hint programs, table rows) are deliberately left alone: they stay
row-level `Witgen.eval` atoms, to be consumed by row-level facts — `h_input` equations
from hint inputs, or `Table.eval_dataGet` — working together with the `evalProjection`
simproc above. Decomposing an opaque value via structure eta would produce
`FExpr.eval ctx s.field` terms that `evalProjection` immediately rewrites back to
`(Witgen.eval ctx s).field`, looping. Restricting to literals makes the two simprocs
confluent: a literal's components are the program's own expressions, never projections
of an opaque base.
-/
private def evalStructLiteralSimproc (e : Expr) : SimpM Simp.Step := do
  let args := e.getAppArgs
  unless e.getAppFn.isConstOf ``Witgen.eval && args.size >= 2 do
    return .continue
  let ctx := args[args.size - 2]!
  let x := args[args.size - 1]!
  -- only fire on literal constructor applications
  let .const fn _ := x.getAppFn | return .continue
  let some (.ctorInfo info) := (← getEnv).find? fn | return .continue
  -- `ProvableStruct` route: rewrite via `StructEval` (`mkAppM` synthesizes the instance)
  try
    let proof ← mkAppM ``Witgen.StructEval.eval_eq_eval #[ctx, x]
    let some (_, _, rhs) := (← inferType proof).eq? | return .continue
    return .visit { expr := rhs, proof? := proof }
  catch _ => pure ()
  -- custom-`ProvableType` route (e.g. `Point`): rewrite the literal component-wise,
  -- validated by definitional equality. Covers flat structs of scalars; bails if a field
  -- is not a scalar `FExpr` or the instance doesn't evaluate field-by-field in
  -- constructor order.
  try
    let ctorArgs := x.getAppArgs
    if ctorArgs.size != info.numParams + info.numFields then return .continue
    let mut newArgs : Array (Option Expr) := #[]
    for _ in [0:info.numParams] do
      newArgs := newArgs.push none
    for a in ctorArgs[info.numParams:] do
      newArgs := newArgs.push (some (← mkAppM ``Witgen.FExpr.eval #[ctx, a]))
    let rhs ← mkAppOptM fn newArgs
    -- custom instances typically need `.all` transparency to reduce (cf. `Point.eval_eq`
    -- being proved by `with_unfolding_all rfl`); the kernel re-checks this unrestricted
    unless ← withTransparency .all (isDefEq e rhs) do return .continue
    return .visit { expr := rhs, proof? := none }
  catch _ => return .continue

simproc evalStructLiteral (Witgen.eval _ _) := evalStructLiteralSimproc
attribute [circuit_norm] evalStructLiteral
end Eval
end Witgen

export Witgen (WitgenIR)
