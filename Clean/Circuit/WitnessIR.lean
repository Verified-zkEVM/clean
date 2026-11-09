import Clean.Circuit.Expression
import Clean.Utils.Field
import Clean.Utils.FiniteField
import Clean.Utils.Vector
import Clean.Circuit.Provable

open Clean

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
`field → ZMod.val → Nat ops → cast → field` pattern:
- `FExpr` — field-sorted: embedded circuit `Expression`s (which is how callbacks read
  inputs and earlier witnesses), env reads at computed indices, arithmetic, inverse
  (IsZeroField), conditionals, constant-table reads, prover-data/hint reads.
- `NExpr` — Nat-sorted: arithmetic, div/mod, bitwise ops, shifts; bridges are
  `NExpr.val : FExpr → NExpr` and `FExpr.ofNat : NExpr → FExpr`.
- `BExpr` — conditions: field equality and Nat comparison (requirement B.7).

The output is a `VExpr`: a literal list, a `mapRange n body` (body may reference the
running index via `NExpr.idx`) — kept as a *loop* rather than unrolled — or an append.

## TOOD Potential open issues

1. **One index binder.** `NExpr.idx` refers to the innermost enclosing `VExpr.mapRange`;
   nesting shadows. No surveyed gadget nests mapRanges inside a single callback. If that
   changes, `idx` generalizes to de Bruijn levels.
2. **Untyped locals.** `localVar i` is resolved in an `F ⊕ ℕ` array with a 0 default on
   sort mismatch / out of range, keeping `eval` total without intrinsically-typed
   syntax. A decidable well-sortedness check can be layered on top later (it will be
   needed for serialization anyway).
-/

variable {F V Env : Type}

namespace Witgen

mutual

/-- Field-sorted witness expressions, generic over the variable atom `V` — how programs
read circuit variables. Main Clean instantiates `V := Expression F` (see the `FExpr`
abbreviation); Halo2-Clean instantiates `V := AssignedCell F`. -/
inductive FExprOver (F : Type) (V : Type) where
  /-- Embedded circuit variable; this is how callbacks read input vars and earlier
  witnesses (`env x`). -/
  | expr (e : V)
  /-- Read the environment at a computed index (e.g. consecutive vars in a mapRange).
  Main-Clean-specific (tape indices); inert in environments without indexed reads. -/
  | envGet (i : NExprOver F V)
  | const (c : F)
  /-- Reference to an earlier `Step` result (must be a `letF` step). -/
  | localVar (i : ℕ)
  | add (x y : FExprOver F V)
  | mul (x y : FExprOver F V)
  /-- Field inverse, with `0⁻¹ = 0` (the `IsZeroField` witness). -/
  | inv (x : FExprOver F V)
  /-- Cast from the Nat sort via `FiniteField.fromNat` (the inverse of `val`;
  equals `Nat.cast` on prime fields, but interprets binary digits as coefficients
  on binary fields, where `Nat.cast` would collapse via the characteristic). -/
  | ofNat (n : NExprOver F V)
  | ite (c : BExprOver F V) (t e : FExprOver F V)
  /-- Read an expression list at a computed index, 0 if out of range -/
  | listGet (xs : List (FExprOver F V)) (i : NExprOver F V)
  /-- Read committed prover data (`Environment.data`), keyed like `ProverData`:
  row `row` of table `key` with rows of width `n`, projected at column `col`.
  Missing rows read as 0. The nondeterministic escape hatch (FemtoCairo memory).
  Main-Clean-specific; inert in environments without committed prover data. -/
  | dataGet (key : String) (n : ℕ) (row : NExprOver F V) (col : Fin n)
  /-- Same as `dataGet` but reads the uncommitted `ProverEnvironment.hint`. -/
  | hintGet (key : String) (n : ℕ) (row : NExprOver F V) (col : Fin n)

/-- Nat-sorted witness expressions. -/
inductive NExprOver (F : Type) (V : Type) where
  | const (n : ℕ)
  /-- The field→Nat bridge (`ZMod.val`). -/
  | val (x : FExprOver F V)
  /-- The index of the innermost enclosing `VExpr.mapRange` (0 outside). -/
  | idx
  /-- Reference to an earlier `Step` result (must be a `letN` step). -/
  | localVar (i : ℕ)
  | add (x y : NExprOver F V)
  | mul (x y : NExprOver F V)
  | div (x y : NExprOver F V)
  | mod (x y : NExprOver F V)
  | land (x y : NExprOver F V)
  | lor (x y : NExprOver F V)
  | lxor (x y : NExprOver F V)
  | shiftL (x y : NExprOver F V)
  | shiftR (x y : NExprOver F V)
  | ite (c : BExprOver F V) (t e : NExprOver F V)

/-- Conditions. -/
inductive BExprOver (F : Type) (V : Type) where
  | true
  | false
  /-- Field equality condition (decided via the injective `ℕ` embedding). -/
  | feq (x y : FExprOver F V)
  /-- Nat equality condition. -/
  | neq (x y : NExprOver F V)
  /-- Nat-sorted less-than condition. -/
  | lt (x y : NExprOver F V)
  /-- Negation of a condition. -/
  | not (b : BExprOver F V)
  /-- Conjunction of conditions. -/
  | and (x y : BExprOver F V)

end

/-- `x - y` as a derived field expression. -/
@[reducible] def FExprOver.sub [Field F] (x y : FExprOver F V) : FExprOver F V :=
  .add x (.mul (.const (-1)) y)

/-- `-x` as a derived field expression. -/
@[reducible] def FExprOver.neg [Field F] (x : FExprOver F V) : FExprOver F V :=
  .mul (.const (-1)) x

/-- `2^k` as a derived Nat expression. -/
@[reducible] def NExprOver.pow2 (k : NExprOver F V) : NExprOver F V := .shiftL (.const 1) k

/-- `Nat.testBit x i` as a derived Nat expression, valued in {0, 1}. -/
@[reducible] def NExprOver.testBit (x i : NExprOver F V) : NExprOver F V :=
  .mod (.shiftR x i) (.const 2)

end Witgen

namespace Clean
open Witgen

/-- Main Clean's field-sorted witness expressions: variables are circuit `Expression`s. -/
abbrev FExpr (F : Type) := FExprOver F (Expression F)
/-- Main Clean's Nat-sorted witness expressions. -/
abbrev NExpr (F : Type) := NExprOver F (Expression F)
/-- Main Clean's witness conditions. -/
abbrev BExpr (F : Type) := BExprOver F (Expression F)

namespace FExpr
export FExprOver (expr envGet const localVar add mul inv ofNat ite listGet dataGet hintGet)
end FExpr

namespace NExpr
export NExprOver (const val idx localVar add mul div mod land lor lxor shiftL shiftR ite)
end NExpr

namespace BExpr
export BExprOver (true false feq neq lt not and)
end BExpr

end Clean

namespace Witgen

/-- Evaluation context: the prover environment, the values of the `let`-steps computed
so far, and the innermost `mapRange` index. Generic over the environment type. -/
structure CtxOver (F : Type) (Env : Type) where
  env : Env
  locals : Array (F ⊕ ℕ) := #[]
  idx : ℕ := 0

/--
How witness programs read from an environment: the variable-atom valuation plus the
indexed/data/hint reads. Main Clean instantiates this at
`(ProverEnvironment F, Expression F)`; Halo2-Clean at its placed environments and cell
atoms (with `get`/`data` inert).
-/
class WitgenEnv (F : Type) (Env : Type) (V : Type) where
  readVar : Env → V → F
  get : Env → ℕ → F
  data : Env → ProverData F
  hint : Env → ProverHint F

end Witgen

namespace Clean
open Witgen

/-- Main Clean's evaluation context. -/
abbrev Ctx (F : Type) := CtxOver F (ProverEnvironment F)

@[reducible] instance instWitgenEnv [Field F] :
    WitgenEnv F (ProverEnvironment F) (Expression F) where
  readVar env e := e.eval env.toEnvironment
  get env := env.get
  data env := env.data
  hint env := env.hint

/- Main-instance reads normalize back to their pre-generalization spellings, so the
existing `circuit_norm` lemma ecosystem keeps matching. -/
namespace WitgenEnv

@[circuit_norm] lemma readVar_eq [Field F] (env : ProverEnvironment F)
    (e : Expression F) : WitgenEnv.readVar env e = e.eval env.toEnvironment := rfl
@[circuit_norm] lemma get_eq [Field F] (env : ProverEnvironment F) (i : ℕ) :
    WitgenEnv.get (V := Expression F) env i = env.get i := rfl
@[circuit_norm] lemma data_eq [Field F] (env : ProverEnvironment F) :
    WitgenEnv.data (V := Expression F) env = env.data := rfl
@[circuit_norm] lemma hint_eq [Field F] (env : ProverEnvironment F) :
    WitgenEnv.hint (V := Expression F) env = env.hint := rfl

end WitgenEnv
end Clean

namespace Witgen

section Eval
variable [FiniteField F] [WitgenEnv F Env V]

mutual

@[circuit_norm]
def FExprOver.eval (ctx : CtxOver F Env) : FExprOver F V → F
  | .expr e => WitgenEnv.readVar ctx.env e
  | .envGet i => WitgenEnv.get (V := V) ctx.env (i.eval ctx)
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
  | .listGet xs i => FExprOver.evalList ctx (i.eval ctx) xs
  | .dataGet key n row col =>
    ((WitgenEnv.data (V := V) ctx.env key n)[row.eval ctx]?.getD default)[col.val]'col.isLt
  | .hintGet key n row col =>
    ((WitgenEnv.hint (V := V) ctx.env key n)[row.eval ctx]?.getD default)[col.val]'col.isLt

@[circuit_norm]
def FExprOver.evalList (ctx : CtxOver F Env) : ℕ → List (FExprOver F V) → F
  | _, [] => 0
  | 0, x :: _ => x.eval ctx
  | i + 1, _ :: xs => FExprOver.evalList ctx i xs

@[circuit_norm]
def NExprOver.eval (ctx : CtxOver F Env) : NExprOver F V → ℕ
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
def BExprOver.eval (ctx : CtxOver F Env) : BExprOver F V → Bool
  | .true => true
  | .false => false
  | .feq x y => x.eval ctx = y.eval ctx
  | .neq x y => x.eval ctx = y.eval ctx
  | .lt x y => x.eval ctx < y.eval ctx
  | .not b => !b.eval ctx
  | .and x y => x.eval ctx && y.eval ctx

end

variable {M : TypeMap} [ProvableType M]

/-- Evaluation for higher-level provable types. -/
def eval (ctx : CtxOver F Env) (x : M (FExprOver F V)) : M F :=
  toElements x |> Vector.map (FExprOver.eval ctx) |> fromElements

@[circuit_norm]
lemma eval_field (ctx : CtxOver F Env) (x : FExprOver F V) :
    Witgen.eval (M := field) ctx x = FExprOver.eval ctx x := by
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
inductive VExprOver (F : Type) (V : Type) : ℕ → Type where
  | lit {n : ℕ} (es : Vector (FExprOver F V) n) : VExprOver F V n
  | mapRange (n : ℕ) (body : FExprOver F V) : VExprOver F V n
  | append {m n : ℕ} (a : VExprOver F V m) (b : VExprOver F V n) : VExprOver F V (m + n)

instance {n} : Coe (Vector (FExprOver F V) n) (VExprOver F V n) where
  coe es := .lit es

def VExprOver.eval [FiniteField F] [WitgenEnv F Env V] (ctx : CtxOver F Env) :
    {n : ℕ} → VExprOver F V n → Vector F n
  | _, .lit es => es.map (FExprOver.eval ctx)
  | _, .mapRange n body => .mapRange n fun i => body.eval { ctx with idx := i }
  | _, .append a b => a.eval ctx ++ b.eval ctx

end Witgen

namespace Clean
open Witgen

/-- Main Clean's vector-shaped witness outputs. -/
abbrev VExpr (F : Type) := VExprOver F (Expression F)

namespace VExpr
export VExprOver (lit mapRange append)
end Clean.VExpr

namespace Witgen

/-- A scalar `let`-step: computes one field or Nat value from the environment and
earlier steps. Referenced by position via `localVar`. -/
inductive StepOver (F : Type) (V : Type) where
  | letF (e : FExprOver F V)
  | letN (e : NExprOver F V)

end Witgen

namespace Clean
open Witgen

/-- Main Clean's `let`-steps. -/
abbrev Step (F : Type) := StepOver F (Expression F)

namespace Step
export StepOver (letF letN)
end Clean.Step

namespace Witgen

/-- Evaluate the `let`-steps left to right, accumulating their values. -/
@[circuit_norm]
def evalSteps [FiniteField F] [WitgenEnv F Env V] (env : Env)
    (steps : List (StepOver F V)) (locals : Array (F ⊕ ℕ) := #[]) : Array (F ⊕ ℕ) :=
  match steps with
  | [] => locals
  | .letF e :: steps => evalSteps env steps (locals.push (.inl (e.eval { env, locals })))
  | .letN e :: steps => evalSteps env steps (locals.push (.inr (e.eval { env, locals })))

/-- A witness-generation program producing `m` field elements. -/
inductive WitgenIROver (F : Type) (Env : Type) (V : Type) : ℕ → Type where
  /-- Arbitrary Lean closure — migration escape hatch, not serializable.
  `eval (native f) = f` holds definitionally. -/
  | native {m : ℕ} (f : Env → Vector F m) : WitgenIROver F Env V m
  /-- Structured straight-line program: `let`-steps, then a vector output. -/
  | ir {m : ℕ} (steps : List (StepOver F V)) (out : VExprOver F V m) : WitgenIROver F Env V m

def WitgenIROver.eval {m : ℕ} [FiniteField F] [WitgenEnv F Env V] :
    WitgenIROver F Env V m → Env → Vector F m
  | .native f => f
  | .ir steps out => fun env =>
    out.eval { env, locals := evalSteps env steps }

end Witgen

namespace Clean
open Witgen

/-- Main Clean's witness-generation programs. -/
abbrev WitgenIR (F : Type) :=
  WitgenIROver F (ProverEnvironment F) (Expression F)

namespace WitgenIR
export WitgenIROver (native ir)

@[circuit_norm]
theorem eval_native {m : ℕ} [FiniteField F]
    (f : ProverEnvironment F → Vector F m) : (WitgenIR.native f : WitgenIR F m).eval = f := rfl

@[circuit_norm]
theorem eval_native_apply {m : ℕ} [FiniteField F]
    (f : ProverEnvironment F → Vector F m) (env : ProverEnvironment F) :
    (WitgenIR.native f : WitgenIR F m).eval env = f env := rfl

end WitgenIR
end Clean

namespace Witgen

/-!
## Smart constructors

The base building blocks used by the IR-based witness entry points
(`witnessField`, `witnessVector`, `witnessIR`) and by `<==`.
Their `eval` lemmas are tagged `circuit_norm` so that IR-built witnesses
simp-normalize to exactly the same hypothesis shapes as the closures they replace.
-/

/-- Witness program producing a single scalar from a field-sorted IR expression. -/
def WitgenIROver.ofFExpr (e : FExprOver F V) : WitgenIROver F Env V 1 := .ir [] (.lit #v[e])

/-- Witness program computing each output element from its own IR expression. -/
def WitgenIROver.ofFExprs {n : ℕ} (es : Vector (FExprOver F V) n) : WitgenIROver F Env V n :=
  .ir [] (.lit es)

end Witgen

namespace Clean
open Witgen

namespace WitgenIR
export WitgenIROver (ofFExpr ofFExprs)

/-- Witness program computing a whole provable value from a native Lean closure — the
payload of `witnessNative`. A named definition (rather than an inline `.native` lambda)
so that the completeness obligation of `witnessNative` stays recognizable and can be
rewritten at the level of provable values (`ProverEnvironment.extendsVector_nativeValue`
in `Clean.Circuit.Basic`) instead of unfolding element-wise into `toElements` internals.
For the same reason, this is deliberately not tagged `@[circuit_norm]`. -/
def nativeValue {value : TypeMap} [ProvableType value]
    (compute : ProverEnvironment F → value F) : WitgenIR F (size value) :=
  .native fun env => compute env |> toElements

theorem eval_nativeValue [FiniteField F] {value : TypeMap} [ProvableType value]
    (compute : ProverEnvironment F → value F) (env : ProverEnvironment F) :
    (nativeValue compute).eval env = toElements (compute env) := rfl

end WitgenIR

/-- `Witgen.eval` on `fields n` is elementwise evaluation (the witgen analogue of
`ProvableType.Clean.eval_fields`). -/
theorem eval_fields' [FiniteField F] {n : ℕ} (ctx : Ctx F) (xs : Vector (FExpr F) n) :
    Witgen.eval (M := fields n) ctx xs = xs.map (FExprOver.eval ctx) := rfl

/-- Vector analogue of the `evalProjection` simproc: evaluating one element of a vector
of IR expressions is one element of the evaluated vector. Lifts stuck element reads of
*opaque* vectors (e.g. per-index reads of an `Unconstrained (fields n)` hint) to the
vector level, where row-level facts (`h_input` equations) can consume them. Stated as a
post-rewrite so that literal vectors reduce first (`Vector.getElem_ofFn` etc.) and never
reach this lemma. -/
@[circuit_norm]
theorem FExpr.eval_getElem [FiniteField F] {n : ℕ} (ctx : Ctx F)
    (xs : Vector (FExpr F) n) (i : ℕ) (hi : i < n) :
    FExprOver.eval ctx xs[i] = (Witgen.eval (M := fields n) ctx xs)[i] := by
  rw [eval_fields', Vector.getElem_map]

/-- Witness program copying the values of given circuit expressions (used by `<==`). -/
def WitgenIR.ofExprs {n : ℕ} (es : Vector (Expression F) n) : WitgenIR F n :=
  .ir [] (.lit (es.map .expr))

@[circuit_norm]
theorem WitgenIR.eval_ofFExpr [FiniteField F] (e : FExpr F) (env : ProverEnvironment F) :
    (ofFExpr e).eval env = #v[e.eval { env }] := by
  ext i hi
  rcases Nat.lt_one_iff.mp hi
  simp [ofFExpr, WitgenIROver.eval, VExprOver.eval, evalSteps]

theorem WitgenIR.eval_ofExprs [FiniteField F] {n : ℕ} (es : Vector (Expression F) n)
    (env : ProverEnvironment F) :
    (ofExprs es).eval env = es.map (Expression.eval env.toEnvironment) := by
  ext i hi
  simp [ofExprs, WitgenIROver.eval, VExprOver.eval, FExprOver.eval, evalSteps, WitgenEnv.readVar_eq]

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
    (VExprOver.eval ctx (.mapRange n body))[i] = body.eval { ctx with idx := i } := by
  simp [VExprOver.eval, Vector.getElem_mapRange]

/-- Elementwise evaluation of literal vector outputs, keyed on the eval term. -/
@[circuit_norm ↓]
theorem VExpr.getElem_eval_lit [FiniteField F] {n : ℕ} (ctx : Ctx F)
    (es : Vector (FExpr F) n) (i : ℕ) (hi : i < n) :
    (VExprOver.eval ctx (.lit es))[i] = es[i].eval ctx := by
  simp [VExprOver.eval]

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
  simp [ofFExpr, WitgenIROver.eval, VExprOver.eval, evalSteps]

/-- Elementwise evaluation of multi-element witness programs, keyed on `getElem`. -/
@[circuit_norm ↓]
theorem WitgenIR.getElem_eval_ofFExprs [FiniteField F] {n : ℕ} (es : Vector (FExpr F) n)
    (env : ProverEnvironment F) (i : ℕ) (hi : i < n) :
    ((ofFExprs es).eval env)[i] = es[i].eval { env } := by
  simp [ofFExprs, WitgenIROver.eval, VExprOver.eval, evalSteps]

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
  simp only [BExprOver.eval, decide_eq_true_eq]

/-- Shape-exact evaluation for expression-copying scalar witnesses (`<==`):
produces the same normal form as the closure it replaced. -/
@[circuit_norm]
theorem WitgenIR.eval_ofFExpr_expr [FiniteField F] (e : Expression F)
    (env : ProverEnvironment F) :
    (ofFExpr (.expr e)).eval env = #v[e.eval env.toEnvironment] := by
  ext i hi
  rcases Nat.lt_one_iff.mp hi
  simp [ofFExpr, WitgenIROver.eval, VExprOver.eval, FExprOver.eval, evalSteps, WitgenEnv.readVar_eq]

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
  rw [WitgenIR.eval_ofExprs, ProvableType.Clean.toElements_eval]

end Clean

namespace Witgen

/-!
## Eval-simplification tooling
-/

section Eval
variable [FiniteField F] [WitgenEnv F Env V] {M : TypeMap} [ProvableStruct M]

namespace StructEval
/-- Struct-preserving evaluation for witness-IR expressions. -/
@[circuit_norm]
def eval (ctx : CtxOver F Env) (var : M (FExprOver F V)) : M F :=
  toComponents var |> go (components M) |> fromComponents
where
  @[circuit_norm]
  go : (cs : List _root_.ProvableStruct.WithProvableType) →
      _root_.ProvableStruct.ProvableTypeList (FExprOver F V) cs →
        _root_.ProvableStruct.ProvableTypeList F cs
    | [], .nil => .nil
    | _ :: cs, .cons a as => .cons (Witgen.eval ctx a) (go cs as)

theorem eval_eq_eval {M : TypeMap} [ProvableStruct M] (ctx : CtxOver F Env) (x : M (FExprOver F V)) :
    Witgen.eval ctx x = StructEval.eval ctx x := by
  symm
  simp only [Witgen.eval, eval, fromElements, toElements, size]
  congr 1
  apply eval_eq_eval_aux
where
  eval_eq_eval_aux (ctx : CtxOver F Env) : (cs : List _root_.ProvableStruct.WithProvableType) →
      (as : _root_.ProvableStruct.ProvableTypeList (FExprOver F V) cs) →
    eval.go ctx cs as =
      (_root_.ProvableStruct.componentsToElements cs as |> Vector.map (FExprOver.eval ctx) |>
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
  -- The simproc is registered on `Witgen.FExprOver.eval _ _`; the last two explicit arguments are
  -- the evaluation context and the scalar expression being evaluated.
  let args := e.getAppArgs
  unless e.getAppFn.isConstOf ``Witgen.FExprOver.eval && args.size >= 2 do
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
    -- custom-`ProvableType` route (e.g. `Point`): the internal `ProvableStruct` set cannot
    -- reduce the candidate, but the rewrite is still definitionally sound — accept by
    -- unrestricted defeq, the kernel re-checks (cf. `evalStructLiteral`'s custom route).
    if ← withTransparency .all (isDefEq rhs e) then
      return .done { expr := rhs, proof? := none }
    return Simp.Step.continue

  -- `rhsSimp` proves `rhs = e`; the simproc must return a proof of `e = rhs`.
  -- Return `.done` rather than `.visit` so the outer simplifier keeps the row-level shape and can
  -- continue from there, instead of immediately descending back into scalar projections.
  let result ← rhsSimp.mkEqSymm rhs
  return .done result

simproc evalProjection (Witgen.FExprOver.eval _ _) := evalProjectionSimproc
attribute [circuit_norm] evalProjection

open Lean Meta Simp in
/--
Evaluate witness-IR *struct literals* component-wise.

`Witgen.eval ctx s`, where `s` is a literal constructor application of a `ProvableStruct`
type, decomposes into per-component evaluations (via `StructEval.eval`) — mirroring the
component-preserving normal form of the regular `ProvableStruct.Clean.eval`. This is the shape
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
      newArgs := newArgs.push (some (← mkAppM ``Witgen.FExprOver.eval #[ctx, a]))
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
