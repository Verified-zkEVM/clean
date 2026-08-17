import Clean.Circuit.WitnessIR
import Std.Data.HashMap

/-!
# Witness-IR subterm sharing (`WitgenIR.share`)

The witness-IR wire format supports sharing — a program is a list of scalar `let`-steps
referenced by `localVar`, so serialized programs can be DAGs — but nothing *produces*
steps from a tree-shaped payload: authored programs naturally build deeply shared Lean
terms, and `WitgenIR.toJson?` expands every shared subterm into a fresh copy.

On small gadgets this is invisible. On production-scale witnesses it is not: SP1's
64-bit DivRem chip (whose `c · quotient` block and carry chain reference the same
128-bit product machinery at every limb) serializes to **1.22 GB** of JSON — two single
witness programs at 552 MB each — for an authoring DAG of a few thousand nodes. An
external interpreter evaluating the unshared tree would pay the same blowup at runtime.

`WitgenIR.share` closes the gap: a bottom-up hash-consing pass that rebuilds a program
with every distinct non-trivial `FExpr`/`U64Expr` node interned as a `let`-step, so the
serialized size and the evaluation cost of the output are both proportional to the
number of *distinct* subterms. `WitgenIR.eval_share` (below) proves the transformation
preserves evaluation on every environment, so a serializer can apply it unconditionally.

Design notes:

- **Interning domain.** Only the two scalar sorts with a `Step` form (`letF`/`letU`) can
  be bound; `BExpr` has no step sort, so conditions are recursed through and their
  scalar children shared. Trivial nodes (`const`, `localVar`, `idx`) stay inline.
- **`mapRange` bodies are remapped, not interned.** The body of `VExpr.mapRange`
  re-binds `U64Expr.idx` per iteration; hoisting a subterm containing `idx` into a step
  (evaluated once, with `idx = 0`) would change its value. Bodies get a remap-only
  traversal that fixes up references to the original steps and otherwise leaves the
  tree alone. Everywhere else `idx` evaluates to `0` exactly as it does inside a step,
  so interning is value-preserving even for `idx`-containing subterms.
- **Original steps are renumbered.** Each original step is itself shared, and an
  old-index → replacement map rewrites `localVar` references in the rest of the
  program. A reference that was already dead under the original semantics (out of
  range, or reading a step of the other sort — both evaluate to `0`) is replaced by an
  explicit `const 0`.
- **The memo is an untrusted cache.** A memo hit is re-verified against the steps array
  (`beq` against the stored step's body) before it is used, so `eval_share` never has
  to reason about `Std.HashMap` internals — a (impossible) stale or colliding cache
  entry would only cost sharing, never correctness.
- **Hand-written `beq`/`hash`.** The `DecidableEq`/`Hashable` deriving handlers do not
  apply to this mutual + nested block, so the instances are written out; `beq_eq`
  (sound: `beq` implies `=`) and `beq_refl` are what the verification path and the
  cache hit rate rely on.
-/

variable {F : Type}

namespace Witgen

deriving instance DecidableEq for Variable
deriving instance Hashable for Variable
deriving instance DecidableEq for Expression
deriving instance Hashable for Expression

/-! ## Structural equality and hashing -/

section Beq
variable [DecidableEq F]

mutual

/-- Structural equality on field-sorted expressions. -/
def FExpr.beq : FExpr F → FExpr F → Bool
  | .expr a, .expr b => a = b
  | .const a, .const b => a = b
  | .localVar i, .localVar j => i == j
  | .add a b, .add c d => a.beq c && b.beq d
  | .mul a b, .mul c d => a.beq c && b.beq d
  | .inv a, .inv b => a.beq b
  | .ofU64 a, .ofU64 b => a.beq b
  | .ite c t e, .ite c' t' e' => c.beq c' && t.beq t' && e.beq e'
  | .listGet xs i, .listGet ys j => FExpr.beqList xs ys && i.beq j
  | .dataGet k n r c, .dataGet k' n' r' c' => k == k' && n == n' && r.beq r' && c.val == c'.val
  | .hintGet k n r c, .hintGet k' n' r' c' => k == k' && n == n' && r.beq r' && c.val == c'.val
  | _, _ => false

/-- Structural equality on expression lists (the `listGet` payload). -/
def FExpr.beqList : List (FExpr F) → List (FExpr F) → Bool
  | [], [] => true
  | x :: xs, y :: ys => x.beq y && FExpr.beqList xs ys
  | _, _ => false

/-- Structural equality on u64-sorted expressions. -/
def U64Expr.beq : U64Expr F → U64Expr F → Bool
  | .const a, .const b => a == b
  | .val a, .val b => a.beq b
  | .idx, .idx => true
  | .localVar i, .localVar j => i == j
  | .add a b, .add c d => a.beq c && b.beq d
  | .mul a b, .mul c d => a.beq c && b.beq d
  | .div a b, .div c d => a.beq c && b.beq d
  | .mod a b, .mod c d => a.beq c && b.beq d
  | .land a b, .land c d => a.beq c && b.beq d
  | .lor a b, .lor c d => a.beq c && b.beq d
  | .lxor a b, .lxor c d => a.beq c && b.beq d
  | .shiftL a b, .shiftL c d => a.beq c && b.beq d
  | .shiftR a b, .shiftR c d => a.beq c && b.beq d
  | .ite c t e, .ite c' t' e' => c.beq c' && t.beq t' && e.beq e'
  | _, _ => false

/-- Structural equality on conditions. -/
def BExpr.beq : BExpr F → BExpr F → Bool
  | .true, .true => true
  | .false, .false => true
  | .feq a b, .feq c d => a.beq c && b.beq d
  | .neq a b, .neq c d => a.beq c && b.beq d
  | .lt a b, .lt c d => a.beq c && b.beq d
  | .flt a b, .flt c d => a.beq c && b.beq d
  | .bit a i, .bit b j => a.beq b && i == j
  | .not a, .not b => a.beq b
  | .and a b, .and c d => a.beq c && b.beq d
  | _, _ => false

end

instance : BEq (FExpr F) := ⟨FExpr.beq⟩
instance : BEq (U64Expr F) := ⟨U64Expr.beq⟩
instance : BEq (BExpr F) := ⟨BExpr.beq⟩

end Beq

section Hash
variable [Hashable F]

mutual

/-- Structural hash on field-sorted expressions. -/
def FExpr.hashCode : FExpr F → UInt64
  | .expr e => mixHash 1 (hash e)
  | .const c => mixHash 2 (hash c)
  | .localVar i => mixHash 3 (hash i)
  | .add x y => mixHash 4 (mixHash x.hashCode y.hashCode)
  | .mul x y => mixHash 5 (mixHash x.hashCode y.hashCode)
  | .inv x => mixHash 6 x.hashCode
  | .ofU64 n => mixHash 7 n.hashCode
  | .ite c t e => mixHash 8 (mixHash c.hashCode (mixHash t.hashCode e.hashCode))
  | .listGet xs i => mixHash 9 (mixHash (FExpr.hashCodeList xs) i.hashCode)
  | .dataGet k n r c => mixHash 10 (mixHash (hash k) (mixHash (hash n) (mixHash r.hashCode (hash c.val))))
  | .hintGet k n r c => mixHash 11 (mixHash (hash k) (mixHash (hash n) (mixHash r.hashCode (hash c.val))))

/-- Structural hash on expression lists. -/
def FExpr.hashCodeList : List (FExpr F) → UInt64
  | [] => 12
  | x :: xs => mixHash x.hashCode (FExpr.hashCodeList xs)

/-- Structural hash on u64-sorted expressions. -/
def U64Expr.hashCode : U64Expr F → UInt64
  | .const n => mixHash 13 (hash n)
  | .val x => mixHash 14 x.hashCode
  | .idx => 15
  | .localVar i => mixHash 16 (hash i)
  | .add x y => mixHash 17 (mixHash x.hashCode y.hashCode)
  | .mul x y => mixHash 18 (mixHash x.hashCode y.hashCode)
  | .div x y => mixHash 19 (mixHash x.hashCode y.hashCode)
  | .mod x y => mixHash 20 (mixHash x.hashCode y.hashCode)
  | .land x y => mixHash 21 (mixHash x.hashCode y.hashCode)
  | .lor x y => mixHash 22 (mixHash x.hashCode y.hashCode)
  | .lxor x y => mixHash 23 (mixHash x.hashCode y.hashCode)
  | .shiftL x y => mixHash 24 (mixHash x.hashCode y.hashCode)
  | .shiftR x y => mixHash 25 (mixHash x.hashCode y.hashCode)
  | .ite c t e => mixHash 26 (mixHash c.hashCode (mixHash t.hashCode e.hashCode))

/-- Structural hash on conditions. -/
def BExpr.hashCode : BExpr F → UInt64
  | .true => 27
  | .false => 28
  | .feq x y => mixHash 29 (mixHash x.hashCode y.hashCode)
  | .neq x y => mixHash 30 (mixHash x.hashCode y.hashCode)
  | .lt x y => mixHash 31 (mixHash x.hashCode y.hashCode)
  | .flt x y => mixHash 32 (mixHash x.hashCode y.hashCode)
  | .bit x i => mixHash 33 (mixHash x.hashCode (hash i))
  | .not b => mixHash 34 b.hashCode
  | .and x y => mixHash 35 (mixHash x.hashCode y.hashCode)

end

instance : Hashable (FExpr F) := ⟨FExpr.hashCode⟩
instance : Hashable (U64Expr F) := ⟨U64Expr.hashCode⟩

end Hash

/-! ## The sharing pass -/

variable [DecidableEq F] [Hashable F] [Zero F]

/-- State of the sharing pass: the new steps built so far, memo tables from interned
node to its step index (untrusted caches — hits are re-verified against `steps`), and
the original-step replacement map (`.inl`/`.inr` following the original step's sort). -/
structure ShareState (F : Type) [DecidableEq F] [Hashable F] where
  steps : Array (Step F) := #[]
  memoF : Std.HashMap (FExpr F) ℕ := {}
  memoU : Std.HashMap (U64Expr F) ℕ := {}
  old : Array (FExpr F ⊕ U64Expr F) := #[]

/-- Intern a rebuilt field-sorted node: return an existing verified step reference, or
bind a fresh step. The memo is only a cache — a hit is used only after re-verifying
`beq` against the stored step's body. -/
def internF (e : FExpr F) : StateM (ShareState F) (FExpr F) := do
  let s ← get
  let hit? : Option ℕ :=
    match s.memoF[e]? with
    | some i =>
      if h : i < s.steps.size then
        match s.steps[i] with
        | .letF e' => if e'.beq e then some i else none
        | .letU _ => none
      else none
    | none => none
  match hit? with
  | some i => pure (.localVar i)
  | none =>
    let i := s.steps.size
    set { s with steps := s.steps.push (.letF e), memoF := s.memoF.insert e i }
    pure (.localVar i)

/-- Intern a rebuilt u64-sorted node (see `internF`). -/
def internU (e : U64Expr F) : StateM (ShareState F) (U64Expr F) := do
  let s ← get
  let hit? : Option ℕ :=
    match s.memoU[e]? with
    | some i =>
      if h : i < s.steps.size then
        match s.steps[i] with
        | .letU e' => if e'.beq e then some i else none
        | .letF _ => none
      else none
    | none => none
  match hit? with
  | some i => pure (.localVar i)
  | none =>
    let i := s.steps.size
    set { s with steps := s.steps.push (.letU e), memoU := s.memoU.insert e i }
    pure (.localVar i)

/-- Replacement for a reference to original step `i` from a field-sorted position:
the recorded replacement if step `i` existed with sort `letF`, else the `0` the
original semantics gave (out of range / sort mismatch). -/
def oldRefF (old : Array (FExpr F ⊕ U64Expr F)) (i : ℕ) : FExpr F :=
  match old[i]? with
  | some (.inl f) => f
  | _ => .const 0

/-- Replacement for a reference to original step `i` from a u64-sorted position. -/
def oldRefU (old : Array (FExpr F ⊕ U64Expr F)) (i : ℕ) : U64Expr F :=
  match old[i]? with
  | some (.inr u) => u
  | _ => .const 0

mutual

/-- Share a field-sorted expression: rebuild bottom-up with children replaced by their
shared forms, then intern the resulting node. `const` stays inline; `localVar` (a
reference to an *original* step) is replaced via the old-step map. -/
def shareF : FExpr F → StateM (ShareState F) (FExpr F)
  | .expr e => internF (.expr e)
  | .const c => pure (.const c)
  | .localVar i => do pure (oldRefF (← get).old i)
  | .add x y => do internF (.add (← shareF x) (← shareF y))
  | .mul x y => do internF (.mul (← shareF x) (← shareF y))
  | .inv x => do internF (.inv (← shareF x))
  | .ofU64 n => do internF (.ofU64 (← shareU n))
  | .ite c t e => do internF (.ite (← shareB c) (← shareF t) (← shareF e))
  | .listGet xs i => do internF (.listGet (← shareListF xs) (← shareU i))
  | .dataGet k n r c => do internF (.dataGet k n (← shareU r) c)
  | .hintGet k n r c => do internF (.hintGet k n (← shareU r) c)

/-- Share each expression of a `listGet` payload. -/
def shareListF : List (FExpr F) → StateM (ShareState F) (List (FExpr F))
  | [] => pure []
  | x :: xs => do pure ((← shareF x) :: (← shareListF xs))

/-- Share a u64-sorted expression (see `shareF`). -/
def shareU : U64Expr F → StateM (ShareState F) (U64Expr F)
  | .const n => pure (.const n)
  | .val x => do internU (.val (← shareF x))
  | .idx => pure .idx
  | .localVar i => do pure (oldRefU (← get).old i)
  | .add x y => do internU (.add (← shareU x) (← shareU y))
  | .mul x y => do internU (.mul (← shareU x) (← shareU y))
  | .div x y => do internU (.div (← shareU x) (← shareU y))
  | .mod x y => do internU (.mod (← shareU x) (← shareU y))
  | .land x y => do internU (.land (← shareU x) (← shareU y))
  | .lor x y => do internU (.lor (← shareU x) (← shareU y))
  | .lxor x y => do internU (.lxor (← shareU x) (← shareU y))
  | .shiftL x y => do internU (.shiftL (← shareU x) (← shareU y))
  | .shiftR x y => do internU (.shiftR (← shareU x) (← shareU y))
  | .ite c t e => do internU (.ite (← shareB c) (← shareU t) (← shareU e))

/-- Share the scalar children of a condition. Conditions themselves have no `Step`
sort, so they are recursed through, never interned. -/
def shareB : BExpr F → StateM (ShareState F) (BExpr F)
  | .true => pure .true
  | .false => pure .false
  | .feq x y => do pure (.feq (← shareF x) (← shareF y))
  | .neq x y => do pure (.neq (← shareU x) (← shareU y))
  | .lt x y => do pure (.lt (← shareU x) (← shareU y))
  | .flt x y => do pure (.flt (← shareF x) (← shareF y))
  | .bit x i => do pure (.bit (← shareF x) i)
  | .not b => do pure (.not (← shareB b))
  | .and x y => do pure (.and (← shareB x) (← shareB y))

end

mutual

/-- Reference-only remap for `mapRange` bodies: rewrite original-step references via
the old-step map, leave everything else in tree form. The body re-binds `U64Expr.idx`
per iteration, so its subterms cannot be hoisted into steps (which evaluate once, with
`idx = 0`). -/
def remapF (old : Array (FExpr F ⊕ U64Expr F)) : FExpr F → FExpr F
  | .expr e => .expr e
  | .const c => .const c
  | .localVar i => oldRefF old i
  | .add x y => .add (remapF old x) (remapF old y)
  | .mul x y => .mul (remapF old x) (remapF old y)
  | .inv x => .inv (remapF old x)
  | .ofU64 n => .ofU64 (remapU old n)
  | .ite c t e => .ite (remapB old c) (remapF old t) (remapF old e)
  | .listGet xs i => .listGet (remapListF old xs) (remapU old i)
  | .dataGet k n r c => .dataGet k n (remapU old r) c
  | .hintGet k n r c => .hintGet k n (remapU old r) c

/-- Reference-only remap for expression lists. -/
def remapListF (old : Array (FExpr F ⊕ U64Expr F)) : List (FExpr F) → List (FExpr F)
  | [] => []
  | x :: xs => remapF old x :: remapListF old xs

/-- Reference-only remap for u64-sorted expressions. -/
def remapU (old : Array (FExpr F ⊕ U64Expr F)) : U64Expr F → U64Expr F
  | .const n => .const n
  | .val x => .val (remapF old x)
  | .idx => .idx
  | .localVar i => oldRefU old i
  | .add x y => .add (remapU old x) (remapU old y)
  | .mul x y => .mul (remapU old x) (remapU old y)
  | .div x y => .div (remapU old x) (remapU old y)
  | .mod x y => .mod (remapU old x) (remapU old y)
  | .land x y => .land (remapU old x) (remapU old y)
  | .lor x y => .lor (remapU old x) (remapU old y)
  | .lxor x y => .lxor (remapU old x) (remapU old y)
  | .shiftL x y => .shiftL (remapU old x) (remapU old y)
  | .shiftR x y => .shiftR (remapU old x) (remapU old y)
  | .ite c t e => .ite (remapB old c) (remapU old t) (remapU old e)

/-- Reference-only remap for conditions. -/
def remapB (old : Array (FExpr F ⊕ U64Expr F)) : BExpr F → BExpr F
  | .true => .true
  | .false => .false
  | .feq x y => .feq (remapF old x) (remapF old y)
  | .neq x y => .neq (remapU old x) (remapU old y)
  | .lt x y => .lt (remapU old x) (remapU old y)
  | .flt x y => .flt (remapF old x) (remapF old y)
  | .bit x i => .bit (remapF old x) i
  | .not b => .not (remapB old b)
  | .and x y => .and (remapB old x) (remapB old y)

end

/-- Share the original steps in order, recording each one's replacement reference in
the old-step map (a step's body may only reference *earlier* original steps; later
references were already dead — `0` — and `oldRefF`/`oldRefU` reproduce that). -/
def shareSteps : List (Step F) → StateM (ShareState F) Unit
  | [] => pure ()
  | .letF e :: rest => do
    let r ← shareF e
    modify fun s => { s with old := s.old.push (.inl r) }
    shareSteps rest
  | .letU e :: rest => do
    let r ← shareU e
    modify fun s => { s with old := s.old.push (.inr r) }
    shareSteps rest

/-- Share a vector-shaped output. `mapRange` bodies are remapped only (see `remapF`). -/
def shareV : {n : ℕ} → VExpr F n → StateM (ShareState F) (VExpr F n)
  | _, .lit es => do pure (.lit (← es.mapM shareF))
  | _, .mapRange n body => do pure (.mapRange n (remapF (← get).old body))
  | _, .envRange offset => pure (.envRange offset)
  | _, .bitsOf x => do pure (.bitsOf (← shareF x))
  | _, .append a b => do pure (.append (← shareV a) (← shareV b))

/-- Rebuild a witness program with every distinct non-trivial scalar subterm interned
as a `let`-step, so that serialized size and external evaluation cost are proportional
to the number of *distinct* subterms rather than the tree size.
`eval_share` proves the rebuilt program evaluates identically. -/
def WitgenIR.share {m : ℕ} : WitgenIR F m → WitgenIR F m
  | .native f => .native f
  | .ir steps out =>
    let (out', s) := (do shareSteps steps; shareV out : StateM (ShareState F) _).run {}
    .ir s.steps.toList out'

end Witgen
