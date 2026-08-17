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

section Pass
variable [DecidableEq F] [Hashable F] [Zero F]

/-- State of the sharing pass: the new steps built so far, memo tables from interned
node to its step index (untrusted caches — hits are re-verified against `steps`), and
the original-step replacement map (`.inl`/`.inr` following the original step's sort). -/
structure ShareState (F : Type) [DecidableEq F] [Hashable F] where
  steps : Array (Step F) := #[]
  memoF : Std.HashMap (FExpr F) ℕ := {}
  memoU : Std.HashMap (U64Expr F) ℕ := {}
  old : Array (FExpr F ⊕ U64Expr F) := #[]

/-- Bind a fresh field-sorted step for `e` and return its reference. -/
def internFreshF (e : FExpr F) (s : ShareState F) : FExpr F × ShareState F :=
  (.localVar s.steps.size,
    { s with steps := s.steps.push (.letF e), memoF := s.memoF.insert e s.steps.size })

/-- Bind a fresh u64-sorted step for `e` and return its reference. -/
def internFreshU (e : U64Expr F) (s : ShareState F) : U64Expr F × ShareState F :=
  (.localVar s.steps.size,
    { s with steps := s.steps.push (.letU e), memoU := s.memoU.insert e s.steps.size })

/-- Intern a rebuilt field-sorted node: return an existing verified step reference, or
bind a fresh step. The memo is only a cache — a hit is used only after re-verifying
`beq` against the stored step's body, so correctness never depends on the `HashMap`. -/
def internF (e : FExpr F) : StateM (ShareState F) (FExpr F) := fun s =>
  match s.memoF[e]? with
  | some i =>
    if h : i < s.steps.size then
      match s.steps[i] with
      | .letF e' => if e'.beq e then (.localVar i, s) else internFreshF e s
      | .letU _ => internFreshF e s
    else internFreshF e s
  | none => internFreshF e s

/-- Intern a rebuilt u64-sorted node (see `internF`). -/
def internU (e : U64Expr F) : StateM (ShareState F) (U64Expr F) := fun s =>
  match s.memoU[e]? with
  | some i =>
    if h : i < s.steps.size then
      match s.steps[i] with
      | .letU e' => if e'.beq e then (.localVar i, s) else internFreshU e s
      | .letF _ => internFreshU e s
    else internFreshU e s
  | none => internFreshU e s

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

/-- Share a u64-sorted expression (see `shareF`). Every position this traversal
reaches evaluates at `idx = 0` (`mapRange` bodies — the only `idx`-binding positions —
are handled by `remapU`, never by this), so `.idx` is rewritten to its value `0`
outright; keeping it symbolic would be wrong where the old-step map substitutes it
into a `mapRange` body, which re-binds `idx`. -/
def shareU : U64Expr F → StateM (ShareState F) (U64Expr F)
  | .const n => pure (.const n)
  | .val x => do internU (.val (← shareF x))
  | .idx => pure (.const 0)
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

/-- `shareListF` preserves length (needed to rebuild a `Vector` in `shareV`). -/
theorem shareListF_length : ∀ (xs : List (FExpr F)) (s : ShareState F),
    (shareListF xs s).1.length = xs.length
  | [], _ => rfl
  | x :: xs, s => by
    show ((shareF x s).1 :: (shareListF xs (shareF x s).2).1).length = xs.length + 1
    simp [shareListF_length xs]

/-- Share a vector-shaped output. `mapRange` bodies are remapped only (see `remapF`). -/
def shareV : {n : ℕ} → VExpr F n → StateM (ShareState F) (VExpr F n)
  | _, .lit es => fun s =>
    match h : shareListF es.toList s with
    | (rs, s') =>
      (.lit ⟨rs.toArray, by
        have hrs : rs = (shareListF es.toList s).1 := (congrArg Prod.fst h).symm
        rw [List.size_toArray, hrs, shareListF_length, Vector.length_toList]⟩, s')
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

end Pass

/-! ## `beq` soundness

`beq_eq` is what the intern verification path relies on: a memo hit is accepted only
after a `beq` re-check against the stored step's body, and `beq_eq` turns that check
into a genuine equality. (The converse direction is not needed for correctness — a
`beq` false-negative would only cost sharing — so it is not proved.) -/

section BeqEq
variable [DecidableEq F]

mutual

/-- `beq` implies equality. -/
theorem FExpr.beq_eq : ∀ (a b : FExpr F), FExpr.beq a b = true → a = b
  | .expr a, b, h => by
    cases b <;> simp only [FExpr.beq, Bool.false_eq_true, decide_eq_true_eq] at h
    case expr b => exact congrArg FExpr.expr h
  | .const a, b, h => by
    cases b <;> simp only [FExpr.beq, Bool.false_eq_true, decide_eq_true_eq] at h
    case const b => exact congrArg FExpr.const h
  | .localVar i, b, h => by
    cases b <;> simp only [FExpr.beq, Bool.false_eq_true, beq_iff_eq] at h
    case localVar j => exact congrArg FExpr.localVar h
  | .add x y, b, h => by
    cases b <;> simp only [FExpr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case add c d => rw [FExpr.beq_eq x c h.1, FExpr.beq_eq y d h.2]
  | .mul x y, b, h => by
    cases b <;> simp only [FExpr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case mul c d => rw [FExpr.beq_eq x c h.1, FExpr.beq_eq y d h.2]
  | .inv x, b, h => by
    cases b <;> simp only [FExpr.beq, Bool.false_eq_true] at h
    case inv y => rw [FExpr.beq_eq x y h]
  | .ofU64 u, b, h => by
    cases b <;> simp only [FExpr.beq, Bool.false_eq_true] at h
    case ofU64 v => rw [U64Expr.beq_eq u v h]
  | .ite c t e, b, h => by
    cases b <;> simp only [FExpr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case ite c' t' e' =>
      rw [BExpr.beq_eq c c' h.1.1, FExpr.beq_eq t t' h.1.2, FExpr.beq_eq e e' h.2]
  | .listGet xs i, b, h => by
    cases b <;> simp only [FExpr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case listGet ys j => rw [FExpr.beqList_eq xs ys h.1, U64Expr.beq_eq i j h.2]
  | .dataGet k n r c, b, h => by
    cases b <;> simp only [FExpr.beq, Bool.false_eq_true, Bool.and_eq_true,
      beq_iff_eq] at h
    case dataGet k' n' r' c' =>
      obtain ⟨⟨⟨hk, hn⟩, hr⟩, hc⟩ := h
      subst hk; subst hn
      cases U64Expr.beq_eq r r' hr
      exact congrArg (FExpr.dataGet k n r) (Fin.ext hc)
  | .hintGet k n r c, b, h => by
    cases b <;> simp only [FExpr.beq, Bool.false_eq_true, Bool.and_eq_true,
      beq_iff_eq] at h
    case hintGet k' n' r' c' =>
      obtain ⟨⟨⟨hk, hn⟩, hr⟩, hc⟩ := h
      subst hk; subst hn
      cases U64Expr.beq_eq r r' hr
      exact congrArg (FExpr.hintGet k n r) (Fin.ext hc)

/-- `beqList` implies equality. -/
theorem FExpr.beqList_eq : ∀ (xs ys : List (FExpr F)), FExpr.beqList xs ys = true → xs = ys
  | [], [], _ => rfl
  | [], _ :: _, h => by simp only [FExpr.beqList, Bool.false_eq_true] at h
  | _ :: _, [], h => by simp only [FExpr.beqList, Bool.false_eq_true] at h
  | x :: xs, y :: ys, h => by
    simp only [FExpr.beqList, Bool.and_eq_true] at h
    rw [FExpr.beq_eq x y h.1, FExpr.beqList_eq xs ys h.2]

/-- `beq` implies equality. -/
theorem U64Expr.beq_eq : ∀ (a b : U64Expr F), U64Expr.beq a b = true → a = b
  | .const a, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true, beq_iff_eq] at h
    case const b => exact congrArg U64Expr.const h
  | .val x, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true] at h
    case val y => rw [FExpr.beq_eq x y h]
  | .idx, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true] at h
    case idx => rfl
  | .localVar i, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true, beq_iff_eq] at h
    case localVar j => exact congrArg U64Expr.localVar h
  | .add x y, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case add c d => rw [U64Expr.beq_eq x c h.1, U64Expr.beq_eq y d h.2]
  | .mul x y, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case mul c d => rw [U64Expr.beq_eq x c h.1, U64Expr.beq_eq y d h.2]
  | .div x y, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case div c d => rw [U64Expr.beq_eq x c h.1, U64Expr.beq_eq y d h.2]
  | .mod x y, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case mod c d => rw [U64Expr.beq_eq x c h.1, U64Expr.beq_eq y d h.2]
  | .land x y, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case land c d => rw [U64Expr.beq_eq x c h.1, U64Expr.beq_eq y d h.2]
  | .lor x y, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case lor c d => rw [U64Expr.beq_eq x c h.1, U64Expr.beq_eq y d h.2]
  | .lxor x y, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case lxor c d => rw [U64Expr.beq_eq x c h.1, U64Expr.beq_eq y d h.2]
  | .shiftL x y, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case shiftL c d => rw [U64Expr.beq_eq x c h.1, U64Expr.beq_eq y d h.2]
  | .shiftR x y, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case shiftR c d => rw [U64Expr.beq_eq x c h.1, U64Expr.beq_eq y d h.2]
  | .ite c t e, b, h => by
    cases b <;> simp only [U64Expr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case ite c' t' e' =>
      rw [BExpr.beq_eq c c' h.1.1, U64Expr.beq_eq t t' h.1.2, U64Expr.beq_eq e e' h.2]

/-- `beq` implies equality. -/
theorem BExpr.beq_eq : ∀ (a b : BExpr F), BExpr.beq a b = true → a = b
  | .true, b, h => by
    cases b <;> simp only [BExpr.beq, Bool.false_eq_true] at h
    case true => rfl
  | .false, b, h => by
    cases b <;> simp only [BExpr.beq, Bool.false_eq_true] at h
    case false => rfl
  | .feq x y, b, h => by
    cases b <;> simp only [BExpr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case feq c d => rw [FExpr.beq_eq x c h.1, FExpr.beq_eq y d h.2]
  | .neq x y, b, h => by
    cases b <;> simp only [BExpr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case neq c d => rw [U64Expr.beq_eq x c h.1, U64Expr.beq_eq y d h.2]
  | .lt x y, b, h => by
    cases b <;> simp only [BExpr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case lt c d => rw [U64Expr.beq_eq x c h.1, U64Expr.beq_eq y d h.2]
  | .flt x y, b, h => by
    cases b <;> simp only [BExpr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case flt c d => rw [FExpr.beq_eq x c h.1, FExpr.beq_eq y d h.2]
  | .bit x i, b, h => by
    cases b <;> simp only [BExpr.beq, Bool.false_eq_true, Bool.and_eq_true,
      beq_iff_eq] at h
    case bit y j => rw [FExpr.beq_eq x y h.1, h.2]
  | .not a, b, h => by
    cases b <;> simp only [BExpr.beq, Bool.false_eq_true] at h
    case not b => rw [BExpr.beq_eq a b h]
  | .and x y, b, h => by
    cases b <;> simp only [BExpr.beq, Bool.false_eq_true, Bool.and_eq_true] at h
    case and c d => rw [BExpr.beq_eq x c h.1, BExpr.beq_eq y d h.2]

end

end BeqEq

/-! ## Scoping

`scoped n` says every `localVar` reference is below `n`. Interned steps are scoped at
their own index by construction, which is what makes their values stable as the steps
array grows — the backbone of the eval-preservation proof. -/

mutual

/-- All `localVar` references below `n`. -/
def FExpr.scoped (n : ℕ) : FExpr F → Bool
  | .expr _ => true
  | .const _ => true
  | .localVar i => decide (i < n)
  | .add x y => x.scoped n && y.scoped n
  | .mul x y => x.scoped n && y.scoped n
  | .inv x => x.scoped n
  | .ofU64 u => u.scoped n
  | .ite c t e => c.scoped n && t.scoped n && e.scoped n
  | .listGet xs i => FExpr.scopedList n xs && i.scoped n
  | .dataGet _ _ r _ => r.scoped n
  | .hintGet _ _ r _ => r.scoped n

/-- All `localVar` references below `n`, elementwise. -/
def FExpr.scopedList (n : ℕ) : List (FExpr F) → Bool
  | [] => true
  | x :: xs => x.scoped n && FExpr.scopedList n xs

/-- All `localVar` references below `n`. -/
def U64Expr.scoped (n : ℕ) : U64Expr F → Bool
  | .const _ => true
  | .val x => x.scoped n
  | .idx => true
  | .localVar i => decide (i < n)
  | .add x y => x.scoped n && y.scoped n
  | .mul x y => x.scoped n && y.scoped n
  | .div x y => x.scoped n && y.scoped n
  | .mod x y => x.scoped n && y.scoped n
  | .land x y => x.scoped n && y.scoped n
  | .lor x y => x.scoped n && y.scoped n
  | .lxor x y => x.scoped n && y.scoped n
  | .shiftL x y => x.scoped n && y.scoped n
  | .shiftR x y => x.scoped n && y.scoped n
  | .ite c t e => c.scoped n && t.scoped n && e.scoped n

/-- All `localVar` references below `n`. -/
def BExpr.scoped (n : ℕ) : BExpr F → Bool
  | .true => Bool.true
  | .false => Bool.true
  | .feq x y => x.scoped n && y.scoped n
  | .neq x y => x.scoped n && y.scoped n
  | .lt x y => x.scoped n && y.scoped n
  | .flt x y => x.scoped n && y.scoped n
  | .bit x _ => x.scoped n
  | .not b => b.scoped n
  | .and x y => x.scoped n && y.scoped n

end

mutual

/-- Scoping is monotone in the bound. -/
theorem FExpr.scoped_mono {n m : ℕ} (hnm : n ≤ m) :
    ∀ {e : FExpr F}, e.scoped n = true → e.scoped m = true
  | .expr _, _ => rfl
  | .const _, _ => rfl
  | .localVar i, h => by
    simp only [FExpr.scoped, decide_eq_true_eq] at h ⊢; omega
  | .add x y, h => by
    simp only [FExpr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .mul x y, h => by
    simp only [FExpr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .inv x, h => x.scoped_mono hnm h
  | .ofU64 u, h => u.scoped_mono hnm h
  | .ite c t e, h => by
    simp only [FExpr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨⟨c.scoped_mono hnm h.1.1, t.scoped_mono hnm h.1.2⟩, e.scoped_mono hnm h.2⟩
  | .listGet xs i, h => by
    simp only [FExpr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨FExpr.scopedList_mono hnm h.1, i.scoped_mono hnm h.2⟩
  | .dataGet _ _ r _, h => r.scoped_mono hnm h
  | .hintGet _ _ r _, h => r.scoped_mono hnm h

/-- Scoping is monotone in the bound, elementwise. -/
theorem FExpr.scopedList_mono {n m : ℕ} (hnm : n ≤ m) :
    ∀ {xs : List (FExpr F)}, FExpr.scopedList n xs = true → FExpr.scopedList m xs = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [FExpr.scopedList, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, FExpr.scopedList_mono hnm h.2⟩

/-- Scoping is monotone in the bound. -/
theorem U64Expr.scoped_mono {n m : ℕ} (hnm : n ≤ m) :
    ∀ {e : U64Expr F}, e.scoped n = true → e.scoped m = true
  | .const _, _ => rfl
  | .val x, h => x.scoped_mono hnm h
  | .idx, _ => rfl
  | .localVar i, h => by
    simp only [U64Expr.scoped, decide_eq_true_eq] at h ⊢; omega
  | .add x y, h => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .mul x y, h => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .div x y, h => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .mod x y, h => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .land x y, h => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .lor x y, h => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .lxor x y, h => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .shiftL x y, h => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .shiftR x y, h => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .ite c t e, h => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨⟨c.scoped_mono hnm h.1.1, t.scoped_mono hnm h.1.2⟩, e.scoped_mono hnm h.2⟩

/-- Scoping is monotone in the bound. -/
theorem BExpr.scoped_mono {n m : ℕ} (hnm : n ≤ m) :
    ∀ {e : BExpr F}, e.scoped n = true → e.scoped m = true
  | .true, _ => rfl
  | .false, _ => rfl
  | .feq x y, h => by
    simp only [BExpr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .neq x y, h => by
    simp only [BExpr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .lt x y, h => by
    simp only [BExpr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .flt x y, h => by
    simp only [BExpr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩
  | .bit x _, h => x.scoped_mono hnm h
  | .not b, h => b.scoped_mono hnm h
  | .and x y, h => by
    simp only [BExpr.scoped, Bool.and_eq_true] at h ⊢
    exact ⟨x.scoped_mono hnm h.1, y.scoped_mono hnm h.2⟩

end

/-! ## Evaluation only reads scoped locals -/

section CongrLocals
variable [FiniteField F] {env : ProverEnvironment F} {idx : ℕ}
  {loc loc' : Array (F ⊕ UInt64)} {n : ℕ}

mutual

/-- Evaluation of an `n`-scoped expression only reads the first `n` locals. -/
theorem FExpr.eval_congr_locals (h : ∀ i, i < n → loc[i]? = loc'[i]?) :
    ∀ (e : FExpr F), e.scoped n = true →
      e.eval { env, locals := loc, idx } = e.eval { env, locals := loc', idx }
  | .expr _, _ => rfl
  | .const _, _ => rfl
  | .localVar i, hs => by
    simp only [FExpr.scoped, decide_eq_true_eq] at hs
    simp only [FExpr.eval, h i hs]
  | .add x y, hs => by
    simp only [FExpr.scoped, Bool.and_eq_true] at hs
    simp only [FExpr.eval, FExpr.eval_congr_locals h x hs.1, FExpr.eval_congr_locals h y hs.2]
  | .mul x y, hs => by
    simp only [FExpr.scoped, Bool.and_eq_true] at hs
    simp only [FExpr.eval, FExpr.eval_congr_locals h x hs.1, FExpr.eval_congr_locals h y hs.2]
  | .inv x, hs => by
    simp only [FExpr.eval, FExpr.eval_congr_locals h x hs]
  | .ofU64 u, hs => by
    simp only [FExpr.eval, U64Expr.eval_congr_locals h u hs]
  | .ite c t e, hs => by
    simp only [FExpr.scoped, Bool.and_eq_true] at hs
    simp only [FExpr.eval, BExpr.eval_congr_locals h c hs.1.1,
      FExpr.eval_congr_locals h t hs.1.2, FExpr.eval_congr_locals h e hs.2]
  | .listGet xs i, hs => by
    simp only [FExpr.scoped, Bool.and_eq_true] at hs
    simp only [FExpr.eval, U64Expr.eval_congr_locals h i hs.2,
      FExpr.evalList_congr_locals h xs hs.1]
  | .dataGet k m r c, hs => by
    simp only [FExpr.eval, U64Expr.eval_congr_locals h r hs]
  | .hintGet k m r c, hs => by
    simp only [FExpr.eval, U64Expr.eval_congr_locals h r hs]

/-- Elementwise `eval_congr_locals` (any index). -/
theorem FExpr.evalList_congr_locals (h : ∀ i, i < n → loc[i]? = loc'[i]?) :
    ∀ (xs : List (FExpr F)), FExpr.scopedList n xs = true → ∀ (k : ℕ),
      FExpr.evalList { env, locals := loc, idx } k xs
        = FExpr.evalList { env, locals := loc', idx } k xs
  | [], _, _ => rfl
  | x :: xs, hs, k => by
    simp only [FExpr.scopedList, Bool.and_eq_true] at hs
    match k with
    | 0 => simpa only [FExpr.evalList] using FExpr.eval_congr_locals h x hs.1
    | k + 1 => simpa only [FExpr.evalList] using FExpr.evalList_congr_locals h xs hs.2 k

/-- Evaluation of an `n`-scoped expression only reads the first `n` locals. -/
theorem U64Expr.eval_congr_locals (h : ∀ i, i < n → loc[i]? = loc'[i]?) :
    ∀ (e : U64Expr F), e.scoped n = true →
      e.eval { env, locals := loc, idx } = e.eval { env, locals := loc', idx }
  | .const _, _ => rfl
  | .val x, hs => by
    simp only [U64Expr.eval, FExpr.eval_congr_locals h x hs]
  | .idx, _ => rfl
  | .localVar i, hs => by
    simp only [U64Expr.scoped, decide_eq_true_eq] at hs
    simp only [U64Expr.eval, h i hs]
  | .add x y, hs => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at hs
    simp only [U64Expr.eval, U64Expr.eval_congr_locals h x hs.1,
      U64Expr.eval_congr_locals h y hs.2]
  | .mul x y, hs => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at hs
    simp only [U64Expr.eval, U64Expr.eval_congr_locals h x hs.1,
      U64Expr.eval_congr_locals h y hs.2]
  | .div x y, hs => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at hs
    simp only [U64Expr.eval, U64Expr.eval_congr_locals h x hs.1,
      U64Expr.eval_congr_locals h y hs.2]
  | .mod x y, hs => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at hs
    simp only [U64Expr.eval, U64Expr.eval_congr_locals h x hs.1,
      U64Expr.eval_congr_locals h y hs.2]
  | .land x y, hs => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at hs
    simp only [U64Expr.eval, U64Expr.eval_congr_locals h x hs.1,
      U64Expr.eval_congr_locals h y hs.2]
  | .lor x y, hs => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at hs
    simp only [U64Expr.eval, U64Expr.eval_congr_locals h x hs.1,
      U64Expr.eval_congr_locals h y hs.2]
  | .lxor x y, hs => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at hs
    simp only [U64Expr.eval, U64Expr.eval_congr_locals h x hs.1,
      U64Expr.eval_congr_locals h y hs.2]
  | .shiftL x y, hs => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at hs
    simp only [U64Expr.eval, U64Expr.eval_congr_locals h x hs.1,
      U64Expr.eval_congr_locals h y hs.2]
  | .shiftR x y, hs => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at hs
    simp only [U64Expr.eval, U64Expr.eval_congr_locals h x hs.1,
      U64Expr.eval_congr_locals h y hs.2]
  | .ite c t e, hs => by
    simp only [U64Expr.scoped, Bool.and_eq_true] at hs
    simp only [U64Expr.eval, BExpr.eval_congr_locals h c hs.1.1,
      U64Expr.eval_congr_locals h t hs.1.2, U64Expr.eval_congr_locals h e hs.2]

/-- Evaluation of an `n`-scoped condition only reads the first `n` locals. -/
theorem BExpr.eval_congr_locals (h : ∀ i, i < n → loc[i]? = loc'[i]?) :
    ∀ (e : BExpr F), e.scoped n = true →
      e.eval { env, locals := loc, idx } = e.eval { env, locals := loc', idx }
  | .true, _ => rfl
  | .false, _ => rfl
  | .feq x y, hs => by
    simp only [BExpr.scoped, Bool.and_eq_true] at hs
    simp only [BExpr.eval, FExpr.eval_congr_locals h x hs.1, FExpr.eval_congr_locals h y hs.2]
  | .neq x y, hs => by
    simp only [BExpr.scoped, Bool.and_eq_true] at hs
    simp only [BExpr.eval, U64Expr.eval_congr_locals h x hs.1,
      U64Expr.eval_congr_locals h y hs.2]
  | .lt x y, hs => by
    simp only [BExpr.scoped, Bool.and_eq_true] at hs
    simp only [BExpr.eval, U64Expr.eval_congr_locals h x hs.1,
      U64Expr.eval_congr_locals h y hs.2]
  | .flt x y, hs => by
    simp only [BExpr.scoped, Bool.and_eq_true] at hs
    simp only [BExpr.eval, FExpr.eval_congr_locals h x hs.1, FExpr.eval_congr_locals h y hs.2]
  | .bit x _, hs => by
    simp only [BExpr.eval, FExpr.eval_congr_locals h x hs]
  | .not b, hs => by
    simp only [BExpr.eval, BExpr.eval_congr_locals h b hs]
  | .and x y, hs => by
    simp only [BExpr.scoped, Bool.and_eq_true] at hs
    simp only [BExpr.eval, BExpr.eval_congr_locals h x hs.1, BExpr.eval_congr_locals h y hs.2]

end

end CongrLocals

/-! ## Step-list well-formedness and evaluation -/

/-- Step at global index `k` may only reference locals below `k`. -/
def Step.scopedAt (k : ℕ) : Step F → Bool
  | .letF e => e.scoped k
  | .letU e => e.scoped k

/-- All steps scoped at their own global index, the first sitting at index `k`. -/
def stepsWF (k : ℕ) : List (Step F) → Bool
  | [] => Bool.true
  | s :: rest => s.scopedAt k && stepsWF (k + 1) rest

theorem stepsWF_append {k : ℕ} {l₁ l₂ : List (Step F)} :
    stepsWF k (l₁ ++ l₂) = (stepsWF k l₁ && stepsWF (k + l₁.length) l₂) := by
  induction l₁ generalizing k with
  | nil => simp [stepsWF]
  | cons s l ih =>
    simp only [List.cons_append, stepsWF, ih, List.length_cons, Bool.and_assoc]
    ring_nf

section Steps
variable [FiniteField F] {env : ProverEnvironment F}

/-- The value a step contributes, evaluated against a given locals array. -/
def Step.val (env : ProverEnvironment F) (locals : Array (F ⊕ UInt64)) :
    Step F → F ⊕ UInt64
  | .letF e => .inl (e.eval { env, locals })
  | .letU e => .inr (e.eval { env, locals })

/-- A scoped step's value only reads the locals below its scope. -/
theorem Step.val_congr_locals {n : ℕ} {loc loc' : Array (F ⊕ UInt64)}
    (h : ∀ i, i < n → loc[i]? = loc'[i]?) :
    ∀ (s : Step F), s.scopedAt n = true → s.val env loc = s.val env loc'
  | .letF e, hs => congrArg Sum.inl (FExpr.eval_congr_locals h e hs)
  | .letU e, hs => congrArg Sum.inr (U64Expr.eval_congr_locals h e hs)

@[simp]
theorem evalSteps_cons (s : Step F) (l : List (Step F)) (acc) :
    evalSteps env (s :: l) acc = evalSteps env l (acc.push (s.val env acc)) := by
  cases s <;> rfl

theorem evalSteps_append (l₁ l₂ : List (Step F)) (acc) :
    evalSteps env (l₁ ++ l₂) acc = evalSteps env l₂ (evalSteps env l₁ acc) := by
  induction l₁ generalizing acc with
  | nil => rfl
  | cons s l ih => rw [List.cons_append, evalSteps_cons, evalSteps_cons, ih]

theorem size_evalSteps (l : List (Step F)) (acc) :
    (evalSteps env l acc).size = acc.size + l.length := by
  induction l generalizing acc with
  | nil => simp [evalSteps]
  | cons s l ih => rw [evalSteps_cons, ih] ; simp ; omega

/-- Evaluating more steps never disturbs the locals already present. -/
theorem getElem?_evalSteps_of_lt (l : List (Step F)) (acc) {i : ℕ} (h : i < acc.size) :
    (evalSteps env l acc)[i]? = acc[i]? := by
  induction l generalizing acc with
  | nil => rfl
  | cons s l ih =>
    rw [evalSteps_cons, ih (h := by simp; omega)]
    exact (Array.getElem?_push_lt h).trans (Array.getElem?_eq_getElem h).symm

/-- On a well-formed step list, the local produced for step `j` is step `j`'s body
evaluated against the **full** final locals (its scope makes the tail invisible to
it). -/
theorem getElem?_evalSteps_self (l : List (Step F)) (acc)
    (hwf : stepsWF acc.size l = true) {j : ℕ} (hj : j < l.length) :
    (evalSteps env l acc)[acc.size + j]?
      = some (l[j].val env (evalSteps env l acc)) := by
  induction l generalizing acc j with
  | nil => exact absurd hj (by simp)
  | cons s rest ih =>
    simp only [stepsWF, Bool.and_eq_true] at hwf
    rw [evalSteps_cons]
    match j, hj with
    | 0, _ =>
      have hsize : acc.size + 0 < (acc.push (Step.val env acc s)).size := by simp
      rw [getElem?_evalSteps_of_lt _ _ hsize]
      simp only [Nat.add_zero, Array.getElem?_push_size, List.getElem_cons_zero]
      congr 1
      refine Step.val_congr_locals (n := acc.size) (fun i hi => ?_) s hwf.1
      rw [getElem?_evalSteps_of_lt _ _ (by simp; omega), Array.getElem?_push_lt hi]
      exact Array.getElem?_eq_getElem hi
    | k + 1, hj =>
      have hwf' : stepsWF (acc.push (Step.val env acc s)).size rest = true := by
        simpa using hwf.2
      have hjk : k < rest.length := by simpa using hj
      have hidx : acc.size + (k + 1) = (acc.push (Step.val env acc s)).size + k := by
        simp; omega
      rw [hidx, ih (acc.push (Step.val env acc s)) hwf' hjk]
      simp only [List.getElem_cons_succ]

end Steps

/-! ## Atoms

Every term the sharing pass returns is an *atom* — a `const` or a `localVar` — because
`internF`/`internU` always answer with a step reference. Atoms are trivially
`idx`-independent, which is what makes substituting old-step replacements into
`mapRange` bodies (which re-bind `idx`) sound. -/

/-- `const` or `localVar`. -/
def FExpr.atom : FExpr F → Bool
  | .const _ => Bool.true
  | .localVar _ => Bool.true
  | _ => Bool.false

/-- `const` or `localVar`. -/
def U64Expr.atom : U64Expr F → Bool
  | .const _ => Bool.true
  | .localVar _ => Bool.true
  | _ => Bool.false

section AtomLemmas
variable [FiniteField F] {env : ProverEnvironment F} {loc : Array (F ⊕ UInt64)}

/-- Atoms ignore the `mapRange` index. -/
theorem FExpr.eval_atom_idx : ∀ {e : FExpr F}, e.atom = true → ∀ (idx idx' : ℕ),
    e.eval { env, locals := loc, idx } = e.eval { env, locals := loc, idx := idx' }
  | .const _, _, _, _ => rfl
  | .localVar _, _, _, _ => rfl

/-- Atoms ignore the `mapRange` index. -/
theorem U64Expr.eval_atom_idx : ∀ {e : U64Expr F}, e.atom = true → ∀ (idx idx' : ℕ),
    e.eval { env, locals := loc, idx } = e.eval { env, locals := loc, idx := idx' }
  | .const _, _, _, _ => rfl
  | .localVar _, _, _, _ => rfl

end AtomLemmas

/-! ## The pass invariant -/

section Spec
variable [DecidableEq F] [Hashable F]

/-- State extension: the steps grow by appending, the old-step map is unchanged. -/
structure Extends (s s' : ShareState F) : Prop where
  prefix_steps : s.steps.toList <+: s'.steps.toList
  old_eq : s'.old = s.old

theorem Extends.rfl {s : ShareState F} : Extends s s := ⟨List.prefix_rfl, _root_.rfl⟩

theorem Extends.trans {s₁ s₂ s₃ : ShareState F}
    (h₁ : Extends s₁ s₂) (h₂ : Extends s₂ s₃) : Extends s₁ s₃ :=
  ⟨h₁.prefix_steps.trans h₂.prefix_steps, h₂.old_eq.trans h₁.old_eq⟩

theorem Extends.size_le {s s' : ShareState F} (h : Extends s s') :
    s.steps.size ≤ s'.steps.size := by
  have := h.prefix_steps.length_le
  simpa using this

variable [FiniteField F]

/-- The locals array a state's steps denote. -/
def ShareState.denote (env : ProverEnvironment F) (s : ShareState F) :
    Array (F ⊕ UInt64) :=
  evalSteps env s.steps.toList

@[simp]
theorem ShareState.size_denote (env : ProverEnvironment F) (s : ShareState F) :
    (s.denote env).size = s.steps.size := by
  simp [ShareState.denote, size_evalSteps]

/-- The field value the original semantics reads from locals slot `i`
(`FExpr.eval`'s `localVar` case). -/
def lookupF (L : Array (F ⊕ UInt64)) (i : ℕ) : F :=
  match L[i]? with
  | some (.inl x) => x
  | _ => 0

/-- The u64 value the original semantics reads from locals slot `i`. -/
def lookupU (L : Array (F ⊕ UInt64)) (i : ℕ) : UInt64 :=
  match L[i]? with
  | some (.inr n) => n
  | _ => 0

/-- The pass invariant, relative to the fixed environment and the *original* locals
prefix `L` (the locals produced by the original steps processed so far):
the new steps are well-formed (each scoped at its own index), and the old-step map's
replacements are atoms, scoped, and denote exactly the original locals reads. -/
structure Inv (env : ProverEnvironment F) (L : Array (F ⊕ UInt64))
    (s : ShareState F) : Prop where
  wf : stepsWF 0 s.steps.toList = true
  oldLen : s.old.size = L.size
  oldAtomF : ∀ i, (oldRefF s.old i).atom = true
  oldAtomU : ∀ i, (oldRefU s.old i).atom = true
  oldScopedF : ∀ i, (oldRefF s.old i).scoped s.steps.size = true
  oldScopedU : ∀ i, (oldRefU s.old i).scoped s.steps.size = true
  oldEvalF : ∀ i, (oldRefF s.old i).eval { env, locals := s.denote env } = lookupF L i
  oldEvalU : ∀ i, (oldRefU s.old i).eval { env, locals := s.denote env } = lookupU L i

variable {env : ProverEnvironment F}

/-- Growing the steps never disturbs the locals already denoted. -/
theorem Extends.denote_agree {s s' : ShareState F} (h : Extends s s') :
    ∀ i, i < s.steps.size → (s.denote env)[i]? = (s'.denote env)[i]? := by
  intro i hi
  obtain ⟨ext, hext⟩ := h.prefix_steps
  rw [ShareState.denote, ShareState.denote, ← hext, evalSteps_append]
  exact (getElem?_evalSteps_of_lt ext _ (by simpa [size_evalSteps] using hi)).symm

/-- A term scoped to the smaller state evaluates identically in the larger one. -/
theorem Extends.eval_stable_F {s s' : ShareState F} (h : Extends s s')
    {e : FExpr F} (hsc : e.scoped s.steps.size = true) :
    e.eval { env, locals := s'.denote env } = e.eval { env, locals := s.denote env } :=
  (FExpr.eval_congr_locals (fun i hi => (h.denote_agree i hi).symm) e hsc)

/-- A term scoped to the smaller state evaluates identically in the larger one. -/
theorem Extends.eval_stable_U {s s' : ShareState F} (h : Extends s s')
    {e : U64Expr F} (hsc : e.scoped s.steps.size = true) :
    e.eval { env, locals := s'.denote env } = e.eval { env, locals := s.denote env } :=
  (U64Expr.eval_congr_locals (fun i hi => (h.denote_agree i hi).symm) e hsc)

/-- A condition scoped to the smaller state evaluates identically in the larger one. -/
theorem Extends.eval_stable_B {s s' : ShareState F} (h : Extends s s')
    {e : BExpr F} (hsc : e.scoped s.steps.size = true) :
    e.eval { env, locals := s'.denote env } = e.eval { env, locals := s.denote env } :=
  (BExpr.eval_congr_locals (fun i hi => (h.denote_agree i hi).symm) e hsc)

/-- The certified outcome of a field-sorted pass step: invariant preserved, state
extended, an atom returned, scoped, denoting `v`. -/
structure OkF (env : ProverEnvironment F) (L : Array (F ⊕ UInt64)) (s : ShareState F)
    (out : FExpr F × ShareState F) (v : F) : Prop where
  inv : Inv env L out.2
  ext : Extends s out.2
  atom : out.1.atom = true
  scope : out.1.scoped out.2.steps.size = true
  eval : out.1.eval { env, locals := out.2.denote env } = v

/-- The certified outcome of a u64-sorted pass step. -/
structure OkU (env : ProverEnvironment F) (L : Array (F ⊕ UInt64)) (s : ShareState F)
    (out : U64Expr F × ShareState F) (v : UInt64) : Prop where
  inv : Inv env L out.2
  ext : Extends s out.2
  atom : out.1.atom = true
  scope : out.1.scoped out.2.steps.size = true
  eval : out.1.eval { env, locals := out.2.denote env } = v

/-- The certified outcome of a condition pass step (conditions are recursed through,
not interned, so no atom clause). -/
structure OkB (env : ProverEnvironment F) (L : Array (F ⊕ UInt64)) (s : ShareState F)
    (out : BExpr F × ShareState F) (v : Bool) : Prop where
  inv : Inv env L out.2
  ext : Extends s out.2
  scope : out.1.scoped out.2.steps.size = true
  eval : out.1.eval { env, locals := out.2.denote env } = v

theorem OkF.of_val {L s out v v'} (h : OkF env L s out v) (hv : v = v') :
    OkF env L s out v' := hv ▸ h

theorem OkU.of_val {L s out v v'} (h : OkU env L s out v) (hv : v = v') :
    OkU env L s out v' := hv ▸ h

theorem OkB.of_val {L s out v v'} (h : OkB env L s out v) (hv : v = v') :
    OkB env L s out v' := hv ▸ h

/-- Recorded outcomes compose backwards along `Extends`. -/
theorem OkF.mono_start {L s₀ s out v} (h : OkF env L s out v) (hext : Extends s₀ s) :
    OkF env L s₀ out v := ⟨h.inv, hext.trans h.ext, h.atom, h.scope, h.eval⟩

/-- Recorded outcomes compose backwards along `Extends`. -/
theorem OkU.mono_start {L s₀ s out v} (h : OkU env L s out v) (hext : Extends s₀ s) :
    OkU env L s₀ out v := ⟨h.inv, hext.trans h.ext, h.atom, h.scope, h.eval⟩

/-- Recorded outcomes compose backwards along `Extends`. -/
theorem OkB.mono_start {L s₀ s out v} (h : OkB env L s out v) (hext : Extends s₀ s) :
    OkB env L s₀ out v := ⟨h.inv, hext.trans h.ext, h.scope, h.eval⟩

/-- The certified outcome of sharing a `listGet` payload: the rebuilt list is scoped
and `evalList`-equivalent to the original at every index. -/
structure OkL (env : ProverEnvironment F) (L : Array (F ⊕ UInt64)) (s : ShareState F)
    (xs : List (FExpr F)) (out : List (FExpr F) × ShareState F) : Prop where
  inv : Inv env L out.2
  ext : Extends s out.2
  scope : FExpr.scopedList out.2.steps.size out.1 = true
  evalList : ∀ k, FExpr.evalList { env, locals := out.2.denote env } k out.1
    = FExpr.evalList { env, locals := L } k xs

/-- Recorded outcomes compose backwards along `Extends`. -/
theorem OkL.mono_start {L s₀ s xs out} (h : OkL env L s xs out) (hext : Extends s₀ s) :
    OkL env L s₀ xs out := ⟨h.inv, hext.trans h.ext, h.scope, h.evalList⟩

/-- The invariant's old-map clauses transport along `Extends` (the replacements are
scoped to the smaller state, so their denotation is stable). -/
theorem Inv.old_transport {L : Array (F ⊕ UInt64)} {s s' : ShareState F}
    (hInv : Inv env L s) (hext : Extends s s')
    (hwf : stepsWF 0 s'.steps.toList = true) : Inv env L s' where
  wf := hwf
  oldLen := by rw [hext.old_eq]; exact hInv.oldLen
  oldAtomF i := by rw [hext.old_eq]; exact hInv.oldAtomF i
  oldAtomU i := by rw [hext.old_eq]; exact hInv.oldAtomU i
  oldScopedF i := by
    rw [hext.old_eq]; exact FExpr.scoped_mono hext.size_le (hInv.oldScopedF i)
  oldScopedU i := by
    rw [hext.old_eq]; exact U64Expr.scoped_mono hext.size_le (hInv.oldScopedU i)
  oldEvalF i := by
    rw [hext.old_eq, hext.eval_stable_F (hInv.oldScopedF i)]; exact hInv.oldEvalF i
  oldEvalU i := by
    rw [hext.old_eq, hext.eval_stable_U (hInv.oldScopedU i)]; exact hInv.oldEvalU i

/-! ## Intern specifications -/

omit [DecidableEq F] [Hashable F] [FiniteField F] in
/-- The last element of a pushed step array. -/
theorem getElem_toList_push_last (steps : Array (Step F)) (st : Step F) :
    ((steps.push st).toList)[steps.size]'(by simp) = st := by
  have h1 : ((steps.push st).toList)[steps.size]? = some st := by
    rw [Array.toList_push, List.getElem?_append_right (by simp)]
    simp
  rw [List.getElem?_eq_getElem (by simp)] at h1
  exact Option.some.inj h1

omit [DecidableEq F] [Hashable F] in
/-- Reading back the just-pushed step: its slot holds its own body's value against the
full locals (well-formedness makes the tail invisible). -/
theorem getElem?_evalSteps_push (steps : Array (Step F)) (st : Step F)
    (hwf : stepsWF 0 (steps.push st).toList = true) :
    (evalSteps env (steps.push st).toList)[steps.size]?
      = some (st.val env (evalSteps env (steps.push st).toList)) := by
  have hj : steps.size < (steps.push st).toList.length := by simp
  have h := getElem?_evalSteps_self (env := env) ((steps.push st).toList) #[]
    (by simpa using hwf) (j := steps.size) hj
  simpa [getElem_toList_push_last] using h

/-- The fresh-intern path satisfies the field-sorted contract. -/
theorem internFreshF_spec {L : Array (F ⊕ UInt64)} {s : ShareState F}
    (hInv : Inv env L s) (e : FExpr F) (hsc : e.scoped s.steps.size = true) :
    OkF env L s (internFreshF e s) (e.eval { env, locals := s.denote env }) := by
  have hext : Extends s (internFreshF e s).2 := by
    refine ⟨?_, rfl⟩
    show s.steps.toList <+: (s.steps.push (.letF e)).toList
    rw [Array.toList_push]
    exact List.prefix_append _ _
  have hwf' : stepsWF 0 (internFreshF e s).2.steps.toList = true := by
    show stepsWF 0 (s.steps.push (.letF e)).toList = true
    rw [Array.toList_push, stepsWF_append, Bool.and_eq_true]
    exact ⟨hInv.wf, by simp [stepsWF, Step.scopedAt, hsc]⟩
  refine ⟨hInv.old_transport hext hwf', hext, rfl, by simp [FExpr.scoped, internFreshF], ?_⟩
  show FExpr.eval _ (.localVar s.steps.size)
    = e.eval { env, locals := s.denote env }
  have hread := getElem?_evalSteps_push (env := env) s.steps (.letF e) hwf'
  simp only [FExpr.eval, ShareState.denote, internFreshF]
  rw [hread]
  exact hext.eval_stable_F hsc

/-- The fresh-intern path satisfies the u64-sorted contract. -/
theorem internFreshU_spec {L : Array (F ⊕ UInt64)} {s : ShareState F}
    (hInv : Inv env L s) (e : U64Expr F) (hsc : e.scoped s.steps.size = true) :
    OkU env L s (internFreshU e s) (e.eval { env, locals := s.denote env }) := by
  have hext : Extends s (internFreshU e s).2 := by
    refine ⟨?_, rfl⟩
    show s.steps.toList <+: (s.steps.push (.letU e)).toList
    rw [Array.toList_push]
    exact List.prefix_append _ _
  have hwf' : stepsWF 0 (internFreshU e s).2.steps.toList = true := by
    show stepsWF 0 (s.steps.push (.letU e)).toList = true
    rw [Array.toList_push, stepsWF_append, Bool.and_eq_true]
    exact ⟨hInv.wf, by simp [stepsWF, Step.scopedAt, hsc]⟩
  refine ⟨hInv.old_transport hext hwf', hext, rfl, by simp [U64Expr.scoped, internFreshU], ?_⟩
  show U64Expr.eval _ (.localVar s.steps.size)
    = e.eval { env, locals := s.denote env }
  have hread := getElem?_evalSteps_push (env := env) s.steps (.letU e) hwf'
  simp only [U64Expr.eval, ShareState.denote, internFreshU]
  rw [hread]
  exact hext.eval_stable_U hsc

/-- `internF` satisfies the field-sorted contract: on a verified memo hit the stored
step already denotes the node's value; otherwise a fresh step is bound. -/
theorem internF_spec {L : Array (F ⊕ UInt64)} {s : ShareState F}
    (hInv : Inv env L s) (e : FExpr F) (hsc : e.scoped s.steps.size = true) :
    OkF env L s (internF e s) (e.eval { env, locals := s.denote env }) := by
  unfold internF
  split
  case _ i heq =>
    split
    case isTrue h =>
      split
      case _ e' hstep =>
        split
        case isTrue hbeq =>
          cases FExpr.beq_eq e' e hbeq
          refine ⟨hInv, Extends.rfl, rfl, by simp [FExpr.scoped, h], ?_⟩
          show FExpr.eval _ (.localVar i) = _
          have hread := getElem?_evalSteps_self (env := env) s.steps.toList #[]
            (by simpa using hInv.wf) (j := i) (by simpa using h)
          simp only [FExpr.eval, ShareState.denote]
          rw [show (#[] : Array (F ⊕ UInt64)).size + i = i by simp] at hread
          rw [hread, Array.getElem_toList, hstep]
          rfl
        case isFalse => exact internFreshF_spec hInv e hsc
      case _ => exact internFreshF_spec hInv e hsc
    case isFalse => exact internFreshF_spec hInv e hsc
  case _ => exact internFreshF_spec hInv e hsc

/-- `internU` satisfies the u64-sorted contract. -/
theorem internU_spec {L : Array (F ⊕ UInt64)} {s : ShareState F}
    (hInv : Inv env L s) (e : U64Expr F) (hsc : e.scoped s.steps.size = true) :
    OkU env L s (internU e s) (e.eval { env, locals := s.denote env }) := by
  unfold internU
  split
  case _ i heq =>
    split
    case isTrue h =>
      split
      case _ e' hstep =>
        split
        case isTrue hbeq =>
          cases U64Expr.beq_eq e' e hbeq
          refine ⟨hInv, Extends.rfl, rfl, by simp [U64Expr.scoped, h], ?_⟩
          show U64Expr.eval _ (.localVar i) = _
          have hread := getElem?_evalSteps_self (env := env) s.steps.toList #[]
            (by simpa using hInv.wf) (j := i) (by simpa using h)
          simp only [U64Expr.eval, ShareState.denote]
          rw [show (#[] : Array (F ⊕ UInt64)).size + i = i by simp] at hread
          rw [hread, Array.getElem_toList, hstep]
          rfl
        case isFalse => exact internFreshU_spec hInv e hsc
      case _ => exact internFreshU_spec hInv e hsc
    case isFalse => exact internFreshU_spec hInv e hsc
  case _ => exact internFreshU_spec hInv e hsc

/-! ## The pass specification

One mutual induction over the four traversals: every result is invariant-preserving,
state-extending, scoped, and denotes the original term's value in the original locals
`L`. Every case opens with a `show` into the fully-projected sequencing form (the
do-blocks reduce to it definitionally), so the goals are syntactically concrete. -/

mutual

/-- `shareF` preserves evaluation. -/
theorem shareF_spec : ∀ (x : FExpr F) {L : Array (F ⊕ UInt64)} {s : ShareState F},
    Inv env L s → OkF env L s (shareF x s) (x.eval { env, locals := L })
  | .expr e, L, s, hInv => by
    show OkF env L s (internF (.expr e) s) _
    exact (internF_spec hInv (.expr e) rfl).of_val rfl
  | .const c, L, s, hInv => by
    show OkF env L s (.const c, s) _
    exact ⟨hInv, Extends.rfl, rfl, rfl, rfl⟩
  | .localVar i, L, s, hInv => by
    show OkF env L s (oldRefF s.old i, s) _
    exact ⟨hInv, Extends.rfl, hInv.oldAtomF i, hInv.oldScopedF i, hInv.oldEvalF i⟩
  | .add x y, L, s, hInv => by
    have hx := shareF_spec x hInv
    have hy := shareF_spec y hx.inv
    show OkF env L s (internF
      (.add (shareF x s).1 (shareF y (shareF x s).2).1) (shareF y (shareF x s).2).2) _
    refine ((internF_spec hy.inv _ ?_).mono_start (hx.ext.trans hy.ext)).of_val ?_
    · simp only [FExpr.scoped, Bool.and_eq_true]
      exact ⟨FExpr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [FExpr.eval]
      rw [hy.ext.eval_stable_F hx.scope, hx.eval, hy.eval]
  | .mul x y, L, s, hInv => by
    have hx := shareF_spec x hInv
    have hy := shareF_spec y hx.inv
    show OkF env L s (internF
      (.mul (shareF x s).1 (shareF y (shareF x s).2).1) (shareF y (shareF x s).2).2) _
    refine ((internF_spec hy.inv _ ?_).mono_start (hx.ext.trans hy.ext)).of_val ?_
    · simp only [FExpr.scoped, Bool.and_eq_true]
      exact ⟨FExpr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [FExpr.eval]
      rw [hy.ext.eval_stable_F hx.scope, hx.eval, hy.eval]
  | .inv x, L, s, hInv => by
    have hx := shareF_spec x hInv
    show OkF env L s (internF (FExpr.inv (shareF x s).1) (shareF x s).2) _
    refine ((internF_spec hx.inv (FExpr.inv (shareF x s).1) hx.scope).mono_start
      hx.ext).of_val ?_
    simp only [FExpr.eval]
    rw [hx.eval]
  | .ofU64 n, L, s, hInv => by
    have hn := shareU_spec n hInv
    show OkF env L s (internF (FExpr.ofU64 (shareU n s).1) (shareU n s).2) _
    refine ((internF_spec hn.inv (FExpr.ofU64 (shareU n s).1) hn.scope).mono_start
      hn.ext).of_val ?_
    simp only [FExpr.eval]
    rw [hn.eval]
  | .ite c t e, L, s, hInv => by
    have hc := shareB_spec c hInv
    have ht := shareF_spec t hc.inv
    have he := shareF_spec e ht.inv
    show OkF env L s (internF
      (.ite (shareB c s).1 (shareF t (shareB c s).2).1
        (shareF e (shareF t (shareB c s).2).2).1)
      (shareF e (shareF t (shareB c s).2).2).2) _
    refine ((internF_spec he.inv _ ?_).mono_start
      ((hc.ext.trans ht.ext).trans he.ext)).of_val ?_
    · simp only [FExpr.scoped, Bool.and_eq_true]
      exact ⟨⟨BExpr.scoped_mono (ht.ext.trans he.ext).size_le hc.scope,
        FExpr.scoped_mono he.ext.size_le ht.scope⟩, he.scope⟩
    · simp only [FExpr.eval]
      rw [(ht.ext.trans he.ext).eval_stable_B hc.scope, hc.eval,
        he.ext.eval_stable_F ht.scope, ht.eval, he.eval]
  | .listGet xs i, L, s, hInv => by
    have hxs := shareListF_spec xs hInv
    have hi := shareU_spec i hxs.inv
    show OkF env L s (internF
      (.listGet (shareListF xs s).1 (shareU i (shareListF xs s).2).1)
      (shareU i (shareListF xs s).2).2) _
    refine ((internF_spec hi.inv _ ?_).mono_start (hxs.ext.trans hi.ext)).of_val ?_
    · simp only [FExpr.scoped, Bool.and_eq_true]
      exact ⟨FExpr.scopedList_mono hi.ext.size_le hxs.scope, hi.scope⟩
    · simp only [FExpr.eval]
      rw [hi.eval]
      exact (FExpr.evalList_congr_locals
        (fun j hj => (hi.ext.denote_agree j hj).symm) _ hxs.scope _).trans
        (hxs.evalList _)
  | .dataGet k n r c, L, s, hInv => by
    have hr := shareU_spec r hInv
    show OkF env L s (internF (FExpr.dataGet k n (shareU r s).1 c) (shareU r s).2) _
    refine ((internF_spec hr.inv (FExpr.dataGet k n (shareU r s).1 c) hr.scope).mono_start
      hr.ext).of_val ?_
    simp only [FExpr.eval]
    rw [hr.eval]
  | .hintGet k n r c, L, s, hInv => by
    have hr := shareU_spec r hInv
    show OkF env L s (internF (FExpr.hintGet k n (shareU r s).1 c) (shareU r s).2) _
    refine ((internF_spec hr.inv (FExpr.hintGet k n (shareU r s).1 c) hr.scope).mono_start
      hr.ext).of_val ?_
    simp only [FExpr.eval]
    rw [hr.eval]

/-- `shareListF` preserves `evalList` at every index. -/
theorem shareListF_spec : ∀ (xs : List (FExpr F)) {L : Array (F ⊕ UInt64)}
    {s : ShareState F}, Inv env L s → OkL env L s xs (shareListF xs s)
  | [], L, s, hInv => by
    show OkL env L s [] ([], s)
    exact ⟨hInv, Extends.rfl, rfl, fun k => rfl⟩
  | x :: xs, L, s, hInv => by
    have hx := shareF_spec x hInv
    have hxs := shareListF_spec xs hx.inv
    show OkL env L s (x :: xs)
      ((shareF x s).1 :: (shareListF xs (shareF x s).2).1, (shareListF xs (shareF x s).2).2)
    refine ⟨hxs.inv, hx.ext.trans hxs.ext, ?_, ?_⟩
    · simp only [FExpr.scopedList, Bool.and_eq_true]
      exact ⟨FExpr.scoped_mono hxs.ext.size_le hx.scope, hxs.scope⟩
    · intro k
      match k with
      | 0 =>
        show FExpr.eval _ (shareF x s).1 = FExpr.eval _ x
        rw [hxs.ext.eval_stable_F hx.scope, hx.eval]
      | k + 1 =>
        exact hxs.evalList k

/-- `shareU` preserves evaluation. -/
theorem shareU_spec : ∀ (x : U64Expr F) {L : Array (F ⊕ UInt64)} {s : ShareState F},
    Inv env L s → OkU env L s (shareU x s) (x.eval { env, locals := L })
  | .const n, L, s, hInv => by
    show OkU env L s (.const n, s) _
    exact ⟨hInv, Extends.rfl, rfl, rfl, rfl⟩
  | .val x, L, s, hInv => by
    have hx := shareF_spec x hInv
    show OkU env L s (internU (U64Expr.val (shareF x s).1) (shareF x s).2) _
    refine ((internU_spec hx.inv (U64Expr.val (shareF x s).1) hx.scope).mono_start
      hx.ext).of_val ?_
    simp only [U64Expr.eval]
    rw [hx.eval]
  | .idx, L, s, hInv => by
    show OkU env L s (.const 0, s) _
    exact ⟨hInv, Extends.rfl, rfl, rfl, by simp [U64Expr.eval]⟩
  | .localVar i, L, s, hInv => by
    show OkU env L s (oldRefU s.old i, s) _
    exact ⟨hInv, Extends.rfl, hInv.oldAtomU i, hInv.oldScopedU i, hInv.oldEvalU i⟩
  | .add x y, L, s, hInv => by
    have hx := shareU_spec x hInv
    have hy := shareU_spec y hx.inv
    show OkU env L s (internU
      (.add (shareU x s).1 (shareU y (shareU x s).2).1) (shareU y (shareU x s).2).2) _
    refine ((internU_spec hy.inv _ ?_).mono_start (hx.ext.trans hy.ext)).of_val ?_
    · simp only [U64Expr.scoped, Bool.and_eq_true]
      exact ⟨U64Expr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [U64Expr.eval]
      rw [hy.ext.eval_stable_U hx.scope, hx.eval, hy.eval]
  | .mul x y, L, s, hInv => by
    have hx := shareU_spec x hInv
    have hy := shareU_spec y hx.inv
    show OkU env L s (internU
      (.mul (shareU x s).1 (shareU y (shareU x s).2).1) (shareU y (shareU x s).2).2) _
    refine ((internU_spec hy.inv _ ?_).mono_start (hx.ext.trans hy.ext)).of_val ?_
    · simp only [U64Expr.scoped, Bool.and_eq_true]
      exact ⟨U64Expr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [U64Expr.eval]
      rw [hy.ext.eval_stable_U hx.scope, hx.eval, hy.eval]
  | .div x y, L, s, hInv => by
    have hx := shareU_spec x hInv
    have hy := shareU_spec y hx.inv
    show OkU env L s (internU
      (.div (shareU x s).1 (shareU y (shareU x s).2).1) (shareU y (shareU x s).2).2) _
    refine ((internU_spec hy.inv _ ?_).mono_start (hx.ext.trans hy.ext)).of_val ?_
    · simp only [U64Expr.scoped, Bool.and_eq_true]
      exact ⟨U64Expr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [U64Expr.eval]
      rw [hy.ext.eval_stable_U hx.scope, hx.eval, hy.eval]
  | .mod x y, L, s, hInv => by
    have hx := shareU_spec x hInv
    have hy := shareU_spec y hx.inv
    show OkU env L s (internU
      (.mod (shareU x s).1 (shareU y (shareU x s).2).1) (shareU y (shareU x s).2).2) _
    refine ((internU_spec hy.inv _ ?_).mono_start (hx.ext.trans hy.ext)).of_val ?_
    · simp only [U64Expr.scoped, Bool.and_eq_true]
      exact ⟨U64Expr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [U64Expr.eval]
      rw [hy.ext.eval_stable_U hx.scope, hx.eval, hy.eval]
  | .land x y, L, s, hInv => by
    have hx := shareU_spec x hInv
    have hy := shareU_spec y hx.inv
    show OkU env L s (internU
      (.land (shareU x s).1 (shareU y (shareU x s).2).1) (shareU y (shareU x s).2).2) _
    refine ((internU_spec hy.inv _ ?_).mono_start (hx.ext.trans hy.ext)).of_val ?_
    · simp only [U64Expr.scoped, Bool.and_eq_true]
      exact ⟨U64Expr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [U64Expr.eval]
      rw [hy.ext.eval_stable_U hx.scope, hx.eval, hy.eval]
  | .lor x y, L, s, hInv => by
    have hx := shareU_spec x hInv
    have hy := shareU_spec y hx.inv
    show OkU env L s (internU
      (.lor (shareU x s).1 (shareU y (shareU x s).2).1) (shareU y (shareU x s).2).2) _
    refine ((internU_spec hy.inv _ ?_).mono_start (hx.ext.trans hy.ext)).of_val ?_
    · simp only [U64Expr.scoped, Bool.and_eq_true]
      exact ⟨U64Expr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [U64Expr.eval]
      rw [hy.ext.eval_stable_U hx.scope, hx.eval, hy.eval]
  | .lxor x y, L, s, hInv => by
    have hx := shareU_spec x hInv
    have hy := shareU_spec y hx.inv
    show OkU env L s (internU
      (.lxor (shareU x s).1 (shareU y (shareU x s).2).1) (shareU y (shareU x s).2).2) _
    refine ((internU_spec hy.inv _ ?_).mono_start (hx.ext.trans hy.ext)).of_val ?_
    · simp only [U64Expr.scoped, Bool.and_eq_true]
      exact ⟨U64Expr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [U64Expr.eval]
      rw [hy.ext.eval_stable_U hx.scope, hx.eval, hy.eval]
  | .shiftL x y, L, s, hInv => by
    have hx := shareU_spec x hInv
    have hy := shareU_spec y hx.inv
    show OkU env L s (internU
      (.shiftL (shareU x s).1 (shareU y (shareU x s).2).1) (shareU y (shareU x s).2).2) _
    refine ((internU_spec hy.inv _ ?_).mono_start (hx.ext.trans hy.ext)).of_val ?_
    · simp only [U64Expr.scoped, Bool.and_eq_true]
      exact ⟨U64Expr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [U64Expr.eval]
      rw [hy.ext.eval_stable_U hx.scope, hx.eval, hy.eval]
  | .shiftR x y, L, s, hInv => by
    have hx := shareU_spec x hInv
    have hy := shareU_spec y hx.inv
    show OkU env L s (internU
      (.shiftR (shareU x s).1 (shareU y (shareU x s).2).1) (shareU y (shareU x s).2).2) _
    refine ((internU_spec hy.inv _ ?_).mono_start (hx.ext.trans hy.ext)).of_val ?_
    · simp only [U64Expr.scoped, Bool.and_eq_true]
      exact ⟨U64Expr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [U64Expr.eval]
      rw [hy.ext.eval_stable_U hx.scope, hx.eval, hy.eval]
  | .ite c t e, L, s, hInv => by
    have hc := shareB_spec c hInv
    have ht := shareU_spec t hc.inv
    have he := shareU_spec e ht.inv
    show OkU env L s (internU
      (.ite (shareB c s).1 (shareU t (shareB c s).2).1
        (shareU e (shareU t (shareB c s).2).2).1)
      (shareU e (shareU t (shareB c s).2).2).2) _
    refine ((internU_spec he.inv _ ?_).mono_start
      ((hc.ext.trans ht.ext).trans he.ext)).of_val ?_
    · simp only [U64Expr.scoped, Bool.and_eq_true]
      exact ⟨⟨BExpr.scoped_mono (ht.ext.trans he.ext).size_le hc.scope,
        U64Expr.scoped_mono he.ext.size_le ht.scope⟩, he.scope⟩
    · simp only [U64Expr.eval]
      rw [(ht.ext.trans he.ext).eval_stable_B hc.scope, hc.eval,
        he.ext.eval_stable_U ht.scope, ht.eval, he.eval]

/-- `shareB` preserves evaluation. -/
theorem shareB_spec : ∀ (x : BExpr F) {L : Array (F ⊕ UInt64)} {s : ShareState F},
    Inv env L s → OkB env L s (shareB x s) (x.eval { env, locals := L })
  | .true, L, s, hInv => by
    show OkB env L s (.true, s) _
    exact ⟨hInv, Extends.rfl, rfl, rfl⟩
  | .false, L, s, hInv => by
    show OkB env L s (.false, s) _
    exact ⟨hInv, Extends.rfl, rfl, rfl⟩
  | .feq x y, L, s, hInv => by
    have hx := shareF_spec x hInv
    have hy := shareF_spec y hx.inv
    show OkB env L s
      (.feq (shareF x s).1 (shareF y (shareF x s).2).1, (shareF y (shareF x s).2).2) _
    refine ⟨hy.inv, hx.ext.trans hy.ext, ?_, ?_⟩
    · simp only [BExpr.scoped, Bool.and_eq_true]
      exact ⟨FExpr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [BExpr.eval]
      rw [hy.ext.eval_stable_F hx.scope, hx.eval, hy.eval]
  | .neq x y, L, s, hInv => by
    have hx := shareU_spec x hInv
    have hy := shareU_spec y hx.inv
    show OkB env L s
      (.neq (shareU x s).1 (shareU y (shareU x s).2).1, (shareU y (shareU x s).2).2) _
    refine ⟨hy.inv, hx.ext.trans hy.ext, ?_, ?_⟩
    · simp only [BExpr.scoped, Bool.and_eq_true]
      exact ⟨U64Expr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [BExpr.eval]
      rw [hy.ext.eval_stable_U hx.scope, hx.eval, hy.eval]
  | .lt x y, L, s, hInv => by
    have hx := shareU_spec x hInv
    have hy := shareU_spec y hx.inv
    show OkB env L s
      (.lt (shareU x s).1 (shareU y (shareU x s).2).1, (shareU y (shareU x s).2).2) _
    refine ⟨hy.inv, hx.ext.trans hy.ext, ?_, ?_⟩
    · simp only [BExpr.scoped, Bool.and_eq_true]
      exact ⟨U64Expr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [BExpr.eval]
      rw [hy.ext.eval_stable_U hx.scope, hx.eval, hy.eval]
  | .flt x y, L, s, hInv => by
    have hx := shareF_spec x hInv
    have hy := shareF_spec y hx.inv
    show OkB env L s
      (.flt (shareF x s).1 (shareF y (shareF x s).2).1, (shareF y (shareF x s).2).2) _
    refine ⟨hy.inv, hx.ext.trans hy.ext, ?_, ?_⟩
    · simp only [BExpr.scoped, Bool.and_eq_true]
      exact ⟨FExpr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [BExpr.eval]
      rw [hy.ext.eval_stable_F hx.scope, hx.eval, hy.eval]
  | .bit x i, L, s, hInv => by
    have hx := shareF_spec x hInv
    show OkB env L s (.bit (shareF x s).1 i, (shareF x s).2) _
    refine ⟨hx.inv, hx.ext, hx.scope, ?_⟩
    simp only [BExpr.eval]
    rw [hx.eval]
  | .not b, L, s, hInv => by
    have hb := shareB_spec b hInv
    show OkB env L s (.not (shareB b s).1, (shareB b s).2) _
    refine ⟨hb.inv, hb.ext, hb.scope, ?_⟩
    simp only [BExpr.eval]
    rw [hb.eval]
  | .and x y, L, s, hInv => by
    have hx := shareB_spec x hInv
    have hy := shareB_spec y hx.inv
    show OkB env L s
      (.and (shareB x s).1 (shareB y (shareB x s).2).1, (shareB y (shareB x s).2).2) _
    refine ⟨hy.inv, hx.ext.trans hy.ext, ?_, ?_⟩
    · simp only [BExpr.scoped, Bool.and_eq_true]
      exact ⟨BExpr.scoped_mono hy.ext.size_le hx.scope, hy.scope⟩
    · simp only [BExpr.eval]
      rw [hy.ext.eval_stable_B hx.scope, hx.eval, hy.eval]

end

/-! ## Remap specification (`mapRange` bodies) -/

set_option linter.unusedSectionVars false in
mutual

/-- Remapped terms are scoped: every surviving `localVar` comes from the old-step map. -/
theorem remapF_scoped {old : Array (FExpr F ⊕ U64Expr F)} {n : ℕ}
    (hF : ∀ i, (oldRefF old i).scoped n = true)
    (hU : ∀ i, (oldRefU old i).scoped n = true) :
    ∀ (x : FExpr F), (remapF old x).scoped n = true
  | .expr _ => rfl
  | .const _ => rfl
  | .localVar i => hF i
  | .add x y => by
    simp only [remapF, FExpr.scoped, Bool.and_eq_true]
    exact ⟨remapF_scoped hF hU x, remapF_scoped hF hU y⟩
  | .mul x y => by
    simp only [remapF, FExpr.scoped, Bool.and_eq_true]
    exact ⟨remapF_scoped hF hU x, remapF_scoped hF hU y⟩
  | .inv x => remapF_scoped hF hU x
  | .ofU64 u => remapU_scoped hF hU u
  | .ite c t e => by
    simp only [remapF, FExpr.scoped, Bool.and_eq_true]
    exact ⟨⟨remapB_scoped hF hU c, remapF_scoped hF hU t⟩, remapF_scoped hF hU e⟩
  | .listGet xs i => by
    simp only [remapF, FExpr.scoped, Bool.and_eq_true]
    exact ⟨remapListF_scoped hF hU xs, remapU_scoped hF hU i⟩
  | .dataGet _ _ r _ => remapU_scoped hF hU r
  | .hintGet _ _ r _ => remapU_scoped hF hU r

/-- Remapped lists are scoped. -/
theorem remapListF_scoped {old : Array (FExpr F ⊕ U64Expr F)} {n : ℕ}
    (hF : ∀ i, (oldRefF old i).scoped n = true)
    (hU : ∀ i, (oldRefU old i).scoped n = true) :
    ∀ (xs : List (FExpr F)), FExpr.scopedList n (remapListF old xs) = true
  | [] => rfl
  | x :: xs => by
    simp only [remapListF, FExpr.scopedList, Bool.and_eq_true]
    exact ⟨remapF_scoped hF hU x, remapListF_scoped hF hU xs⟩

/-- Remapped terms are scoped. -/
theorem remapU_scoped {old : Array (FExpr F ⊕ U64Expr F)} {n : ℕ}
    (hF : ∀ i, (oldRefF old i).scoped n = true)
    (hU : ∀ i, (oldRefU old i).scoped n = true) :
    ∀ (x : U64Expr F), (remapU old x).scoped n = true
  | .const _ => rfl
  | .val x => remapF_scoped hF hU x
  | .idx => rfl
  | .localVar i => hU i
  | .add x y => by
    simp only [remapU, U64Expr.scoped, Bool.and_eq_true]
    exact ⟨remapU_scoped hF hU x, remapU_scoped hF hU y⟩
  | .mul x y => by
    simp only [remapU, U64Expr.scoped, Bool.and_eq_true]
    exact ⟨remapU_scoped hF hU x, remapU_scoped hF hU y⟩
  | .div x y => by
    simp only [remapU, U64Expr.scoped, Bool.and_eq_true]
    exact ⟨remapU_scoped hF hU x, remapU_scoped hF hU y⟩
  | .mod x y => by
    simp only [remapU, U64Expr.scoped, Bool.and_eq_true]
    exact ⟨remapU_scoped hF hU x, remapU_scoped hF hU y⟩
  | .land x y => by
    simp only [remapU, U64Expr.scoped, Bool.and_eq_true]
    exact ⟨remapU_scoped hF hU x, remapU_scoped hF hU y⟩
  | .lor x y => by
    simp only [remapU, U64Expr.scoped, Bool.and_eq_true]
    exact ⟨remapU_scoped hF hU x, remapU_scoped hF hU y⟩
  | .lxor x y => by
    simp only [remapU, U64Expr.scoped, Bool.and_eq_true]
    exact ⟨remapU_scoped hF hU x, remapU_scoped hF hU y⟩
  | .shiftL x y => by
    simp only [remapU, U64Expr.scoped, Bool.and_eq_true]
    exact ⟨remapU_scoped hF hU x, remapU_scoped hF hU y⟩
  | .shiftR x y => by
    simp only [remapU, U64Expr.scoped, Bool.and_eq_true]
    exact ⟨remapU_scoped hF hU x, remapU_scoped hF hU y⟩
  | .ite c t e => by
    simp only [remapU, U64Expr.scoped, Bool.and_eq_true]
    exact ⟨⟨remapB_scoped hF hU c, remapU_scoped hF hU t⟩, remapU_scoped hF hU e⟩

/-- Remapped conditions are scoped. -/
theorem remapB_scoped {old : Array (FExpr F ⊕ U64Expr F)} {n : ℕ}
    (hF : ∀ i, (oldRefF old i).scoped n = true)
    (hU : ∀ i, (oldRefU old i).scoped n = true) :
    ∀ (x : BExpr F), (remapB old x).scoped n = true
  | .true => rfl
  | .false => rfl
  | .feq x y => by
    simp only [remapB, BExpr.scoped, Bool.and_eq_true]
    exact ⟨remapF_scoped hF hU x, remapF_scoped hF hU y⟩
  | .neq x y => by
    simp only [remapB, BExpr.scoped, Bool.and_eq_true]
    exact ⟨remapU_scoped hF hU x, remapU_scoped hF hU y⟩
  | .lt x y => by
    simp only [remapB, BExpr.scoped, Bool.and_eq_true]
    exact ⟨remapU_scoped hF hU x, remapU_scoped hF hU y⟩
  | .flt x y => by
    simp only [remapB, BExpr.scoped, Bool.and_eq_true]
    exact ⟨remapF_scoped hF hU x, remapF_scoped hF hU y⟩
  | .bit x _ => remapF_scoped hF hU x
  | .not b => remapB_scoped hF hU b
  | .and x y => by
    simp only [remapB, BExpr.scoped, Bool.and_eq_true]
    exact ⟨remapB_scoped hF hU x, remapB_scoped hF hU y⟩

end

section Remap
variable {env : ProverEnvironment F} {L : Array (F ⊕ UInt64)} {s : ShareState F}

mutual

/-- Remapping preserves evaluation at **every** `mapRange` index: the substituted
old-step replacements are atoms, so they ignore the index. -/
theorem remapF_spec (hInv : Inv env L s) : ∀ (x : FExpr F) (idx : ℕ),
    (remapF s.old x).eval { env, locals := s.denote env, idx }
      = x.eval { env, locals := L, idx }
  | .expr _, _ => rfl
  | .const _, _ => rfl
  | .localVar i, idx => by
    show (oldRefF s.old i).eval _ = _
    rw [FExpr.eval_atom_idx (hInv.oldAtomF i) idx 0]
    exact hInv.oldEvalF i
  | .add x y, idx => by
    simp only [remapF, FExpr.eval, remapF_spec hInv x idx, remapF_spec hInv y idx]
  | .mul x y, idx => by
    simp only [remapF, FExpr.eval, remapF_spec hInv x idx, remapF_spec hInv y idx]
  | .inv x, idx => by
    simp only [remapF, FExpr.eval, remapF_spec hInv x idx]
  | .ofU64 u, idx => by
    simp only [remapF, FExpr.eval, remapU_spec hInv u idx]
  | .ite c t e, idx => by
    simp only [remapF, FExpr.eval, remapB_spec hInv c idx, remapF_spec hInv t idx,
      remapF_spec hInv e idx]
  | .listGet xs i, idx => by
    simp only [remapF, FExpr.eval, remapU_spec hInv i idx]
    exact remapListF_spec hInv xs idx _
  | .dataGet k n r c, idx => by
    simp only [remapF, FExpr.eval, remapU_spec hInv r idx]
  | .hintGet k n r c, idx => by
    simp only [remapF, FExpr.eval, remapU_spec hInv r idx]

/-- Remapping preserves `evalList` at every index. -/
theorem remapListF_spec (hInv : Inv env L s) : ∀ (xs : List (FExpr F)) (idx k : ℕ),
    FExpr.evalList { env, locals := s.denote env, idx } k (remapListF s.old xs)
      = FExpr.evalList { env, locals := L, idx } k xs
  | [], _, _ => rfl
  | x :: xs, idx, k => by
    match k with
    | 0 => simpa only [remapListF, FExpr.evalList] using remapF_spec hInv x idx
    | k + 1 => simpa only [remapListF, FExpr.evalList] using remapListF_spec hInv xs idx k

/-- Remapping preserves evaluation at every index. -/
theorem remapU_spec (hInv : Inv env L s) : ∀ (x : U64Expr F) (idx : ℕ),
    (remapU s.old x).eval { env, locals := s.denote env, idx }
      = x.eval { env, locals := L, idx }
  | .const _, _ => rfl
  | .val x, idx => by
    simp only [remapU, U64Expr.eval, remapF_spec hInv x idx]
  | .idx, _ => rfl
  | .localVar i, idx => by
    show (oldRefU s.old i).eval _ = _
    rw [U64Expr.eval_atom_idx (hInv.oldAtomU i) idx 0]
    exact hInv.oldEvalU i
  | .add x y, idx => by
    simp only [remapU, U64Expr.eval, remapU_spec hInv x idx, remapU_spec hInv y idx]
  | .mul x y, idx => by
    simp only [remapU, U64Expr.eval, remapU_spec hInv x idx, remapU_spec hInv y idx]
  | .div x y, idx => by
    simp only [remapU, U64Expr.eval, remapU_spec hInv x idx, remapU_spec hInv y idx]
  | .mod x y, idx => by
    simp only [remapU, U64Expr.eval, remapU_spec hInv x idx, remapU_spec hInv y idx]
  | .land x y, idx => by
    simp only [remapU, U64Expr.eval, remapU_spec hInv x idx, remapU_spec hInv y idx]
  | .lor x y, idx => by
    simp only [remapU, U64Expr.eval, remapU_spec hInv x idx, remapU_spec hInv y idx]
  | .lxor x y, idx => by
    simp only [remapU, U64Expr.eval, remapU_spec hInv x idx, remapU_spec hInv y idx]
  | .shiftL x y, idx => by
    simp only [remapU, U64Expr.eval, remapU_spec hInv x idx, remapU_spec hInv y idx]
  | .shiftR x y, idx => by
    simp only [remapU, U64Expr.eval, remapU_spec hInv x idx, remapU_spec hInv y idx]
  | .ite c t e, idx => by
    simp only [remapU, U64Expr.eval, remapB_spec hInv c idx, remapU_spec hInv t idx,
      remapU_spec hInv e idx]

/-- Remapping preserves evaluation at every index. -/
theorem remapB_spec (hInv : Inv env L s) : ∀ (x : BExpr F) (idx : ℕ),
    (remapB s.old x).eval { env, locals := s.denote env, idx }
      = x.eval { env, locals := L, idx }
  | .true, _ => rfl
  | .false, _ => rfl
  | .feq x y, idx => by
    simp only [remapB, BExpr.eval, remapF_spec hInv x idx, remapF_spec hInv y idx]
    exact decide_eq_decide.mpr Iff.rfl
  | .neq x y, idx => by
    simp only [remapB, BExpr.eval, remapU_spec hInv x idx, remapU_spec hInv y idx]
  | .lt x y, idx => by
    simp only [remapB, BExpr.eval, remapU_spec hInv x idx, remapU_spec hInv y idx]
  | .flt x y, idx => by
    simp only [remapB, BExpr.eval, remapF_spec hInv x idx, remapF_spec hInv y idx]
  | .bit x i, idx => by
    simp only [remapB, BExpr.eval, remapF_spec hInv x idx]
  | .not b, idx => by
    simp only [remapB, BExpr.eval, remapB_spec hInv b idx]
  | .and x y, idx => by
    simp only [remapB, BExpr.eval, remapB_spec hInv x idx, remapB_spec hInv y idx]

end

end Remap

/-! ## Original steps: the old-map construction -/

section StepsSpec
variable {env : ProverEnvironment F}

/-- Recording a field-sorted original step's replacement extends the invariant to the
grown original-locals prefix. -/
theorem Inv.push_old_inl {L : Array (F ⊕ UInt64)} {s : ShareState F}
    (hInv : Inv env L s) {r : FExpr F} {v : F}
    (hatom : r.atom = true) (hscope : r.scoped s.steps.size = true)
    (heval : r.eval { env, locals := s.denote env } = v) :
    Inv env (L.push (.inl v)) { s with old := s.old.push (.inl r) } := by
  have hcases : ∀ i, oldRefF (s.old.push (.inl r)) i
      = if i = s.old.size then r else oldRefF s.old i := by
    intro i
    rcases Nat.lt_trichotomy i s.old.size with hlt | heq | hgt
    · rw [if_neg (by omega)]
      unfold oldRefF
      rw [Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]
    · subst heq
      rw [if_pos rfl]
      unfold oldRefF
      rw [Array.getElem?_push_size]
    · rw [if_neg (by omega)]
      unfold oldRefF
      rw [Array.getElem?_eq_none (by simp; omega), Array.getElem?_eq_none (by omega)]
  have hcasesU : ∀ i, oldRefU (s.old.push (.inl r)) i
      = if i = s.old.size then .const 0 else oldRefU s.old i := by
    intro i
    rcases Nat.lt_trichotomy i s.old.size with hlt | heq | hgt
    · rw [if_neg (by omega)]
      unfold oldRefU
      rw [Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]
    · subst heq
      rw [if_pos rfl]
      unfold oldRefU
      rw [Array.getElem?_push_size]
    · rw [if_neg (by omega)]
      unfold oldRefU
      rw [Array.getElem?_eq_none (by simp; omega), Array.getElem?_eq_none (by omega)]
  have hlookF : ∀ i, lookupF (L.push (.inl v)) i
      = if i = s.old.size then v else lookupF L i := by
    intro i
    rcases Nat.lt_trichotomy i L.size with hlt | heq | hgt
    · rw [if_neg (by have := hInv.oldLen; omega)]
      unfold lookupF
      rw [Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]
    · rw [if_pos (by have := hInv.oldLen; omega), heq]
      unfold lookupF
      rw [Array.getElem?_push_size]
    · rw [if_neg (by have := hInv.oldLen; omega)]
      unfold lookupF
      rw [Array.getElem?_eq_none (by simp; omega), Array.getElem?_eq_none (by omega)]
  have hlookU : ∀ i, lookupU (L.push (.inl v)) i
      = if i = s.old.size then 0 else lookupU L i := by
    intro i
    rcases Nat.lt_trichotomy i L.size with hlt | heq | hgt
    · rw [if_neg (by have := hInv.oldLen; omega)]
      unfold lookupU
      rw [Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]
    · rw [if_pos (by have := hInv.oldLen; omega), heq]
      unfold lookupU
      rw [Array.getElem?_push_size]
    · rw [if_neg (by have := hInv.oldLen; omega)]
      unfold lookupU
      rw [Array.getElem?_eq_none (by simp; omega), Array.getElem?_eq_none (by omega)]
  refine ⟨hInv.wf, by simp [hInv.oldLen], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hcases]
    split
    · exact hatom
    · exact hInv.oldAtomF i
  · intro i
    rw [hcasesU]
    split
    · rfl
    · exact hInv.oldAtomU i
  · intro i
    rw [hcases]
    split
    · exact hscope
    · exact hInv.oldScopedF i
  · intro i
    rw [hcasesU]
    split
    · rfl
    · exact hInv.oldScopedU i
  · intro i
    rw [hcases, hlookF]
    split
    · exact heval
    · exact hInv.oldEvalF i
  · intro i
    rw [hcasesU, hlookU]
    split
    · rfl
    · exact hInv.oldEvalU i

/-- Recording a u64-sorted original step's replacement extends the invariant to the
grown original-locals prefix. -/
theorem Inv.push_old_inr {L : Array (F ⊕ UInt64)} {s : ShareState F}
    (hInv : Inv env L s) {r : U64Expr F} {v : UInt64}
    (hatom : r.atom = true) (hscope : r.scoped s.steps.size = true)
    (heval : r.eval { env, locals := s.denote env } = v) :
    Inv env (L.push (.inr v)) { s with old := s.old.push (.inr r) } := by
  have hcases : ∀ i, oldRefU (s.old.push (.inr r)) i
      = if i = s.old.size then r else oldRefU s.old i := by
    intro i
    rcases Nat.lt_trichotomy i s.old.size with hlt | heq | hgt
    · rw [if_neg (by omega)]
      unfold oldRefU
      rw [Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]
    · subst heq
      rw [if_pos rfl]
      unfold oldRefU
      rw [Array.getElem?_push_size]
    · rw [if_neg (by omega)]
      unfold oldRefU
      rw [Array.getElem?_eq_none (by simp; omega), Array.getElem?_eq_none (by omega)]
  have hcasesF : ∀ i, oldRefF (s.old.push (.inr r)) i
      = if i = s.old.size then .const 0 else oldRefF s.old i := by
    intro i
    rcases Nat.lt_trichotomy i s.old.size with hlt | heq | hgt
    · rw [if_neg (by omega)]
      unfold oldRefF
      rw [Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]
    · subst heq
      rw [if_pos rfl]
      unfold oldRefF
      rw [Array.getElem?_push_size]
    · rw [if_neg (by omega)]
      unfold oldRefF
      rw [Array.getElem?_eq_none (by simp; omega), Array.getElem?_eq_none (by omega)]
  have hlookU : ∀ i, lookupU (L.push (.inr v)) i
      = if i = s.old.size then v else lookupU L i := by
    intro i
    rcases Nat.lt_trichotomy i L.size with hlt | heq | hgt
    · rw [if_neg (by have := hInv.oldLen; omega)]
      unfold lookupU
      rw [Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]
    · rw [if_pos (by have := hInv.oldLen; omega), heq]
      unfold lookupU
      rw [Array.getElem?_push_size]
    · rw [if_neg (by have := hInv.oldLen; omega)]
      unfold lookupU
      rw [Array.getElem?_eq_none (by simp; omega), Array.getElem?_eq_none (by omega)]
  have hlookF : ∀ i, lookupF (L.push (.inr v)) i
      = if i = s.old.size then 0 else lookupF L i := by
    intro i
    rcases Nat.lt_trichotomy i L.size with hlt | heq | hgt
    · rw [if_neg (by have := hInv.oldLen; omega)]
      unfold lookupF
      rw [Array.getElem?_push_lt hlt, Array.getElem?_eq_getElem hlt]
    · rw [if_pos (by have := hInv.oldLen; omega), heq]
      unfold lookupF
      rw [Array.getElem?_push_size]
    · rw [if_neg (by have := hInv.oldLen; omega)]
      unfold lookupF
      rw [Array.getElem?_eq_none (by simp; omega), Array.getElem?_eq_none (by omega)]
  refine ⟨hInv.wf, by simp [hInv.oldLen], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hcasesF]
    split
    · rfl
    · exact hInv.oldAtomF i
  · intro i
    rw [hcases]
    split
    · exact hatom
    · exact hInv.oldAtomU i
  · intro i
    rw [hcasesF]
    split
    · rfl
    · exact hInv.oldScopedF i
  · intro i
    rw [hcases]
    split
    · exact hscope
    · exact hInv.oldScopedU i
  · intro i
    rw [hcasesF, hlookF]
    split
    · rfl
    · exact hInv.oldEvalF i
  · intro i
    rw [hcases, hlookU]
    split
    · exact heval
    · exact hInv.oldEvalU i

/-- Sharing the original steps yields the invariant at the full original locals. -/
theorem shareSteps_spec : ∀ (l : List (Step F)) {L : Array (F ⊕ UInt64)}
    {s : ShareState F}, Inv env L s →
    Inv env (evalSteps env l L) (shareSteps l s).2
  | [], _, _, hInv => hInv
  | .letF e :: rest, L, s, hInv => by
    have he := shareF_spec e hInv
    show Inv env _ (shareSteps rest
      { (shareF e s).2 with old := (shareF e s).2.old.push (.inl (shareF e s).1) }).2
    rw [evalSteps_cons]
    exact shareSteps_spec rest (he.inv.push_old_inl he.atom he.scope he.eval)
  | .letU e :: rest, L, s, hInv => by
    have he := shareU_spec e hInv
    show Inv env _ (shareSteps rest
      { (shareU e s).2 with old := (shareU e s).2.old.push (.inr (shareU e s).1) }).2
    rw [evalSteps_cons]
    exact shareSteps_spec rest (he.inv.push_old_inr he.atom he.scope he.eval)

end StepsSpec

/-! ## Output specification and the theorem -/

omit [DecidableEq F] [Hashable F] [FiniteField F] in
/-- Elementwise scoping from a scoped list. -/
theorem FExpr.scopedList_getElem {n : ℕ} : ∀ {xs : List (FExpr F)}
    (_ : FExpr.scopedList n xs = true) {k : ℕ} (hk : k < xs.length),
    xs[k].scoped n = true
  | x :: xs, h, 0, _ => by
    simp only [FExpr.scopedList, Bool.and_eq_true] at h
    simpa using h.1
  | x :: xs, h, k + 1, hk => by
    simp only [FExpr.scopedList, Bool.and_eq_true] at h
    simpa using FExpr.scopedList_getElem h.2 (Nat.lt_of_succ_lt_succ hk)

omit [DecidableEq F] [Hashable F] in
/-- `evalList` at an in-range index is that element's evaluation. -/
theorem FExpr.evalList_eq_getElem (ctx : Ctx F) :
    ∀ (xs : List (FExpr F)) (k : ℕ) (hk : k < xs.length),
    FExpr.evalList ctx k xs = xs[k].eval ctx
  | x :: xs, 0, _ => rfl
  | x :: xs, k + 1, hk => by
    simpa [FExpr.evalList] using
      FExpr.evalList_eq_getElem ctx xs k (Nat.lt_of_succ_lt_succ hk)

/-- All `localVar` references below `n`, including inside `mapRange` bodies. -/
def VExpr.scopedBelow (n : ℕ) : {m : ℕ} → VExpr F m → Bool
  | _, .lit es => FExpr.scopedList n es.toList
  | _, .mapRange _ body => body.scoped n
  | _, .envRange _ => Bool.true
  | _, .bitsOf x => x.scoped n
  | _, .append a b => a.scopedBelow n && b.scopedBelow n

omit [DecidableEq F] [Hashable F] [FiniteField F] in
/-- Scoping is monotone in the bound. -/
theorem VExpr.scopedBelow_mono {n n' : ℕ} (hnm : n ≤ n') :
    ∀ {m : ℕ} (v : VExpr F m), v.scopedBelow n = true → v.scopedBelow n' = true
  | _, .lit es, h => FExpr.scopedList_mono hnm h
  | _, .mapRange _ body, h => body.scoped_mono hnm h
  | _, .envRange _, _ => rfl
  | _, .bitsOf x, h => x.scoped_mono hnm h
  | _, .append a b, h => by
    simp only [VExpr.scopedBelow, Bool.and_eq_true] at h ⊢
    exact ⟨VExpr.scopedBelow_mono hnm a h.1, VExpr.scopedBelow_mono hnm b h.2⟩

omit [DecidableEq F] [Hashable F] in
/-- Evaluation of a scoped output only reads the first `n` locals. -/
theorem VExpr.eval_congr_locals {env : ProverEnvironment F} {idx : ℕ}
    {loc loc' : Array (F ⊕ UInt64)} {n : ℕ} (h : ∀ i, i < n → loc[i]? = loc'[i]?) :
    ∀ {m : ℕ} (v : VExpr F m), v.scopedBelow n = true →
      v.eval { env, locals := loc, idx } = v.eval { env, locals := loc', idx }
  | _, .lit es, hs => by
    ext k hk
    simp only [VExpr.eval, Vector.getElem_map]
    refine FExpr.eval_congr_locals h es[k] ?_
    have := FExpr.scopedList_getElem hs (k := k) (by simpa using hk)
    simpa [Vector.getElem_toList] using this
  | _, .mapRange nn body, hs => by
    ext k hk
    rw [VExpr.getElem_eval_mapRange, VExpr.getElem_eval_mapRange]
    exact FExpr.eval_congr_locals h body hs
  | _, .envRange _, _ => rfl
  | _, .bitsOf x, hs => by
    ext k hk
    rw [VExpr.getElem_eval_bitsOf, VExpr.getElem_eval_bitsOf,
      FExpr.eval_congr_locals h x hs]
  | _, .append a b, hs => by
    simp only [VExpr.scopedBelow, Bool.and_eq_true] at hs
    simp only [VExpr.eval, VExpr.eval_congr_locals h a hs.1,
      VExpr.eval_congr_locals h b hs.2]

section VSpec
variable {env : ProverEnvironment F}

/-- The certified outcome of sharing an output former. -/
structure OkV (env : ProverEnvironment F) (L : Array (F ⊕ UInt64)) (s : ShareState F)
    {m : ℕ} (x : VExpr F m) (out : VExpr F m × ShareState F) : Prop where
  inv : Inv env L out.2
  ext : Extends s out.2
  scope : out.1.scopedBelow out.2.steps.size = true
  eval : out.1.eval { env, locals := out.2.denote env } = x.eval { env, locals := L }

/-- `shareV` preserves evaluation. -/
theorem shareV_spec : ∀ {m : ℕ} (x : VExpr F m) {L : Array (F ⊕ UInt64)}
    {s : ShareState F}, Inv env L s → OkV env L s x (shareV x s)
  | _, .lit es, L, s, hInv => by
    have hes := shareListF_spec es.toList hInv
    have hlen0 := shareListF_length es.toList s
    simp only [shareV]
    split
    next rs s' hsl =>
    rw [hsl] at hes hlen0
    have hlen : rs.length = es.toList.length := by simpa using hlen0
    refine ⟨hes.inv, hes.ext, ?_, ?_⟩
    · show FExpr.scopedList _ (Vector.toList ⟨rs.toArray, _⟩) = true
      simpa using hes.scope
    · ext k hk
      simp only [VExpr.eval, Vector.getElem_map]
      have hk' : k < rs.length := by rw [hlen]; simpa using hk
      rw [show ((⟨rs.toArray, _⟩ : Vector (FExpr F) _))[k]'(by simpa using hk)
          = rs[k]'hk' from by simp,
        ← FExpr.evalList_eq_getElem _ rs k hk', hes.evalList k,
        FExpr.evalList_eq_getElem _ es.toList k (by simpa using hk)]
      simp [Vector.getElem_toList]
  | _, .mapRange nn body, L, s, hInv => by
    show OkV env L s (.mapRange nn body) (.mapRange nn (remapF s.old body), s)
    refine ⟨hInv, Extends.rfl, ?_, ?_⟩
    · exact remapF_scoped hInv.oldScopedF hInv.oldScopedU body
    · ext k hk
      rw [VExpr.getElem_eval_mapRange, VExpr.getElem_eval_mapRange]
      exact remapF_spec hInv body k
  | _, .envRange o, L, s, hInv => by
    show OkV env L s (.envRange o) (.envRange o, s)
    exact ⟨hInv, Extends.rfl, rfl, rfl⟩
  | _, .bitsOf x, L, s, hInv => by
    have hx := shareF_spec x hInv
    show OkV env L s (.bitsOf x) (.bitsOf (shareF x s).1, (shareF x s).2)
    refine ⟨hx.inv, hx.ext, hx.scope, ?_⟩
    ext k hk
    rw [VExpr.getElem_eval_bitsOf, VExpr.getElem_eval_bitsOf, hx.eval]
  | _, .append a b, L, s, hInv => by
    have ha := shareV_spec a hInv
    have hb := shareV_spec b ha.inv
    show OkV env L s (.append a b)
      (.append (shareV a s).1 (shareV b (shareV a s).2).1, (shareV b (shareV a s).2).2)
    refine ⟨hb.inv, ha.ext.trans hb.ext, ?_, ?_⟩
    · simp only [VExpr.scopedBelow, Bool.and_eq_true]
      exact ⟨VExpr.scopedBelow_mono hb.ext.size_le _ ha.scope, hb.scope⟩
    · simp only [VExpr.eval]
      rw [VExpr.eval_congr_locals (fun i hi => (hb.ext.denote_agree i hi).symm) _ ha.scope,
        ha.eval, hb.eval]

end VSpec

/-- **Eval preservation**: `WitgenIR.share` rebuilds a witness program with every
distinct subterm interned as a `let`-step, without changing its evaluation on any
prover environment. This is what lets a serializer apply the pass unconditionally. -/
theorem WitgenIR.eval_share {m : ℕ} :
    ∀ (ir : WitgenIR F m) (env : ProverEnvironment F), ir.share.eval env = ir.eval env
  | .native _, _ => rfl
  | .ir steps out, env => by
    have hnoneS : ∀ (i : ℕ), (#[] : Array (FExpr F ⊕ U64Expr F))[i]? = none := by simp
    have hnoneL : ∀ (i : ℕ), (#[] : Array (F ⊕ UInt64))[i]? = none := by simp
    have hInv0 : Inv env #[] ({} : ShareState F) := by
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro i
      · unfold oldRefF; rw [hnoneS i]; rfl
      · unfold oldRefU; rw [hnoneS i]; rfl
      · unfold oldRefF; rw [hnoneS i]; rfl
      · unfold oldRefU; rw [hnoneS i]; rfl
      · unfold oldRefF lookupF; rw [hnoneS i, hnoneL i]; rfl
      · unfold oldRefU lookupU; rw [hnoneS i, hnoneL i]; rfl
    have hSteps := shareSteps_spec (env := env) steps hInv0
    have hV := shareV_spec (env := env) out hSteps
    show VExpr.eval _ (shareV out (shareSteps steps ({} : ShareState F)).2).1 = _
    exact hV.eval

end Spec

end Witgen
