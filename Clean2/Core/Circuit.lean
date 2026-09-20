/-
The circuit monad over a backend, and its two semantics:
- the *real* one (`ConstraintsHold`, `Honest`, `Local`), obtained by flattening every call to
  native operations, which is what the proof system checks, and
- the *proof-level* one (`SoundnessHold`, `CompletenessHold`, `HonestCompleteness`,
  `LocalHold`), where a call to an implementation is replaced by the contract of its interface.
The replacement theorems at the end connect the two.
-/
module

public import Clean2.Core.Backend

@[expose] public section

namespace Clean2
variable {B : Backend}

/--
A called implementation, as recorded in the parent's operations. It carries the flattened native
operations (for the real semantics) and the contract at this call site (for the proof-level
semantics), together with the proofs connecting them.

This is the proof boundary: a parent never looks at `ops`, only at the contract. The contract has
a semantic part (`Assumptions`, `Spec`, ...) and a spatial part (`pre`, `post`): the inputs must
exist in the heap, and then the outputs exist afterwards and the call is well-formed.
-/
structure Subcircuit (B : Backend) (s : B.State) where
  ops : List B.Op
  /-- the allocation state after the call -/
  next : B.State
  next_eq : next = B.flatAdvance ops s
  Assumptions : (B.Cell → B.Native) → Prop
  Spec : (B.Cell → B.Native) → Prop
  ProverAssumptions : (B.Cell → B.Native) → Prop
  ProverSpec : (B.Cell → B.Native) → Prop
  pre : Prop
  post : Prop
  soundness : ∀ env, Assumptions env → B.FlatHolds env s ops → Spec env
  completeness : ∀ env, B.FlatHonest env s ops →
    (ProverAssumptions env → B.FlatHolds env s ops) ∧ ProverSpec env
  local_of_pre : pre → B.FlatLocal s ops
  post_of_pre : pre → post

theorem Subcircuit.alloc_mono {s : B.State} (sc : Subcircuit B s) : B.Alloc s ⊆ B.Alloc sc.next := by
  rw [sc.next_eq]; exact Backend.flatAlloc_mono _ _

inductive Op (B : Backend) where
  | native : B.Op → Op B
  | call : {s : B.State} → Subcircuit B s → Op B

abbrev Ops (B : Backend) := List (Op B)

namespace Ops

/-- The allocation state after a list of operations. -/
@[circuit_norm]
def advance : Ops B → B.State → B.State
  | [], s => s
  | .native op :: ops, s => advance ops (B.advance op s)
  | .call sc :: ops, _ => advance ops sc.next

def toFlat : Ops B → List B.Op
  | [] => []
  | .native op :: ops => op :: toFlat ops
  | .call sc :: ops => sc.ops ++ toFlat ops

/-- Every call was recorded at the state where it actually sits. -/
@[circuit_norm]
def Consistent : B.State → Ops B → Prop
  | _, [] => True
  | s, .native op :: ops => Consistent (B.advance op s) ops
  | s, .call (s := s₀) sc :: ops => s = s₀ ∧ Consistent sc.next ops

/-! ### Real semantics -/

def ConstraintsHold (env : B.Cell → B.Native) (s : B.State) (ops : Ops B) : Prop :=
  B.FlatHolds env s ops.toFlat

def Honest (env : B.Cell → B.Native) (s : B.State) (ops : Ops B) : Prop :=
  B.FlatHonest env s ops.toFlat

def Local (s : B.State) (ops : Ops B) : Prop :=
  B.FlatLocal s ops.toFlat

/-! ### Proof-level semantics -/

/-- Constraints hold, with calls replaced by `Assumptions → Spec`. Used in soundness proofs. -/
@[circuit_norm]
def SoundnessHold (env : B.Cell → B.Native) : B.State → Ops B → Prop
  | _, [] => True
  | s, .native op :: ops => B.Holds env s op ∧ SoundnessHold env (B.advance op s) ops
  | _, .call sc :: ops => (sc.Assumptions env → sc.Spec env) ∧ SoundnessHold env sc.next ops

/-- Constraints hold, with calls replaced by `ProverAssumptions`. This is what a completeness
proof has to establish. -/
@[circuit_norm]
def CompletenessHold (env : B.Cell → B.Native) : B.State → Ops B → Prop
  | _, [] => True
  | s, .native op :: ops => B.Holds env s op ∧ CompletenessHold env (B.advance op s) ops
  | _, .call sc :: ops => sc.ProverAssumptions env ∧ CompletenessHold env sc.next ops

/-- The prover is honest, with calls replaced by `ProverSpec`. This is what a completeness proof
may assume. -/
@[circuit_norm]
def HonestCompleteness (env : B.Cell → B.Native) : B.State → Ops B → Prop
  | _, [] => True
  | s, .native op :: ops => B.Honest env s op ∧ HonestCompleteness env (B.advance op s) ops
  | _, .call sc :: ops => sc.ProverSpec env ∧ HonestCompleteness env sc.next ops

/-- Well-formedness, with calls replaced by `pre`, and each call's `post` (plus heap growth)
available to what follows; at the end, the continuation `K` holds at the final state, under
everything learned. This is the frame rule in sequential form: what a spatial proof has to
establish. -/
@[circuit_norm]
def LocalHold : B.State → Ops B → (B.State → Prop) → Prop
  | s, [], K => K s
  | s, .native op :: ops, K => B.reads op ⊆ B.Alloc s ∧ LocalHold (B.advance op s) ops K
  | s, .call sc :: ops, K => sc.pre ∧ (sc.post → B.Alloc s ⊆ B.Alloc sc.next → LocalHold sc.next ops K)

/-! ### Structural lemmas -/

@[circuit_norm]
theorem advance_append (a b : Ops B) (s : B.State) : advance (a ++ b) s = advance b (advance a s) := by
  induction a generalizing s with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [advance, ih]

theorem toFlat_append (a b : Ops B) : toFlat (a ++ b) = toFlat a ++ toFlat b := by
  induction a with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [toFlat, ih]

theorem flatAdvance_toFlat {s : B.State} {ops : Ops B} (h : Consistent s ops) :
    B.flatAdvance ops.toFlat s = ops.advance s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | native op => simp only [toFlat, Backend.flatAdvance, advance]; exact ih h
    | call sc =>
      obtain ⟨rfl, h⟩ := h
      simp only [toFlat, Backend.flatAdvance_append, advance, ← sc.next_eq]
      exact ih h

@[circuit_norm]
theorem consistent_append {s : B.State} (a b : Ops B) :
    Consistent s (a ++ b) ↔ Consistent s a ∧ Consistent (advance a s) b := by
  induction a generalizing s with
  | nil => simp [Consistent, advance]
  | cons op ops ih =>
    cases op with
    | native op => simp [Consistent, advance, ih]
    | call sc => simp [Consistent, advance, ih, and_assoc]

@[circuit_norm]
theorem soundnessHold_append {env : B.Cell → B.Native} {s : B.State} (a b : Ops B) :
    SoundnessHold env s (a ++ b) ↔ SoundnessHold env s a ∧ SoundnessHold env (advance a s) b := by
  induction a generalizing s with
  | nil => simp [SoundnessHold, advance]
  | cons op ops ih =>
    cases op with
    | native op => simp [SoundnessHold, advance, ih, and_assoc]
    | call sc => simp [SoundnessHold, advance, ih, and_assoc]

@[circuit_norm]
theorem completenessHold_append {env : B.Cell → B.Native} {s : B.State} (a b : Ops B) :
    CompletenessHold env s (a ++ b) ↔
      CompletenessHold env s a ∧ CompletenessHold env (advance a s) b := by
  induction a generalizing s with
  | nil => simp [CompletenessHold, advance]
  | cons op ops ih =>
    cases op with
    | native op => simp [CompletenessHold, advance, ih, and_assoc]
    | call sc => simp [CompletenessHold, advance, ih, and_assoc]

@[circuit_norm]
theorem honestCompleteness_append {env : B.Cell → B.Native} {s : B.State} (a b : Ops B) :
    HonestCompleteness env s (a ++ b) ↔
      HonestCompleteness env s a ∧ HonestCompleteness env (advance a s) b := by
  induction a generalizing s with
  | nil => simp [HonestCompleteness, advance]
  | cons op ops ih =>
    cases op with
    | native op => simp [HonestCompleteness, advance, ih, and_assoc]
    | call sc => simp [HonestCompleteness, advance, ih, and_assoc]

/-- `LocalHold` over an append, in continuation-passing form: the continuation of the first part
is the obligation of the second, so everything the first part's calls establish is available. -/
theorem localHold_append {s : B.State} (a b : Ops B) (K : B.State → Prop) :
    LocalHold s (a ++ b) K ↔ LocalHold s a fun s' => LocalHold s' b K := by
  induction a generalizing s with
  | nil => simp [LocalHold]
  | cons op ops ih => cases op <;> simp [LocalHold, ih]

/-- The continuation of consistent operations can be weakened at the state they advance to. -/
theorem localHold_mono_of_consistent {s : B.State} {ops : Ops B} (h : Consistent s ops) {K K' : B.State → Prop}
    (h_loc : LocalHold s ops K) (h_imp : K (ops.advance s) → K' (ops.advance s)) : LocalHold s ops K' := by
  induction ops generalizing s with
  | nil => exact h_imp h_loc
  | cons op ops ih =>
    cases op with
    | native op => exact ⟨h_loc.1, ih h h_loc.2 h_imp⟩
    | call sc =>
      obtain ⟨rfl, h⟩ := h
      exact ⟨h_loc.1, fun h_post h_mono => ih h (h_loc.2 h_post h_mono) h_imp⟩

/-- The same for consistent operations, where the continuation runs at the state the operations
advance to. This is the form a proof by induction over a loop needs: the `pre` of a call is
stated at its recorded state, which is that state. -/
theorem localHold_append_of_consistent {s : B.State} {a : Ops B} (h : Consistent s a) (b : Ops B)
    (K : B.State → Prop) :
    LocalHold s (a ++ b) K ↔ LocalHold s a fun _ => LocalHold (a.advance s) b K := by
  induction a generalizing s with
  | nil => simp [LocalHold, advance]
  | cons op ops ih =>
    cases op with
    | native op => simp only [Consistent] at h; simp [LocalHold, advance, ih h]
    | call sc => obtain ⟨rfl, h⟩ := h; simp [LocalHold, advance, ih h]

-- Instead, operation lists are normalized to cons form (calls and natives emit singletons).

theorem alloc_mono {s : B.State} {ops : Ops B} (h : Consistent s ops) :
    B.Alloc s ⊆ B.Alloc (ops.advance s) := by
  induction ops generalizing s with
  | nil => exact le_rfl
  | cons op ops ih =>
    cases op with
    | native op => exact (B.alloc_mono op s).trans (ih h)
    | call sc =>
      obtain ⟨rfl, h⟩ := h
      exact sc.alloc_mono.trans (ih h)

/-! ### Replacement theorems: real semantics ↔ proof-level semantics -/

/-- If the real constraints hold, then the proof-level soundness statement holds. -/
theorem soundnessHold_of_constraintsHold {env : B.Cell → B.Native} {s : B.State} {ops : Ops B}
    (h_consistent : Consistent s ops) (h : ConstraintsHold env s ops) : SoundnessHold env s ops := by
  induction ops generalizing s with
  | nil => trivial
  | cons op ops ih =>
    cases op with
    | native op =>
      simp only [ConstraintsHold, toFlat, Backend.FlatHolds] at h
      exact ⟨h.1, ih h_consistent h.2⟩
    | call sc =>
      obtain ⟨rfl, h_consistent⟩ := h_consistent
      simp only [ConstraintsHold, toFlat, Backend.flatHolds_append, ← sc.next_eq] at h
      exact ⟨fun has => sc.soundness env has h.1, ih h_consistent h.2⟩

/-- If the prover is honest and the proof-level completeness statement holds, then the real
constraints hold. -/
theorem constraintsHold_of_completenessHold {env : B.Cell → B.Native} {s : B.State} {ops : Ops B}
    (h_consistent : Consistent s ops) (h_honest : Honest env s ops) (h : CompletenessHold env s ops) :
    ConstraintsHold env s ops := by
  induction ops generalizing s with
  | nil => trivial
  | cons op ops ih =>
    cases op with
    | native op =>
      simp only [Honest, toFlat, Backend.FlatHonest] at h_honest
      exact ⟨h.1, ih h_consistent h_honest.2 h.2⟩
    | call sc =>
      obtain ⟨rfl, h_consistent⟩ := h_consistent
      simp only [Honest, toFlat, Backend.flatHonest_append, ← sc.next_eq] at h_honest
      simp only [ConstraintsHold, toFlat, Backend.flatHolds_append, ← sc.next_eq]
      exact ⟨(sc.completeness env h_honest.1).1 h.1, ih h_consistent h_honest.2 h.2⟩

/-- If the prover is honest, then the proof-level honesty statement holds. -/
theorem honestCompleteness_of_honest {env : B.Cell → B.Native} {s : B.State} {ops : Ops B}
    (h_consistent : Consistent s ops) (h_honest : Honest env s ops) : HonestCompleteness env s ops := by
  induction ops generalizing s with
  | nil => trivial
  | cons op ops ih =>
    cases op with
    | native op =>
      simp only [Honest, toFlat, Backend.FlatHonest] at h_honest
      exact ⟨h_honest.1, ih h_consistent h_honest.2⟩
    | call sc =>
      obtain ⟨rfl, h_consistent⟩ := h_consistent
      simp only [Honest, toFlat, Backend.flatHonest_append, ← sc.next_eq] at h_honest
      exact ⟨(sc.completeness env h_honest.1).2, ih h_consistent h_honest.2⟩

/-- If the proof-level spatial statement holds, the flattened operations are well-formed and
the continuation holds at the final state: the frame rule, discharged once for all calls. -/
theorem local_of_localHold {s : B.State} {ops : Ops B} {K : B.State → Prop}
    (h_consistent : Consistent s ops) (h : LocalHold s ops K) : Local s ops ∧ K (ops.advance s) := by
  induction ops generalizing s with
  | nil => exact ⟨trivial, h⟩
  | cons op ops ih =>
    cases op with
    | native op =>
      obtain ⟨h_loc, h_k⟩ := ih h_consistent h.2
      exact ⟨⟨h.1, h_loc⟩, h_k⟩
    | call sc =>
      obtain ⟨rfl, h_consistent⟩ := h_consistent
      obtain ⟨h_pre, h_rest⟩ := h
      obtain ⟨h_loc, h_k⟩ := ih h_consistent (h_rest (sc.post_of_pre h_pre) sc.alloc_mono)
      simp only [Local, toFlat, Backend.flatLocal_append, ← sc.next_eq]
      exact ⟨⟨sc.local_of_pre h_pre, h_loc⟩, h_k⟩

end Ops

/-! ### The circuit monad -/

/--
A circuit is a function from the allocation state to a result and the operations it emits.
The operations determine the next state (`Ops.advance`), so the state is recoverable from the
output, which is what keeps `output` and `advance` static.
-/
@[implicit_reducible]
def Circuit (B : Backend) (α : Type) := B.State → α × Ops B

namespace Circuit

def bind {α β : Type} (f : Circuit B α) (g : α → Circuit B β) : Circuit B β := fun s =>
  let (b, ops') := g (f s).1 (Ops.advance (f s).2 s)
  (b, (f s).2 ++ ops')

instance : Monad (Circuit B) where
  map f circuit := fun s => let (a, ops) := circuit s; (f a, ops)
  pure a := fun _ => (a, [])
  bind := bind

@[circuit_norm]
theorem bind_def {α β : Type} (f : Circuit B α) (g : α → Circuit B β) :
    f >>= g = fun s =>
      let (a, ops) := f s
      let (b, ops') := g a (Ops.advance ops s)
      (b, ops ++ ops') := rfl

@[circuit_norm]
theorem pure_def {α : Type} (a : α) : (pure a : Circuit B α) = fun _ => (a, []) := rfl

@[circuit_norm]
theorem map_def {α β : Type} (f : α → β) (circuit : Circuit B α) :
    f <$> circuit = fun s => let (a, ops) := circuit s; (f a, ops) := rfl

@[circuit_norm]
theorem seqRight_def {α β : Type} (f : Circuit B α) (g : Circuit B β) :
    f *> g = fun s =>
      let (_, ops) := f s
      let (b, ops') := g (Ops.advance ops s)
      (b, ops ++ ops') := rfl

instance : LawfulMonad (Circuit B) := LawfulMonad.mk'
  (id_map := fun x => by
    funext s
    show (let (a, ops) := x s; (id a, ops)) = x s
    rcases h : x s with ⟨a, ops⟩
    rfl)
  (pure_bind := fun a f => by
    funext s
    show (let (b, ops) := f a s; (b, [] ++ ops)) = f a s
    rcases h : f a s with ⟨b, ops⟩
    rfl)
  (bind_assoc := fun x f g => by
    funext s
    simp only [bind_def]
    rcases hx : x s with ⟨a, o₁⟩
    rcases hf : f a (Ops.advance o₁ s) with ⟨b, o₂⟩
    simp only [Ops.advance_append, List.append_assoc])
  (bind_pure_comp := fun f x => by
    funext s
    show (let (a, ops) := x s; (f a, ops ++ [])) = (let (a, ops) := x s; (f a, ops))
    rcases h : x s with ⟨a, ops⟩
    simp)

/-- The loop `for i in [n - 1, …, 0] do acc ← f i acc`, over the loop bound `n`: the same
equations as `Fin.foldrM`, which is not exposed and so does not reduce. A circuit over `n` inputs
is written as such a loop, and a proof about it is an induction on `n`. -/
@[circuit_norm]
def foldr {α : Type} : (n : ℕ) → (Fin n → α → Circuit B α) → α → Circuit B α
  | 0, _, init => pure init
  | n + 1, f, init => do
    let acc ← foldr n (fun i => f i.succ) init
    f 0 acc

/-- The loop `for i in [0, …, n - 1] do out[i] ← f i`, collecting the results: `Vector.ofFn` in
the circuit monad. A proof about it is an induction on `n`, peeling off the last iteration. -/
@[circuit_norm]
def mapFin {α : Type} : (n : ℕ) → (Fin n → Circuit B α) → Circuit B (Vector α n)
  | 0, _ => pure #v[]
  | n + 1, f => do
    let xs ← mapFin n (fun i => f i.castSucc)
    let x ← f (Fin.last n)
    return xs.push x

@[reducible, circuit_norm]
def operations {α : Type} (circuit : Circuit B α) (s : B.State) : Ops B := (circuit s).2

@[reducible, circuit_norm]
def output {α : Type} (circuit : Circuit B α) (s : B.State) : α := (circuit s).1

/-- Emit a native operation. Backends wrap this in typed smart constructors. -/
@[circuit_norm]
def native (op : B.Op) : Circuit B Unit := fun _ => ((), [.native op])

end Circuit

-- propositional cleanup that the semantics leave behind (`∧ True`, `True → p`, `p → p`)
attribute [circuit_norm] and_true true_and true_implies imp_self
-- operation lists are normalized to cons form
attribute [circuit_norm] List.cons_append List.nil_append List.append_nil List.append_assoc
  List.singleton_append

end Clean2
