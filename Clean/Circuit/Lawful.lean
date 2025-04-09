import Clean.Circuit.Basic
import Clean.Circuit.SubCircuit
variable {n m o : ℕ} {F : Type} [Field F] {α β : Type}

namespace Operations
def append {m n: ℕ} (as : Operations F m) : (bs : Operations F n) → bs.initial_offset = m → Operations F n
  | empty n, (heq : n = _) => heq ▸ as
  | witness bs k c, heq => witness (append as bs heq) k c
  | assert bs e, heq => assert (append as bs heq) e
  | lookup bs l, heq => lookup (append as bs heq) l
  | subcircuit bs s, heq => subcircuit (append as bs heq) s
end Operations

@[reducible] def OperationsFrom (F: Type) [Field F] (m: ℕ) (n : ℕ) :=
  { bs : Operations F n // bs.initial_offset = m }

instance (as : Operations F n) : CoeDep (Operations F n) (as) (OperationsFrom F (as.initial_offset) n) where
  coe := ⟨ as, rfl ⟩

def OperationsFrom.empty (n: ℕ) : OperationsFrom F n n := .mk (.empty n) rfl

-- induction principle for OperationsFrom
open Operations in
def OperationsFrom.induct {F: Type} [Field F] {motive : {n m: ℕ} → OperationsFrom F m n → Prop}
  (empty : ∀ (n), motive (n:=n) (m:=n) (OperationsFrom.empty n))
  (witness : ∀ {n m} (as : Operations F n) (k c) (ha : as.initial_offset = m),
    motive (.mk as ha) → motive (.mk (witness as k c) ha))
  (assert : ∀ {n m} (as : Operations F n) (e) (ha : as.initial_offset = m),
    motive (.mk as ha) → motive (.mk (assert as e) ha))
  (lookup : ∀ {n m} (as : Operations F n) (l) (ha : as.initial_offset = m),
    motive (.mk as ha) → motive (.mk (lookup as l) ha))
  (subcircuit : ∀ {n m} (as : Operations F n) (s) (ha : as.initial_offset = m),
    motive (.mk as ha) → motive (.mk (subcircuit as s) ha))
  {n m: ℕ} (as: OperationsFrom F m n) : motive as :=
  motive' as.val as.property
where
  motive' {n m} : (as : Operations F n) → (ha: as.initial_offset = m) → motive (.mk as ha)
  | .empty n, rfl => empty n
  | .witness _ _ _, _ => witness _ _ _ _ (motive' _ _)
  | .assert _ _, _ => assert _ _ _ (motive' _ _)
  | .lookup _ _, _ => lookup _ _ _ (motive' _ _)
  | .subcircuit _ _, _ => subcircuit _ _ _ (motive' _ _)

namespace Operations
instance : HAppend (Operations F m) (OperationsFrom F m n) (Operations F n) where
  hAppend as bs := as.append bs.val bs.property

theorem append_empty (as : Operations F n) : as ++ (OperationsFrom.empty (F:=F) n) = as := rfl

theorem empty_append (as : OperationsFrom F n m) : Operations.empty (F:=F) n ++ as = as := by
  induction as using OperationsFrom.induct with
  | empty n => rfl
  | witness | assert | lookup | subcircuit => simp_all only [HAppend.hAppend, append]

theorem append_initial_offset {m n: ℕ} (as : Operations F m) (bs : OperationsFrom F m n) :
    (as ++ bs).initial_offset = as.initial_offset := by
  induction bs using OperationsFrom.induct with
  | empty n => rfl
  | witness as _ _ _ ih | assert as _ _ ih | lookup as _ _ ih | subcircuit as _ _ ih => exact ih as

instance : HAppend (OperationsFrom F m n) (OperationsFrom F n o) (OperationsFrom F m o) where
  hAppend as bs := ⟨ as.val.append bs.val bs.property, by
    show (as.val ++ bs).initial_offset = m
    rw [append_initial_offset, as.property] ⟩

theorem append_assoc {m n o: ℕ} (as : Operations F m) (bs : OperationsFrom F m n) (cs : OperationsFrom F n o) :
  (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction cs using OperationsFrom.induct with
  | empty n => rfl
  | witness _ _ _ _ ih | assert _ _ _ ih | lookup _ _ _ ih | subcircuit _ _ _ ih =>
    simp only [HAppend.hAppend, append, witness.injEq, assert.injEq, lookup.injEq, subcircuit.injEq, and_true]
    exact ih bs
end Operations

structure OperationsListFrom (F: Type) [Field F] (m: ℕ) where
  offset : ℕ
  withLength : OperationsFrom F m offset

-- `OperationsListFrom` can be coerced to `OperationsFrom` and back
instance (ops : OperationsListFrom F m) : CoeDep (OperationsListFrom F m) (ops) (OperationsFrom F m ops.offset) where
  coe := ops.withLength

instance : CoeOut (OperationsFrom F m n) (OperationsListFrom F m) where
  coe ops := ⟨ n, ops ⟩

-- functions of the form `(n : ℕ) → OperationsListFrom F n` are an alternative representation of a circuit,
-- after resolving the successive inputs to each monad bind
def CircuitDiff (F: Type) [Field F] := (n : ℕ) → (m : ℕ) × OperationsFrom F n m

def CircuitDiff.final_offset (diff : CircuitDiff F) (n : ℕ) : ℕ := (diff n).1
def CircuitDiff.operations (diff : CircuitDiff F) (n : ℕ) : OperationsFrom F n (diff.final_offset n) :=
  (diff n).2

namespace Circuit
-- a proper circuit is "append-only"
def appends (circuit : Circuit F α) (diff : CircuitDiff F) :=
  ∀ ops: OperationsList F, (circuit ops).snd = ops.withLength ++ diff.operations ops.offset

-- a proper circuit only depends on the input offset, not on the operations
def independent (circuit : Circuit F α) : Prop :=
  ∀ ops: OperationsList F,
    (circuit ops).fst = circuit.output ops.offset ∧
    (circuit ops).snd.offset = circuit.final_offset ops.offset

def returns (circuit : Circuit F α) (out : ℕ → α) :=
  ∀ ops: OperationsList F, (circuit ops).fst = out ops.offset
end Circuit

class LawfulCircuit (circuit : Circuit F α) where
  /-- a proper circuit is encapsulated by three functions of the input offset -/
  output : ℕ → α
  final_offset : ℕ → ℕ
  operations : (n : ℕ) → OperationsFrom F n (final_offset n)

  /-- the circuit's output and final offset only depend on the input offset -/
  output_independent : ∀ ops: OperationsList F, (circuit ops).fst = output ops.offset := by intro _; rfl
  offset_independent : ∀ ops: OperationsList F, (circuit ops).snd.offset = final_offset ops.offset := by intro _; rfl

  /-- the circuit acts on operations by appending its own operations; which only depend on the input offset -/
  append_only : ∀ ops: OperationsList F, (circuit ops).snd = ops.withLength ++ operations ops.offset := by intro _; rfl

-- `pure` is a lawful circuit
instance LawfulCircuit.from_pure {a : α} : LawfulCircuit (pure a : Circuit F α) where
  output _ := a
  final_offset n := n
  operations n := .empty n

-- `bind` of two lawful circuits yields a lawful circuit
instance LawfulCircuit.from_bind {f: Circuit F α} {g : α → Circuit F β}
    (f_lawful : LawfulCircuit f) (g_lawful : ∀ a : α, LawfulCircuit (g a)) : LawfulCircuit (f >>= g) where
  output n :=
    let n' := f_lawful.final_offset n
    let a := f_lawful.output n
    (g_lawful a).output n'

  final_offset n :=
    let n' := f_lawful.final_offset n
    let a := f_lawful.output n
    (g_lawful a).final_offset n'

  operations n :=
    let n' := f_lawful.final_offset n
    let a := f_lawful.output n
    let ops_f := f_lawful.operations n
    let ops_g := (g_lawful a).operations n'
    ops_f ++ ops_g

  output_independent ops := by
    show (g _ _).1 = _ -- by definition, `(f >>= g) ops = g (f ops).1 (f ops).2`
    rw [(g_lawful _).output_independent, f_lawful.output_independent, f_lawful.offset_independent]

  offset_independent ops := by
    show (g _ _).2.offset = _
    rw [(g_lawful _).offset_independent, f_lawful.output_independent, f_lawful.offset_independent]

  append_only ops := by
    show (g _ _).2 = _
    rw [(g_lawful _).append_only, f_lawful.output_independent, f_lawful.append_only, Operations.append_assoc]

-- basic operations are lawful circuits

instance {c : Environment F → F} : LawfulCircuit (witness_var c) where
  output n := ⟨ n ⟩
  final_offset n := n + 1
  operations n := ⟨.witness (.empty n) 1 fun env => #v[c env], rfl⟩

instance {k : ℕ} {c : Environment F → Vector F k} : LawfulCircuit (witness_vars k c) where
  output n := .natInit k fun i => ⟨n + i⟩
  final_offset n := n + k
  operations n := ⟨.witness (.empty n) k c, rfl⟩

instance {e : Expression F} : LawfulCircuit (assert_zero e) where
  output n := ()
  final_offset n := n
  operations n := ⟨.assert (.empty n) e, rfl⟩

instance {l : Lookup F} : LawfulCircuit (lookup l) where
  output n := ()
  final_offset n := n
  operations n := ⟨.lookup (.empty n) l, rfl⟩

instance {β α: TypeMap} [ProvableType α] [ProvableType β] {circuit : FormalCircuit F β α} {input} :
    LawfulCircuit (subcircuit circuit input) where
  output n := circuit.output input n
  final_offset n := n + circuit.local_length input
  operations n := ⟨.subcircuit (.empty n) (circuit.to_subcircuit n input), rfl⟩

instance {β: TypeMap} [ProvableType β] {circuit : FormalAssertion F β} {input} :
    LawfulCircuit (assertion circuit input) where
  output n := ()
  final_offset n := n + circuit.local_length input
  operations n := ⟨.subcircuit (.empty n) (circuit.to_subcircuit n input), rfl⟩

syntax "infer_lawful_circuit" : tactic

macro_rules
  | `(tactic|infer_lawful_circuit) => `(tactic|(
    try intros
    try repeat infer_instance
    repeat (
      try intros
      apply LawfulCircuit.from_bind
      repeat infer_instance
    )))

-- this tactic is pretty good at inferring lawful circuits!
section
example : LawfulCircuit (witness (fun _ => (0 : F)))
  := by infer_lawful_circuit

example :
  let add := do
    let x : Expression F ← witness (fun _ => 0)
    let y ← witness (fun _ => 1)
    let z ← witness (fun eval => eval (x + y))
    assert_zero (x + y - z)
    pure z

  LawfulCircuit add := by infer_lawful_circuit
end

-- characterize the circuit.operations of lawful circuits
-- (ultimate goal: unfold constraints from the beginning)

-- helper lemma needed right below
lemma OperationsList.withLength_eq {F: Type} [Field F] {ops : OperationsList F} {ops' : Operations F ops.offset} :
  ops = ⟨ops.offset, ops'⟩ → ops.withLength = ops' := by
  intro h
  -- this is a nice trick: destruct dependent equality
  rcases ops with ⟨ offset, withLength ⟩
  rw [mk.injEq, heq_eq_eq] at h
  exact h.right

namespace LawfulCircuit
-- slightly different way to state the append-only principle, which deals with the type dependency
lemma append_only' {circuit : Circuit F α} [lawful : LawfulCircuit circuit] :
    ∀ ops: OperationsList F,
      (circuit ops).snd.withLength = ops.withLength ++ (lawful.offset_independent ops ▸ operations ops.offset) := by
  intro ops
  apply OperationsList.withLength_eq
  simp only [append_only ops]
  congr
  repeat exact offset_independent ops |>.symm
  rw [heq_eqRec_iff_heq, heq_eq_eq]

theorem final_offset_eq (circuit : Circuit F α) [LawfulCircuit circuit] (n : ℕ) :
  circuit.final_offset n = final_offset circuit n := by
  apply offset_independent

lemma operations_eq (circuit : Circuit F α) [LawfulCircuit circuit] (n : ℕ) :
    circuit.operations n = (final_offset_eq circuit n ▸ operations n).val := by
  rw [Circuit.operations, append_only', Operations.empty_append]

theorem initial_offset_eq (circuit : Circuit F α) [LawfulCircuit circuit] (n : ℕ) :
  (circuit.operations n).initial_offset = n := by
  rw [operations_eq circuit n]
  exact (final_offset_eq circuit n ▸ operations n).property

-- lemma operations_bind_length {f: Circuit F α} {g : α → Circuit F β}
--     (hg : ∀ a : α, LawfulCircuit (g a)) {n : ℕ} :
--     (f >>= g).final_offset n = (g (f.output n)).final_offset (f.final_offset n)
--    := by
--   unfold Circuit.final_offset
--   have : (f >>= g) n = (g (f n).1) (f n).2 := rfl
--   show ((g (f.output n)) (f n).2).2.offset = _
--   set a := f.output n
--   set opf := (f (OperationsList.from_offset n)).2
--   have ⟨ op_left, h_left ⟩ := LawfulCircuit.lawful (circuit := g a) opf
--   have ⟨ op_right, h_right ⟩ := LawfulCircuit.lawful (circuit := g a) opf.offset
--   -- rw [LawfulCircuit.operations_append (g a)]
--   sorry

-- theorem operations_bind_eq {f: Circuit F α} {g : α → Circuit F β}
--   (f_lawful : LawfulCircuit f) (g_lawful : ∀ a : α, LawfulCircuit (g a)) (n : ℕ) :
--     (f >>= g).operations n = (f_lawful.operations n ++ (g_lawful (output f n)).operations (final_offset f n)).val := by
--   apply LawfulCircuit.lawful -- why is this so easy? :D
end LawfulCircuit

-- loops

instance LawfulCircuit.from_forM {α: Type} {circuit : α → Circuit F Unit} :
    (∀ x : α, LawfulCircuit (circuit x)) → ∀ xs : List α, LawfulCircuit (forM xs circuit) := by
  intro h xs
  induction xs
  case nil => rw [List.forM_nil]; infer_instance
  case cons x xs ih =>
    rw [List.forM_cons]
    apply from_bind
    exact h x
    intro _
    exact ih

instance LawfulCircuit.from_forM_vector {α: Type} {circuit : α → Circuit F Unit} :
    (∀ x : α, LawfulCircuit (circuit x)) → ∀ (n : ℕ) (xs : Vector α n), LawfulCircuit (forM xs circuit) := by
  intro h n xs
  induction xs using Vector.induct
  case nil => simp only [Vector.forM_mk, List.forM_toArray, List.forM_eq_forM, List.forM_nil]; infer_instance
  case cons x xs ih =>
    rw [Vector.cons, Vector.forM_mk, List.forM_toArray, List.forM_eq_forM, List.forM_cons]
    apply from_bind
    exact h x
    intro _
    rw [Vector.forM_mk, List.forM_toArray] at ih
    exact ih
