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

def OperationsFrom.witness (as : OperationsFrom F m n) (k : ℕ) (c : Environment F → Vector F k) : OperationsFrom F m (n + k) :=
  .mk (.witness as.val k c) as.property
def OperationsFrom.assert (as : OperationsFrom F m n) (e : Expression F) : OperationsFrom F m n :=
  .mk (.assert as.val e) as.property
def OperationsFrom.lookup (as : OperationsFrom F m n) (l : Lookup F) : OperationsFrom F m n :=
  .mk (.lookup as.val l) as.property
def OperationsFrom.subcircuit (as : OperationsFrom F m n) (s : SubCircuit F n) : OperationsFrom F m (n + s.local_length) :=
  .mk (.subcircuit as.val s) as.property

-- induction principle for OperationsFrom
def OperationsFrom.induct' {F: Type} [Field F] {motive : {n m: ℕ} → OperationsFrom F m n → Prop}
  (empty : ∀ (n), motive (n:=n) (m:=n) (.empty n))
  (witness : ∀ {n m} (as : Operations F n) (k c) (ha : as.initial_offset = m),
    motive (.mk as ha) → motive (.mk (.witness as k c) ha))
  (assert : ∀ {n m} (as : Operations F n) (e) (ha : as.initial_offset = m),
    motive (.mk as ha) → motive (.mk (.assert as e) ha))
  (lookup : ∀ {n m} (as : Operations F n) (l) (ha : as.initial_offset = m),
    motive (.mk as ha) → motive (.mk (.lookup as l) ha))
  (subcircuit : ∀ {n m} (as : Operations F n) (s) (ha : as.initial_offset = m),
    motive (.mk as ha) → motive (.mk (.subcircuit as s) ha))
  {n m: ℕ} (as: OperationsFrom F m n) : motive as :=
  motive' as.val as.property
where
  motive' {n m} : (as : Operations F n) → (ha: as.initial_offset = m) → motive (.mk as ha)
  | .empty n, rfl => empty n
  | .witness _ _ _, _ => witness _ _ _ _ (motive' _ _)
  | .assert _ _, _ => assert _ _ _ (motive' _ _)
  | .lookup _ _, _ => lookup _ _ _ (motive' _ _)
  | .subcircuit _ _, _ => subcircuit _ _ _ (motive' _ _)

def OperationsFrom.induct {F: Type} [Field F] {motive : {n m: ℕ} → OperationsFrom F m n → Prop}
  (empty : ∀ (n), motive (n:=n) (m:=n) (.empty n))
  (witness : ∀ {n m} (as : OperationsFrom F m n) (k c), motive as → motive (.witness as k c))
  (assert : ∀ {n m} (as : OperationsFrom F m n) (e), motive as → motive (.assert as e))
  (lookup : ∀ {n m} (as : OperationsFrom F m n) (l), motive as → motive (.lookup as l))
  (subcircuit : ∀ {n m} (as : OperationsFrom F m n) (s), motive as → motive (.subcircuit as s))
    {n m: ℕ} (as: OperationsFrom F m n) : motive as := by
  induction as using OperationsFrom.induct' with
  | empty n => exact empty n
  | witness as k c ha ih => exact witness _ _ _ ih
  | assert as e ha ih => exact assert _ _ ih
  | lookup as l ha ih => exact lookup _ _ ih
  | subcircuit as s ha ih => exact subcircuit _ _ ih

namespace Operations
instance : HAppend (Operations F m) (OperationsFrom F m n) (Operations F n) where
  hAppend as bs := as.append bs.val bs.property

theorem append_empty (as : Operations F n) : as ++ (OperationsFrom.empty (F:=F) n) = as := rfl

theorem empty_append (as : OperationsFrom F n m) : empty (F:=F) n ++ as = as.val := by
  induction as using OperationsFrom.induct' with
  | empty n => rfl
  | witness | assert | lookup | subcircuit => simp_all only [HAppend.hAppend, append]

theorem append_witness (as : Operations F m) (bs : OperationsFrom F m n) (k : ℕ) (c : Environment F → Vector F k) :
  as ++ (OperationsFrom.witness bs k c) = .witness (as ++ bs) k c := by rfl
theorem append_assert (as : Operations F m) (bs : OperationsFrom F m n) (e : Expression F) :
  as ++ (OperationsFrom.assert bs e) = .assert (as ++ bs) e := by rfl
theorem append_lookup (as : Operations F m) (bs : OperationsFrom F m n) (l : Lookup F) :
  as ++ (OperationsFrom.lookup bs l) = .lookup (as ++ bs) l := by rfl
theorem append_subcircuit (as : Operations F m) (bs : OperationsFrom F m n) (s : SubCircuit F n) :
  as ++ (OperationsFrom.subcircuit bs s) = .subcircuit (as ++ bs) s := by rfl

theorem append_initial_offset {m n: ℕ} (as : Operations F m) (bs : OperationsFrom F m n) :
    (as ++ bs).initial_offset = as.initial_offset := by
  induction bs using OperationsFrom.induct with
  | empty n => rfl
  | witness bs _ _ ih | assert bs _ ih | lookup bs _ ih | subcircuit bs _ ih => exact ih as

instance : HAppend (OperationsFrom F m n) (OperationsFrom F n o) (OperationsFrom F m o) where
  hAppend as bs := ⟨ as.val.append bs.val bs.property, by
    show (as.val ++ bs).initial_offset = m
    rw [append_initial_offset, as.property] ⟩

theorem append_assoc {m n o: ℕ} (as : Operations F m) (bs : OperationsFrom F m n) (cs : OperationsFrom F n o) :
  (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  induction cs using OperationsFrom.induct' with
  | empty n => rfl
  | witness _ _ _ _ ih | assert _ _ _ ih | lookup _ _ _ ih | subcircuit _ _ _ ih =>
    simp only [HAppend.hAppend, append, witness.injEq, assert.injEq, lookup.injEq, subcircuit.injEq, and_true]
    exact ih bs
end Operations

namespace OperationsFrom
theorem append_val (as : OperationsFrom F m n) (bs : OperationsFrom F n o) :
    (as ++ bs).val = as.val ++ bs := by
  dsimp only [HAppend.hAppend]

theorem empty_val (n : ℕ) : (empty (F:=F) n).val = Operations.empty n := rfl

theorem append_empty (as : OperationsFrom F m n) : as ++ empty (F:=F) n = as := rfl

theorem empty_append (as : OperationsFrom F m n) : empty (F:=F) m ++ as = as := by
  ext; rw [append_val, empty_val, Operations.empty_append]

theorem append_assoc {p: ℕ} (as : OperationsFrom F m n) (bs : OperationsFrom F n o) (cs : OperationsFrom F o p) :
  (as ++ bs) ++ cs = as ++ (bs ++ cs) := by
  ext; simp only [append_val, Operations.append_assoc]
end OperationsFrom

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
end LawfulCircuit

namespace Circuit
theorem constraints_hold_soundness_append (env : Environment F) (as : Operations F m) (bs : OperationsFrom F m n) :
  constraints_hold.soundness env (as ++ bs) ↔
    (constraints_hold.soundness env as ∧ constraints_hold.soundness env bs.val) := by
  repeat rw [constraints_hold.soundness'_iff_soundness]
  induction bs using OperationsFrom.induct with
  | empty n => rw [Operations.append_empty]; tauto
  | witness bs k c ih | assert bs _ ih | lookup bs _ ih | subcircuit bs _ ih =>
    specialize ih as
    simp only [Operations.append_lookup, Operations.append_assert, Operations.append_witness, Operations.append_subcircuit]
    simp only [OperationsFrom.lookup, OperationsFrom.assert, OperationsFrom.witness, OperationsFrom.subcircuit]
    simp only [constraints_hold.soundness', ih]
    try tauto
end Circuit

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
