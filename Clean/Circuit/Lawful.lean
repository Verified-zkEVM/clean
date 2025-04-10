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

theorem self_val (as : Operations F n) : as = (⟨ as, rfl ⟩ : OperationsFrom F as.initial_offset n).val := rfl

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

-- slightly stronger variant: LawfulCircuit with a fixed local length
class ConstantLawfulCircuit (circuit : Circuit F α) extends LawfulCircuit circuit where
  local_length : ℕ
  local_length_eq : ∀ n : ℕ, final_offset n = n + local_length := by intro _; rfl
  final_offset n := n + local_length

-- even stronger (and still the typical case): an indexed family of lawful circuits that all share the same local length
class ConstantLawfulCircuits (circuit : α → Circuit F β) where
  output : α → ℕ → β
  local_length : ℕ
  operations : α → (n : ℕ) → OperationsFrom F n (n + local_length)

  output_independent : ∀ (a : α) (ops: OperationsList F), (circuit a ops).fst = output a ops.offset := by intro _ _; rfl
  offset_independent : ∀ (a : α) (ops: OperationsList F), (circuit a ops).snd.offset = ops.offset + local_length := by intro _ _; rfl
  append_only : ∀ (a : α) (ops: OperationsList F), (circuit a ops).snd = ops.withLength ++ operations a ops.offset := by intro _ _; rfl

-- `pure` is a (constant) lawful circuit
instance LawfulCircuit.from_pure {a : α} : ConstantLawfulCircuit (pure a : Circuit F α) where
  output _ := a
  local_length := 0
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

-- basic operations are (constant) lawful circuits

instance {c : Environment F → F} : ConstantLawfulCircuit (witness_var c) where
  output n := ⟨ n ⟩
  local_length := 1
  operations n := ⟨.witness (.empty n) 1 fun env => #v[c env], rfl⟩

instance {k : ℕ} {c : Environment F → Vector F k} : ConstantLawfulCircuit (witness_vars k c) where
  output n := .natInit k fun i => ⟨n + i⟩
  local_length := k
  operations n := ⟨.witness (.empty n) k c, rfl⟩

instance {e : Expression F} : ConstantLawfulCircuit (assert_zero e) where
  output n := ()
  local_length := 0
  operations n := ⟨.assert (.empty n) e, rfl⟩

instance {l : Lookup F} : ConstantLawfulCircuit (lookup l) where
  output n := ()
  local_length := 0
  operations n := ⟨.lookup (.empty n) l, rfl⟩

instance {β α: TypeMap} [ProvableType α] [ProvableType β] {circuit : FormalCircuit F β α} {input} :
    ConstantLawfulCircuit (subcircuit circuit input) where
  output n := circuit.output input n
  local_length := circuit.local_length input
  operations n := ⟨.subcircuit (.empty n) (circuit.to_subcircuit n input), rfl⟩

instance {β: TypeMap} [ProvableType β] {circuit : FormalAssertion F β} {input} :
    ConstantLawfulCircuit (assertion circuit input) where
  output n := ()
  local_length := circuit.local_length input
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

-- lower `ConstantLawfulCircuits` to `ConstantLawfulCircuit`
instance ConstantLawfulCircuits.to_single (circuit : α → Circuit F β) (a : α) [lawful : ConstantLawfulCircuits circuit] : ConstantLawfulCircuit (circuit a) where
  output n := lawful.output a n
  local_length := lawful.local_length
  operations n := lawful.operations a n
  output_independent := lawful.output_independent a
  offset_independent := lawful.offset_independent a
  append_only := lawful.append_only a

-- constant version of `bind`
instance ConstantLawfulCircuit.from_bind {f: Circuit F α} {g : α → Circuit F β}
    [f_lawful : ConstantLawfulCircuit f] [g_lawful : ConstantLawfulCircuits g] : ConstantLawfulCircuit (f >>= g) where
  output n :=
    let nf := f_lawful.local_length
    let a := f_lawful.output n
    g_lawful.output a (n + nf)

  local_length := f_lawful.local_length + g_lawful.local_length
  final_offset n := f_lawful.final_offset n + g_lawful.local_length
  local_length_eq n := by
    show f_lawful.final_offset n + g_lawful.local_length = _
    rw [f_lawful.local_length_eq, add_assoc]

  operations n :=
    let n' := f_lawful.final_offset n
    let a := f_lawful.output n
    let ops_f := f_lawful.operations n
    let ops_g := g_lawful.operations a n'
    ops_f ++ ops_g

  output_independent ops := by
    show (g _ _).1 = _
    rw [g_lawful.output_independent, f_lawful.output_independent, f_lawful.offset_independent, f_lawful.local_length_eq]

  offset_independent ops := by
    show (g _ _).2.offset = _
    rw [g_lawful.offset_independent, f_lawful.offset_independent]

  append_only ops := by
    show (g _ _).2 = _
    rw [g_lawful.append_only, f_lawful.output_independent, f_lawful.append_only, Operations.append_assoc]

-- TODO tactic to infer `ConstantLawfulCircuit(s)`
-- this probably just needs to use a combination of `infer_instance` and `ConstantLawfulCircuit.from_bind`
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

theorem constraints_hold_eq.soundness (circuit : Circuit F α) [lawful : LawfulCircuit circuit] (env : Environment F) (n : ℕ) :
  Circuit.constraints_hold.soundness env (circuit.operations n) ↔
    Circuit.constraints_hold.soundness env (lawful.operations n).val := by
  rw [operations_eq, iff_iff_eq]
  have h_off : circuit.final_offset n = final_offset circuit n := final_offset_eq circuit n
  congr
  · apply Function.hfunext; congr; intros; congr
  · rw [eqRec_heq_iff_heq, heq_eq_eq]

end LawfulCircuit

theorem Circuit.constraints_hold_append.soundness (env : Environment F) (as : Operations F m) (bs : OperationsFrom F m n) :
  constraints_hold.soundness env (as ++ bs) ↔
    constraints_hold.soundness env as ∧ constraints_hold.soundness env bs.val := by
  simp only [constraints_hold.soundness'_iff_soundness]
  induction bs using OperationsFrom.induct with
  | empty n => rw [Operations.append_empty]; tauto
  | witness bs k c ih | assert bs _ ih | lookup bs _ ih | subcircuit bs _ ih =>
    specialize ih as
    simp only [Operations.append_lookup, Operations.append_assert, Operations.append_witness, Operations.append_subcircuit]
    simp only [OperationsFrom.lookup, OperationsFrom.assert, OperationsFrom.witness, OperationsFrom.subcircuit]
    simp only [constraints_hold.soundness', ih]
    try tauto

theorem Circuit.constraints_hold_bind.soundness (env : Environment F)
  (f : Circuit F α) (g : α → Circuit F β) [f_lawful: LawfulCircuit f] [g_lawful : ∀ a, LawfulCircuit (g a)] (n : ℕ) :
  constraints_hold.soundness env ((f >>= g).operations n) ↔
    constraints_hold.soundness env (f.operations n)
    ∧ constraints_hold.soundness env ((g (LawfulCircuit.output f n)).operations (LawfulCircuit.final_offset f n)) := by
  open LawfulCircuit in
  let fg_lawful : LawfulCircuit (f >>= g) := .from_bind inferInstance inferInstance
  simp only [constraints_hold_eq.soundness]
  have h_length : fg_lawful.final_offset n = (g_lawful (f_lawful.output n)).final_offset (f_lawful.final_offset n) := by
    simp only [fg_lawful, from_bind]
  have h_ops : fg_lawful.operations n = f_lawful.operations n ++ h_length ▸ (g_lawful (f_lawful.output n)).operations (f_lawful.final_offset n) := by
    simp only [fg_lawful, from_bind]
  rw [h_ops, OperationsFrom.append_val, constraints_hold_append.soundness]

-- loops

instance LawfulCircuit.from_forM {α: Type} {circuit : α → Circuit F Unit} [h : ∀ x : α, LawfulCircuit (circuit x)] (xs : List α) :
     LawfulCircuit (forM xs circuit) := by
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

theorem Circuit.constraints_hold_forM.soundness
  (env : Environment F) (circuit : α → Circuit F Unit) [lawful : ConstantLawfulCircuits circuit]
  (xs : List α) (n : ℕ) :
    constraints_hold.soundness env (forM xs circuit |>.operations n) ↔
      xs.zipIdx.Forall fun (x, i) => constraints_hold.soundness env (circuit x |>.operations (n + i*lawful.local_length)) := by

  induction xs generalizing n with
  | nil => simp [circuit_norm]
  | cons x xs ih =>
    rw [List.forM_cons, List.zipIdx_cons, List.forall_cons]
    simp only at ih ⊢
    rw [zero_mul, add_zero, zero_add]
    specialize ih (n + lawful.local_length)

    have h_zip : List.Forall (fun (x, i) ↦ constraints_hold.soundness env ((circuit x).operations (n + lawful.local_length + i * lawful.local_length))) xs.zipIdx
      ↔ List.Forall (fun (x, i) ↦ constraints_hold.soundness env ((circuit x).operations (n + i * lawful.local_length))) (xs.zipIdx 1) := by
      rw [List.zipIdx_succ, List.forall_map_iff]
      conv =>
        rhs
        change List.Forall (fun (x, i) ↦ constraints_hold.soundness env ((circuit x).operations (n + (i + 1) * lawful.local_length))) xs.zipIdx
        lhs
        intro t
        simp only
        rw [add_mul, one_mul, add_comm _ lawful.local_length, ←add_assoc]

    rw [←h_zip, ←ih]
    clear h_zip ih
    rw [constraints_hold_bind.soundness]
    exact Iff.intro id id
