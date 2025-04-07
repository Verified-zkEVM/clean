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

-- classify circuits by what they append to the current operations
namespace Circuit
def appends (circuit : Circuit F α) (op : (n : ℕ) → (m: ℕ) × OperationsFrom F n m) :=
  ∀ n : ℕ, ∀ ops: Operations F n, (circuit ops).snd = ops ++ (op n).snd

theorem pure_appends (a : α) : (pure a : Circuit F α).appends fun n => ⟨ n, .empty n ⟩ := by
  intro n ops; rfl

theorem witness_var_appends : ∀ c : Environment F → F,
  (witness_var c).appends fun n => ⟨n + 1, ⟨.witness (.empty n) 1 fun env => #v[c env], rfl⟩⟩ := by
  intros; intro n ops; rfl

theorem witness_vars_appends : ∀ (k : ℕ) (c : Environment F → Vector F k),
  (witness_vars k c).appends fun n => ⟨n + k, ⟨.witness (.empty n) k c, rfl⟩⟩ := by
  intros; intro n ops; rfl

theorem assert_zero_appends : ∀ e : Expression F,
  (assert_zero e).appends fun n => ⟨n, ⟨.assert (.empty n) e, rfl⟩⟩ := by
  intros; intro n ops; rfl

theorem lookup_appends : ∀ l : Lookup F,
  (lookup l).appends fun n => ⟨n, ⟨.lookup (.empty n) l, rfl⟩⟩ := by
  intros; intro n ops; rfl

theorem subcircuit_appends {β α: TypeMap} [ProvableType α] [ProvableType β] :
  ∀ (circuit : FormalCircuit F β α) (input),
  (subcircuit circuit input).appends fun n =>
    let s := Circuit.formal_circuit_to_subcircuit n circuit input
  ⟨n + s.local_length, ⟨.subcircuit (.empty n) s, rfl⟩⟩ := by
  intros; intro n ops; rfl
end Circuit

class LawfulCircuit (circuit : Circuit F α) where
  lawful : ∀ ops : OperationsList F, let n := (circuit ops).snd.offset;
    ∃ ops' : OperationsFrom F ops.offset n, (circuit ops).snd.withLength = ops.withLength ++ ops'

-- `bind` of two lawful circuits yields a lawful circuit
instance {f: Circuit F α} {g : α → Circuit F β} [hf : LawfulCircuit f] (hg : ∀ a : α, LawfulCircuit (g a)) : LawfulCircuit (f >>= g) where
  lawful := by
    intro ops n
    let ⟨ ops', happ ⟩ := hf.lawful ops
    let ⟨ ops'', happ' ⟩ := (hg (f ops).1).lawful (f ops).2
    rw [happ, Operations.append_assoc] at happ'
    use ops' ++ ops'', happ'

lemma OperationsList.withLength_eq {F: Type} [Field F] {ops : OperationsList F} {ops' : Operations F ops.offset} :
  ops = ⟨ ops.offset, ops'⟩ → ops.withLength = ops' := by
  intro h
  -- this is a nice trick: destruct dependent equality
  rcases ops with ⟨ offset, withLength ⟩
  rw [mk.injEq, heq_eq_eq] at h
  exact h.right

-- given an `appends` lemma for a circuit, we get a lawful circuit
instance LawfulCircuit.from_appends {circuit : Circuit F α} {op : (n : ℕ) → (m: ℕ) × OperationsFrom F n m}
  (happ : circuit.appends op) : LawfulCircuit circuit where
  lawful ops := by
    unfold Circuit.appends at happ
    specialize happ ops.offset ops
    change (circuit ops).snd = _ at happ
    have hn : (op ops.offset).fst = (circuit ops).snd.offset := by rw [happ]
    use hn ▸ (op ops.offset).snd
    apply OperationsList.withLength_eq
    simp only [happ]
    congr
    rw [heq_eqRec_iff_heq, heq_eq_eq]

-- `pure` is a lawful circuit
instance (a : α) : LawfulCircuit (pure a : Circuit F α) := .from_appends (Circuit.pure_appends a)

-- basic operations are lawful circuits
instance {c : Environment F → F} : LawfulCircuit (witness_var c) :=
  .from_appends (Circuit.witness_var_appends c)
instance {k : ℕ} {c : Environment F → Vector F k} : LawfulCircuit (witness_vars k c) :=
  .from_appends (Circuit.witness_vars_appends k c)
instance {e : Expression F} : LawfulCircuit (assert_zero e) :=
  .from_appends (Circuit.assert_zero_appends e)
instance {l : Lookup F} : LawfulCircuit (lookup l) :=
  .from_appends (Circuit.lookup_appends l)
instance {β α: TypeMap} [ProvableType α] [ProvableType β] {circuit : FormalCircuit F β α} {input} :
    LawfulCircuit (subcircuit circuit input) :=
  .from_appends (Circuit.subcircuit_appends circuit input)
