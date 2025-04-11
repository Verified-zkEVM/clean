import Clean.Circuit.Append
import Clean.Circuit.SubCircuit
variable {n m o : ℕ} {F : Type} [Field F] {α β : Type}

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

instance ConstantLawfulCircuits.from_pure {f : α → β} : ConstantLawfulCircuits (fun a => pure (f a) : α → Circuit F β) where
  output a _ := f a
  local_length := 0
  operations _ n := .empty n

-- `bind` of two lawful circuits yields a lawful circuit
instance LawfulCircuit.from_bind {f: Circuit F α} {g : α → Circuit F β}
    (f_lawful : LawfulCircuit f) (g_lawful : ∀ a : α, LawfulCircuit (g a)) : LawfulCircuit (f >>= g) where
  output n :=
    let a := output f n
    output (g a) (final_offset f n)

  final_offset n :=
    let a := output f n
    final_offset (g a) (final_offset f n)

  operations n :=
    let a := output f n
    let ops_f := f_lawful.operations n
    let ops_g := (g_lawful a).operations (final_offset f n)
    ops_f ++ ops_g

  output_independent ops := by
    show (g _ _).1 = _ -- by definition, `(f >>= g) ops = g (f ops).1 (f ops).2`
    rw [output_independent, output_independent, offset_independent]

  offset_independent ops := by
    show (g _ _).2.offset = _
    rw [offset_independent, output_independent, offset_independent]

  append_only ops := by
    show (g _ _).2 = _
    rw [append_only, output_independent, append_only, Operations.append_assoc]

-- basic operations are (constant) lawful circuits

instance : ConstantLawfulCircuits (F:=F) witness_var where
  output _ n := ⟨ n ⟩
  local_length := 1
  operations c n := ⟨.witness (.empty n) 1 fun env => #v[c env], rfl⟩

instance {k : ℕ} {c : Environment F → Vector F k} : ConstantLawfulCircuit (witness_vars k c) where
  output n := .natInit k fun i => ⟨n + i⟩
  local_length := k
  operations n := ⟨.witness (.empty n) k c, rfl⟩

instance : ConstantLawfulCircuits (F:=F) assert_zero where
  output _ _ := ()
  local_length := 0
  operations e n := ⟨.assert (.empty n) e, rfl⟩

instance : ConstantLawfulCircuits (F:=F) lookup where
  output _ _ := ()
  local_length := 0
  operations l n := ⟨.lookup (.empty n) l, rfl⟩

instance {β α: TypeMap} [ProvableType α] [ProvableType β] {circuit : FormalCircuit F β α} {input} :
    ConstantLawfulCircuit (subcircuit circuit input) where
  output n := circuit.output input n
  local_length := circuit.local_length input
  final_offset n := n + circuit.local_length input
  operations n := ⟨.subcircuit (.empty n) (circuit.to_subcircuit n input), rfl⟩

instance {β: TypeMap} [ProvableType β] {circuit : FormalAssertion F β} {input} :
    ConstantLawfulCircuit (assertion circuit input) where
  output n := ()
  local_length := circuit.local_length input
  final_offset n := n + circuit.local_length input
  operations n := ⟨.subcircuit (.empty n) (circuit.to_subcircuit n input), rfl⟩

-- lower `ConstantLawfulCircuits` to `ConstantLawfulCircuit`
instance ConstantLawfulCircuits.to_single (circuit : α → Circuit F β) (a : α) [lawful : ConstantLawfulCircuits circuit] : ConstantLawfulCircuit (circuit a) where
  output n := output circuit a n
  local_length := local_length circuit
  operations n := operations a n
  output_independent := output_independent a
  offset_independent := offset_independent a
  append_only := append_only a

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

-- constant version of `bind`
open LawfulCircuit in
instance ConstantLawfulCircuit.from_bind {f: Circuit F α} {g : α → Circuit F β}
    (f_lawful : ConstantLawfulCircuit f) (g_lawful : ConstantLawfulCircuits g) : ConstantLawfulCircuit (f >>= g) where
  output n :=
    let a := output f n
    g_lawful.output a (n + local_length f)

  local_length := local_length f + g_lawful.local_length
  final_offset n := final_offset f n + g_lawful.local_length
  local_length_eq n := by
    show final_offset f n + g_lawful.local_length = _
    rw [local_length_eq, add_assoc]

  operations n :=
    let a := output f n
    let ops_f := f_lawful.operations n
    let ops_g := g_lawful.operations a (final_offset f n)
    ops_f ++ ops_g

  output_independent ops := by
    show (g _ _).1 = _
    rw [g_lawful.output_independent, output_independent, offset_independent, local_length_eq]

  offset_independent ops := by
    show (g _ _).2.offset = _
    rw [g_lawful.offset_independent, offset_independent]

  append_only ops := by
    show (g _ _).2 = _
    rw [g_lawful.append_only, output_independent, append_only, Operations.append_assoc]

-- TODO inferring `ConstantLawfulCircuit` doesn't work yet.
-- the problem is that in every successive bind, in general, you get one more dependent variable in the second function.
-- i.e. we would need `ConstantLawfulCircuits (α → β)`, `ConstantLawfulCircuitss (α → β → γ)` etc.

-- characterize various properties of lawful circuits

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

theorem operations_eq' (motive : {n : ℕ} → Operations F n → Prop)
    {circuit : Circuit F α} [lawful : LawfulCircuit circuit] {n : ℕ} :
  motive (circuit.operations n) ↔ motive (lawful.operations n).val := by
  rw [operations_eq, iff_iff_eq]
  have h_off : circuit.final_offset n = final_offset circuit n := final_offset_eq circuit n
  congr
  · apply Function.hfunext; congr; intros; congr
  · rw [eqRec_heq_iff_heq, heq_eq_eq]

theorem initial_offset_eq (circuit : Circuit F α) [LawfulCircuit circuit] (n : ℕ) :
    (circuit.operations n).initial_offset = n := by
  rw [operations_eq circuit n]
  exact (final_offset_eq circuit n ▸ operations n).property

theorem local_length_eq (circuit : Circuit F α) [lawful: ConstantLawfulCircuit circuit] (n : ℕ) :
    (circuit.operations n).local_length = lawful.local_length := by
  apply Nat.add_left_cancel (n:=n)
  rw [←lawful.local_length_eq]
  rw (occs := .pos [1]) [←initial_offset_eq circuit n]
  rw [Circuit.total_length_eq, final_offset_eq]

theorem bind_local_length (f : Circuit F α) (g : α → Circuit F β)
  [f_lawful: LawfulCircuit f] [g_lawful : ∀ a : α, LawfulCircuit (g a)] (n : ℕ) :
    ((f >>= g).operations n).local_length = (f.operations n).local_length + ((g (f.output n)).operations (f.final_offset n)).local_length := by
  apply Nat.add_left_cancel (n:=n)
  let fg_lawful : LawfulCircuit (f >>= g) := .from_bind inferInstance inferInstance
  rw (occs := .pos [1]) [←fg_lawful.initial_offset_eq _ n]
  rw [Circuit.total_length_eq, final_offset_eq]
  rw (occs := .pos [2]) [←f_lawful.initial_offset_eq _ n]
  rw [←add_assoc, Circuit.total_length_eq, final_offset_eq]
  rw (occs := .pos [1]) [←(g_lawful (f.output n)).initial_offset_eq _ (final_offset f n)]
  rw [Circuit.total_length_eq, final_offset_eq]
  simp only [fg_lawful, final_offset]
  rw [←LawfulCircuit.output_independent (.from_offset n)]

theorem soundness_eq {circuit : Circuit F α} [lawful : LawfulCircuit circuit] {env} {n : ℕ} :
    Circuit.constraints_hold.soundness env (circuit.operations n) ↔ Circuit.constraints_hold.soundness env (lawful.operations n).val :=
  LawfulCircuit.operations_eq' (Circuit.constraints_hold.soundness env)

theorem completeness_eq {circuit : Circuit F α} [lawful : LawfulCircuit circuit] {env} {n : ℕ} :
    Circuit.constraints_hold.completeness env (circuit.operations n) ↔ Circuit.constraints_hold.completeness env (lawful.operations n).val :=
  LawfulCircuit.operations_eq' (Circuit.constraints_hold.completeness env)
end LawfulCircuit

namespace Circuit.constraints_hold
variable {env : Environment F} {n : ℕ} (from_subcircuit : {n : ℕ} → Environment F → SubCircuit F n → Prop)

theorem bind_generic {f : Circuit F α} {g : α → Circuit F β} (f_lawful: LawfulCircuit f) (g_lawful : ∀ a, LawfulCircuit (g a)) :
  generic from_subcircuit env ((f >>= g).operations n) ↔
    generic from_subcircuit env (f.operations n)
    ∧ generic from_subcircuit env ((g (LawfulCircuit.output f n)).operations (LawfulCircuit.final_offset f n)) := by
  open LawfulCircuit in
  let fg_lawful : LawfulCircuit (f >>= g) := .from_bind inferInstance inferInstance
  simp only [LawfulCircuit.operations_eq' (generic from_subcircuit env)]
  have h_length : fg_lawful.final_offset n = (g_lawful (f_lawful.output n)).final_offset (f_lawful.final_offset n) := by
    simp only [fg_lawful, from_bind]
  have h_ops : fg_lawful.operations n = f_lawful.operations n ++ h_length ▸ (g_lawful (f_lawful.output n)).operations (f_lawful.final_offset n) := by
    simp only [fg_lawful, from_bind]
  rw [h_ops, OperationsFrom.append_val, append_generic]

-- specializations to soundness / completeness

theorem bind_soundness {f : Circuit F α} {g : α → Circuit F β} (f_lawful: LawfulCircuit f) (g_lawful : ∀ a, LawfulCircuit (g a)) :
    soundness env ((f >>= g).operations n) ↔
    soundness env (f.operations n) ∧ soundness env ((g (LawfulCircuit.output f n)).operations (LawfulCircuit.final_offset f n)) := by
  simp only [soundness_iff_generic, bind_generic]

theorem bind_completeness {f : Circuit F α} {g : α → Circuit F β} (f_lawful: LawfulCircuit f) (g_lawful : ∀ a, LawfulCircuit (g a)) :
    completeness env ((f >>= g).operations n) ↔
    completeness env (f.operations n) ∧ completeness env ((g (LawfulCircuit.output f n)).operations (LawfulCircuit.final_offset f n)) := by
  simp only [completeness_iff_generic, bind_generic]
end Circuit.constraints_hold
