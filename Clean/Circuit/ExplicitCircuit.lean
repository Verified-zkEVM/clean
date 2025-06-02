-- TODO this has most of the previous content of `Clean.Circuit.Lawful`
-- could be useful to auto-derive the output/local_length/operations by tactic
import Clean.Circuit.Constant
variable {n m o : ℕ} {F : Type} [Field F] {α β : Type}

class ExplicitCircuit (circuit : Circuit F α) where
  /-- an "explicit" circuit is encapsulated by three functions of the input offset -/
  output : ℕ → α
  local_length : ℕ → ℕ
  operations : ℕ → Operations F

  /-- the function have to match the circuit -/
  output_eq : ∀ n: ℕ, circuit.output n = output n := by intro _; rfl
  local_length_eq : ∀ n: ℕ, circuit.local_length n = local_length n := by intro _; rfl
  operations_eq : ∀ n: ℕ, circuit.operations n = operations n := by intro _; rfl

-- slightly stronger variant: ExplicitCircuit with a fixed local length
class ConstantExplicitCircuit (circuit : Circuit F α) extends ConstantCircuit circuit where
  output : ℕ → α
  operations : ℕ → Operations F
  output_eq : ∀ n: ℕ, circuit.output n = output n := by intro _; rfl
  operations_eq : ∀ n: ℕ, circuit.operations n = operations n := by intro _; rfl

def ConstantExplicitCircuit.toExplicitCircuit (circuit : Circuit F α) [constant: ConstantExplicitCircuit circuit] : ExplicitCircuit circuit where
  output := constant.output
  local_length _ := constant.local_length
  operations := constant.operations
  output_eq := output_eq
  local_length_eq := constant.local_length_eq
  operations_eq := operations_eq

-- indexed family of explicit circuits that all share the same local length
class ConstantExplicitCircuits (circuit : α → Circuit F β) extends ConstantCircuits circuit where
  output : α → ℕ → β
  operations : α → ℕ → Operations F
  output_eq : ∀ (a : α) (n: ℕ), (circuit a).output n = output a n := by intro _ _; rfl
  operations_eq : ∀ (a : α) (n: ℕ), (circuit a).operations n = operations a n := by intro _ _; rfl

-- `pure` is a (constant) lawful circuit
instance ConstantExplicitCircuit.from_pure {a : α} : ConstantExplicitCircuit (pure a : Circuit F α) where
  output _ := a
  local_length := 0
  operations _ := []

instance ConstantExplicitCircuits.from_pure {f : α → β} : ConstantExplicitCircuits (fun a => pure (f a) : α → Circuit F β) where
  output a _ := f a
  local_length := 0
  operations _ _ := []

-- `bind` of two lawful circuits yields a lawful circuit
instance ExplicitCircuit.from_bind {f: Circuit F α} {g : α → Circuit F β}
    (f_lawful : ExplicitCircuit f) (g_lawful : ∀ a : α, ExplicitCircuit (g a)) : ExplicitCircuit (f >>= g) where
  output n :=
    let a := output f n
    output (g a) (n + local_length f n)

  local_length n :=
    let a := output f n
    local_length f n + local_length (g a) (n + local_length f n)

  operations n :=
    let a := output f n
    operations f n ++ operations (g a) (n + local_length f n)

  output_eq n := by rw [Circuit.bind_output_eq, output_eq, output_eq, local_length_eq]
  local_length_eq n := by rw [Circuit.bind_local_length_eq, local_length_eq, output_eq, local_length_eq]
  operations_eq n := by rw [Circuit.bind_operations_eq, operations_eq, output_eq, local_length_eq, operations_eq]

instance ExplicitCircuit.from_map {f : α → β} {g : Circuit F α}
    (g_lawful : ExplicitCircuit g) : ExplicitCircuit (f <$> g) where
  output n := output g n |> f
  local_length n := local_length g n
  operations n := operations g n

  output_eq n := by rw [Circuit.map_output_eq, output_eq]
  local_length_eq n := by rw [Circuit.map_local_length_eq, local_length_eq]
  operations_eq n := by rw [Circuit.map_operations_eq, operations_eq]

-- basic operations are (constant) lawful circuits

instance : ConstantExplicitCircuits (F:=F) witness_var where
  output _ n := ⟨ n ⟩
  local_length := 1
  operations c n := [.witness 1 fun env => #v[c env]]

instance {k : ℕ} {c : Environment F → Vector F k} : ConstantExplicitCircuit (witness_vars k c) where
  output n := .mapRange k fun i => ⟨n + i⟩
  local_length := k
  operations n := [.witness k c]

instance {α: TypeMap} [ProvableType α] : ConstantExplicitCircuits (ProvableType.witness (α:=α) (F:=F)) where
  output _ n := var_from_offset α n
  local_length := size α
  operations c n := [.witness (size α) (to_elements ∘ c)]

instance : ConstantExplicitCircuits (F:=F) assert_zero where
  output _ _ := ()
  local_length := 0
  operations e n := [.assert e]

instance : ConstantExplicitCircuits (F:=F) lookup where
  output _ _ := ()
  local_length := 0
  operations l n := [.lookup l]

instance {β α: TypeMap} [ProvableType α] [ProvableType β] {circuit : FormalCircuit F β α} {input} :
    ConstantExplicitCircuit (subcircuit circuit input) where
  output n := circuit.output input n
  local_length := circuit.local_length input
  operations n := [.subcircuit (circuit.to_subcircuit n input)]

instance {β: TypeMap} [ProvableType β] {circuit : FormalAssertion F β} {input} :
    ConstantExplicitCircuit (assertion circuit input) where
  output n := ()
  local_length := circuit.local_length input
  operations n := [.subcircuit (circuit.to_subcircuit n input)]

-- lower `ConstantLawfulCircuits` to `ConstantLawfulCircuit`
instance ConstantExplicitCircuits.to_single (circuit : α → Circuit F β) (a : α) [lawful : ConstantExplicitCircuits circuit] : ConstantExplicitCircuit (circuit a) where
  output n := output circuit a n
  local_length := lawful.local_length
  operations n := operations circuit a n
  output_eq := output_eq a
  local_length_eq := (ConstantCircuits.to_single circuit a).local_length_eq
  operations_eq := operations_eq a

instance ExplicitCircuit.from_constants {circuit : α → Circuit F β} (lawful : ConstantExplicitCircuits circuit) (a : α) :
    ExplicitCircuit (circuit a) := ConstantExplicitCircuits.to_single circuit a |>.toExplicitCircuit

syntax "infer_explicit_circuit" : tactic

macro_rules
  | `(tactic|infer_explicit_circuit) => `(tactic|(
    try intros
    try repeat infer_instance
    repeat (
      try intros
      first
        | apply ExplicitCircuit.from_bind
        | apply ExplicitCircuit.from_map
      repeat infer_instance
    )))

-- this tactic is pretty good at inferring lawful circuits!
section
example : ExplicitCircuit (witness (fun _ => (0 : F)))
  := by infer_explicit_circuit

example :
  let add := do
    let x : Expression F ← witness (fun _ => 0)
    let y ← witness (fun _ => 1)
    let z ← witness (fun eval => eval (x + y))
    assert_zero (x + y - z)
    pure z

  ExplicitCircuit add := by infer_explicit_circuit
end

-- `ConstantLawfulCircuit(s)` can be proved from `LawfulCircuit` by adding the requirement that `final_offset` is `n` plus a constant.
-- the latter can usually be proved by rfl!
open ExplicitCircuit in
def ConstantExplicitCircuit.from_constant_length {circuit : Circuit F α} (lawful : ExplicitCircuit circuit)
  (h_length : ∀ n, circuit.local_length n = circuit.local_length 0) : ConstantExplicitCircuit circuit where
  local_length := circuit.local_length 0
  local_length_eq := h_length

open ExplicitCircuit in
def ConstantExplicitCircuits.from_constant_length {circuit : α → Circuit F β} [Inhabited α] (lawful : ∀ a, ExplicitCircuit (circuit a))
  (h_length : ∀ a n, (circuit a).local_length n = (circuit default).local_length 0) : ConstantExplicitCircuits circuit where

  output a n := ExplicitCircuit.output (circuit a) n
  local_length := (circuit default).local_length 0
  operations a n := ExplicitCircuit.operations (circuit a) n

  output_eq a n := ExplicitCircuit.output_eq n
  local_length_eq a n := by
    show (circuit a).final_offset n = _
    rw [(lawful a).offset_consistent, h_length]
  append_only a n := by rw [ExplicitCircuit.append_only]
  offset_consistent a n := by rw [(lawful a).offset_consistent, h_length]
  local_length_eq a n := by rw [h_length]

syntax "infer_constant_lawful_elaborated_circuits" : tactic

macro_rules
  | `(tactic|infer_constant_lawful_elaborated_circuits) => `(tactic|(
    apply ConstantExplicitCircuits.from_constant_length (by infer_lawful_elaborated_circuit)
    try intros
    try simp only [ExplicitCircuit.final_offset]
    try ac_rfl))

section
example : ConstantExplicitCircuits (witness (F:=F))
  := by infer_constant_lawful_elaborated_circuits

example :
  let add (x : Expression F) := do
    let y ← witness (fun _ => (1 : F))
    let z ← witness (fun eval => eval (x + y))
    assert_zero (x + y - z)
    pure z

  ConstantExplicitCircuits add := by infer_constant_lawful_elaborated_circuits
end

-- characterize various properties of lawful circuits
-- TODO

namespace LawfulCircuit

theorem output_eq (circuit : Circuit F α) [LawfulCircuit circuit] (n : ℕ) :
    circuit.output n = output circuit n := by
  apply output_eq

theorem final_offset_eq (circuit : Circuit F α) [LawfulCircuit circuit] (n : ℕ) :
    circuit.final_offset n = final_offset circuit n := by
  apply local_length_eq

lemma operations_eq (circuit : Circuit F α) [LawfulCircuit circuit] (n : ℕ) :
    circuit.operations n = operations circuit n := by
  apply append_only

theorem local_length_eq (circuit : Circuit F α) [lawful: ConstantLawfulCircuit circuit] (n : ℕ) :
    circuit.local_length n = lawful.local_length := by
  apply Nat.add_left_cancel (n:=n)
  rw [←lawful.local_length_eq]
  rw [←final_offset_eq]

theorem local_length_eq' (circuit : Circuit F α) [lawful: ConstantLawfulCircuit circuit] (ops : OperationsList F) :
    (circuit ops).2.withLength.local_length = ops.withLength.local_length + lawful.local_length := by
  apply Nat.add_left_cancel (n:=(circuit ops).2.withLength.initial_offset)
  rw [←add_assoc, Circuit.total_length_eq, initial_offset_eq', Circuit.total_length_eq,
    local_length_eq, ←lawful.local_length_eq]

theorem bind_local_length (f : Circuit F α) (g : α → Circuit F β)
  (f_lawful: LawfulCircuit f) (g_lawful : ∀ a : α, LawfulCircuit (g a)) (n : ℕ) :
    (f >>= g).local_length n = f.local_length n + (g (f.output n)).local_length (f.final_offset n) := by
  apply Nat.add_left_cancel (n:=n)
  let fg_lawful : LawfulCircuit (f >>= g) := .from_bind inferInstance inferInstance
  rw (occs := .pos [1]) [←fg_lawful.initial_offset_eq _ n]
  rw [Circuit.total_length_eq, final_offset_eq]
  rw (occs := .pos [2]) [←f_lawful.initial_offset_eq _ n]
  rw [←add_assoc, Circuit.total_length_eq, final_offset_eq]
  rw (occs := .pos [1]) [←(g_lawful (f.output n)).initial_offset_eq _ (final_offset f n)]
  rw [Circuit.total_length_eq, final_offset_eq]
  simp only [fg_lawful, final_offset]
  rw [←LawfulCircuit.output_eq (.from_offset n)]

theorem soundness_eq {circuit : Circuit F α} [lawful : LawfulCircuit circuit] {env} {n : ℕ} :
    Circuit.constraints_hold.soundness env (circuit.operations n) ↔ Circuit.constraints_hold.soundness env (lawful.operations n).val :=
  LawfulCircuit.operations_eq' (Circuit.constraints_hold.soundness env)

theorem completeness_eq {circuit : Circuit F α} [lawful : LawfulCircuit circuit] {env} {n : ℕ} :
    Circuit.constraints_hold.completeness env (circuit.operations n) ↔ Circuit.constraints_hold.completeness env (lawful.operations n).val :=
  LawfulCircuit.operations_eq' (Circuit.constraints_hold.completeness env)
end LawfulCircuit

namespace ConstantLawfulCircuits
theorem output_eq {circuit : α → Circuit F β} [lawful : ConstantLawfulCircuits circuit] :
    ∀ (a : α) (n : ℕ), (circuit a).output n = lawful.output a n := by
  intros; apply output_eq

theorem final_offset_eq {circuit : α → Circuit F β} [lawful : ConstantLawfulCircuits circuit] :
    ∀ (a : α) (n : ℕ), (circuit a).final_offset n = n + lawful.local_length := by
  intros; apply local_length_eq

theorem initial_offset_eq {circuit : α → Circuit F β} [lawful : ConstantLawfulCircuits circuit] :
    ∀ (a : α) (n : ℕ), ((circuit a).operations n).initial_offset = n := by
  intro a n
  have : LawfulCircuit (circuit a) := lawful.to_single _ _ |>.toLawfulCircuit
  apply LawfulCircuit.initial_offset_eq

theorem local_length_eq {circuit : α → Circuit F β} [lawful : ConstantLawfulCircuits circuit] :
    ∀ (a : α) (n : ℕ), (circuit a).local_length n = lawful.local_length := by
  intros; apply LawfulCircuit.local_length_eq
end ConstantLawfulCircuits

namespace Circuit.constraints_hold
variable {env : Environment F} {n : ℕ} {prop : Operations.Condition F}

theorem bind_forAll {f : Circuit F α} {g : α → Circuit F β} (f_lawful: LawfulCircuit f) (g_lawful : ∀ a, LawfulCircuit (g a)) :
  ((f >>= g).operations n).forAll prop ↔
    (f.operations n).forAll prop ∧
      ((g (LawfulCircuit.output f n)).operations (LawfulCircuit.final_offset f n)).forAll prop := by
  open LawfulCircuit in
  let fg_lawful : LawfulCircuit (f >>= g) := .from_bind inferInstance inferInstance
  simp only [LawfulCircuit.operations_eq' (Operations.forAll prop)]
  have h_length : fg_lawful.final_offset n = (g_lawful (f_lawful.output n)).final_offset (f_lawful.final_offset n) := by
    simp only [fg_lawful, from_bind]
  have h_ops : fg_lawful.operations n = f_lawful.operations n ++ h_length ▸ (g_lawful (f_lawful.output n)).operations (f_lawful.final_offset n) := by
    simp only [fg_lawful, from_bind]
  rw [h_ops, OperationsFrom.append_val, append_forAll]

theorem bind_forAll' {f : Circuit F α} {g : α → Circuit F β} (f_lawful: LawfulCircuit f) (g_lawful : ∀ a, LawfulCircuit (g a))
  (ops : OperationsList F) :
  ((f >>= g) ops).2.withLength.forAll prop ↔
    (f ops).2.withLength.forAll prop ∧
      ((g (LawfulCircuit.output f ops.offset)).operations (f ops).2.offset).forAll prop := by
  open LawfulCircuit in
  let fg_lawful : LawfulCircuit (f >>= g) := .from_bind inferInstance inferInstance
  rw [append_only, append_only]
  simp only
  rw [append_forAll, append_forAll]
  simp only [←LawfulCircuit.operations_eq' (Operations.forAll prop)]
  simp only [bind_forAll]
  simp only [and_assoc, and_assoc]

-- specializations to soundness / completeness

theorem bind_soundness {f : Circuit F α} {g : α → Circuit F β} (f_lawful: LawfulCircuit f) (g_lawful : ∀ a, LawfulCircuit (g a)) :
    soundness env ((f >>= g).operations n) ↔
    soundness env (f.operations n) ∧ soundness env ((g (LawfulCircuit.output f n)).operations (LawfulCircuit.final_offset f n)) := by
  simp only [soundness_iff_forAll, bind_forAll]

theorem bind_completeness {f : Circuit F α} {g : α → Circuit F β} (f_lawful: LawfulCircuit f) (g_lawful : ∀ a, LawfulCircuit (g a)) :
    completeness env ((f >>= g).operations n) ↔
    completeness env (f.operations n) ∧ completeness env ((g (LawfulCircuit.output f n)).operations (LawfulCircuit.final_offset f n)) := by
  simp only [completeness_iff_forAll, bind_forAll]
end Circuit.constraints_hold

attribute [lawful_norm] LawfulCircuit.final_offset LawfulCircuit.operations LawfulCircuit.output ConstantLawfulCircuit.local_length
attribute [lawful_norm] ConstantLawfulCircuits.output ConstantLawfulCircuits.local_length ConstantLawfulCircuits.operations
  ConstantLawfulCircuits.from_constant_length id_eq
attribute [lawful_norm] ElaboratedCircuit.local_length ElaboratedCircuit.output
