-- TODO this has most of the previous content of `Clean.Circuit.Lawful`
-- could be useful to auto-derive the output/local_length/operations by tactic
import Clean.Circuit.Constant
variable {n m o : ℕ} {F : Type} [Field F] {α β : Type}

class LawfulElaboratedCircuit (circuit : Circuit F α) extends LawfulCircuit circuit where
  /-- a proper circuit is encapsulated by three functions of the input offset -/
  output : ℕ → α
  final_offset : ℕ → ℕ
  operations : ℕ → Operations F

  /-- the circuit's output and final offset only depend on the input offset -/
  output_independent : ∀ offset: ℕ, (circuit offset).fst.fst = output offset := by intro _; rfl
  offset_independent : ∀ offset: ℕ, (circuit offset).snd = final_offset offset := by intro _; rfl

  /-- the circuit acts on operations by appending its own operations; which only depend on the input offset -/
  append_only : ∀ offset: ℕ, (circuit offset).fst.snd = operations offset := by intro _; rfl

-- slightly stronger variant: LawfulCircuit with a fixed local length
class ConstantLawfulElaboratedCircuit (circuit : Circuit F α) extends LawfulElaboratedCircuit circuit, ConstantLawfulCircuit circuit where
  final_offset n := n + local_length

-- even stronger (and still the typical case): an indexed family of lawful circuits that all share the same local length
class ConstantLawfulElaboratedCircuits (circuit : α → Circuit F β) extends ConstantLawfulCircuits circuit where
  output : α → ℕ → β
  operations : α → ℕ → Operations F

  output_independent : ∀ (a : α) (offset: ℕ), (circuit a offset).fst.fst = output a offset := by intro _ _; rfl
  offset_independent : ∀ (a : α) (offset: ℕ), (circuit a offset).snd = offset + local_length := by intro _ _; rfl
  append_only : ∀ (a : α) (offset: ℕ), (circuit a offset).fst.snd = operations a offset := by intro _ _; rfl

-- `pure` is a (constant) lawful circuit
instance LawfulElaboratedCircuit.from_pure {a : α} : ConstantLawfulElaboratedCircuit (pure a : Circuit F α) where
  output _ := a
  local_length := 0
  operations _ := []

instance ConstantLawfulElaboratedCircuits.from_pure {f : α → β} : ConstantLawfulElaboratedCircuits (fun a => pure (f a) : α → Circuit F β) where
  output a _ := f a
  local_length := 0
  operations _ _ := []

-- `bind` of two lawful circuits yields a lawful circuit
instance LawfulElaboratedCircuit.from_bind {f: Circuit F α} {g : α → Circuit F β}
    (f_lawful : LawfulElaboratedCircuit f) (g_lawful : ∀ a : α, LawfulElaboratedCircuit (g a)) : LawfulElaboratedCircuit (f >>= g) where
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

  output_independent n := by
    show (g _ _).1.1 = _ -- by definition, `(f >>= g) ops = g (f ops).1 (f ops).2`
    rw [output_independent, output_independent, offset_independent]

  offset_independent n := by
    show (g _ _).2 = _
    rw [offset_independent, output_independent, offset_independent]

  append_only n := by
    show _ ++ (g _ _).1.2 = _
    rw [append_only, append_only, output_independent, offset_independent]

  offset_consistent n := (LawfulCircuit.from_bind inferInstance inferInstance).offset_consistent n

instance LawfulElaboratedCircuit.from_map {f : α → β} {g : Circuit F α}
    (g_lawful : LawfulElaboratedCircuit g) : LawfulElaboratedCircuit (f <$> g) where
  output n := output g n |> f
  final_offset n := final_offset g n
  operations n := g_lawful.operations n

  output_independent n := by
    show f _ = _
    rw [output_independent]

  offset_independent n := by
    show (g _).2 = _
    rw [offset_independent]

  append_only n := by
    show (g _).1.2 = _
    rw [append_only]

  offset_consistent n := (LawfulCircuit.from_map inferInstance).offset_consistent n

-- basic operations are (constant) lawful circuits

instance : ConstantLawfulElaboratedCircuits (F:=F) witness_var where
  output _ n := ⟨ n ⟩
  local_length := 1
  operations c n := [.witness 1 fun env => #v[c env]]

instance {k : ℕ} {c : Environment F → Vector F k} : ConstantLawfulElaboratedCircuit (witness_vars k c) where
  output n := .mapRange k fun i => ⟨n + i⟩
  local_length := k
  operations n := [.witness k c]

instance {α: TypeMap} [ProvableType α] : ConstantLawfulElaboratedCircuits (ProvableType.witness (α:=α) (F:=F)) where
  output _ n := var_from_offset α n
  local_length := size α
  operations c n := [.witness (size α) (to_elements ∘ c)]

instance : ConstantLawfulElaboratedCircuits (F:=F) assert_zero where
  output _ _ := ()
  local_length := 0
  operations e n := [.assert e]

instance : ConstantLawfulElaboratedCircuits (F:=F) lookup where
  output _ _ := ()
  local_length := 0
  operations l n := [.lookup l]

instance {β α: TypeMap} [ProvableType α] [ProvableType β] {circuit : FormalCircuit F β α} {input} :
    ConstantLawfulElaboratedCircuit (subcircuit circuit input) where
  output n := circuit.output input n
  local_length := circuit.local_length input
  final_offset n := n + circuit.local_length input
  operations n := [.subcircuit (circuit.to_subcircuit n input)]

instance {β: TypeMap} [ProvableType β] {circuit : FormalAssertion F β} {input} :
    ConstantLawfulElaboratedCircuit (assertion circuit input) where
  output n := ()
  local_length := circuit.local_length input
  final_offset n := n + circuit.local_length input
  operations n := [.subcircuit (circuit.to_subcircuit n input)]

-- lower `ConstantLawfulCircuits` to `ConstantLawfulCircuit`
instance ConstantLawfulElaboratedCircuits.to_single (circuit : α → Circuit F β) (a : α) [lawful : ConstantLawfulElaboratedCircuits circuit] : ConstantLawfulElaboratedCircuit (circuit a) where
  output n := output circuit a n
  local_length := lawful.local_length
  local_length_eq := (ConstantLawfulCircuits.to_single circuit a).local_length_eq
  operations n := operations circuit a n
  output_independent := output_independent a
  offset_independent := offset_independent a
  append_only := append_only a
  offset_consistent := (ConstantLawfulCircuits.to_single circuit a).offset_consistent

instance LawfulElaboratedCircuit.from_constants {circuit : α → Circuit F β} (lawful : ConstantLawfulElaboratedCircuits circuit) (a : α) :
    LawfulElaboratedCircuit (circuit a) := ConstantLawfulElaboratedCircuits.to_single circuit a |>.toLawfulElaboratedCircuit

syntax "infer_lawful_elaborated_circuit" : tactic

macro_rules
  | `(tactic|infer_lawful_elaborated_circuit) => `(tactic|(
    try intros
    try repeat infer_instance
    repeat (
      try intros
      first
        | apply LawfulElaboratedCircuit.from_bind
        | apply LawfulElaboratedCircuit.from_map
      repeat infer_instance
    )))

-- this tactic is pretty good at inferring lawful circuits!
section
example : LawfulElaboratedCircuit (witness (fun _ => (0 : F)))
  := by infer_lawful_elaborated_circuit

example :
  let add := do
    let x : Expression F ← witness (fun _ => 0)
    let y ← witness (fun _ => 1)
    let z ← witness (fun eval => eval (x + y))
    assert_zero (x + y - z)
    pure z

  LawfulElaboratedCircuit add := by infer_lawful_elaborated_circuit
end

-- `ConstantLawfulCircuit(s)` can be proved from `LawfulCircuit` by adding the requirement that `final_offset` is `n` plus a constant.
-- the latter can usually be proved by rfl!
open LawfulElaboratedCircuit in
def ConstantLawfulElaboratedCircuit.from_constant_length {circuit : Circuit F α} (lawful : LawfulElaboratedCircuit circuit)
  (h_length : ∀ n, circuit.local_length n = circuit.local_length 0) : ConstantLawfulElaboratedCircuit circuit where
  local_length := circuit.local_length 0
  local_length_eq := h_length

open LawfulElaboratedCircuit in
def ConstantLawfulElaboratedCircuits.from_constant_length {circuit : α → Circuit F β} [Inhabited α] (lawful : ∀ a, LawfulElaboratedCircuit (circuit a))
  (h_length : ∀ a n, (circuit a).local_length n = (circuit default).local_length 0) : ConstantLawfulElaboratedCircuits circuit where

  output a n := LawfulElaboratedCircuit.output (circuit a) n
  local_length := (circuit default).local_length 0
  operations a n := LawfulElaboratedCircuit.operations (circuit a) n

  output_independent a n := LawfulElaboratedCircuit.output_independent n
  offset_independent a n := by
    show (circuit a).final_offset n = _
    rw [(lawful a).offset_consistent, h_length]
  append_only a n := by rw [LawfulElaboratedCircuit.append_only]
  offset_consistent a n := by rw [(lawful a).offset_consistent, h_length]
  local_length_eq a n := by rw [h_length]

syntax "infer_constant_lawful_elaborated_circuits" : tactic

macro_rules
  | `(tactic|infer_constant_lawful_elaborated_circuits) => `(tactic|(
    apply ConstantLawfulElaboratedCircuits.from_constant_length (by infer_lawful_elaborated_circuit)
    try intros
    try simp only [LawfulElaboratedCircuit.final_offset]
    try ac_rfl))

section
example : ConstantLawfulElaboratedCircuits (witness (F:=F))
  := by infer_constant_lawful_elaborated_circuits

example :
  let add (x : Expression F) := do
    let y ← witness (fun _ => (1 : F))
    let z ← witness (fun eval => eval (x + y))
    assert_zero (x + y - z)
    pure z

  ConstantLawfulElaboratedCircuits add := by infer_constant_lawful_elaborated_circuits
end

-- characterize various properties of lawful circuits
-- TODO

namespace LawfulCircuit

theorem output_eq (circuit : Circuit F α) [LawfulCircuit circuit] (n : ℕ) :
    circuit.output n = output circuit n := by
  apply output_independent

theorem final_offset_eq (circuit : Circuit F α) [LawfulCircuit circuit] (n : ℕ) :
    circuit.final_offset n = final_offset circuit n := by
  apply offset_independent

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
    offset_independent, ←lawful.local_length_eq]

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
  rw [←LawfulCircuit.output_independent (.from_offset n)]

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
  intros; apply output_independent

theorem final_offset_eq {circuit : α → Circuit F β} [lawful : ConstantLawfulCircuits circuit] :
    ∀ (a : α) (n : ℕ), (circuit a).final_offset n = n + lawful.local_length := by
  intros; apply offset_independent

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
