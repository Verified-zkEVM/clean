/-
This file introduces `ExplicitCircuit`, a variant of `ElaboratedCircuit` that can be auto-derived
using the `infer_explicit_circuit` tactic.
This could be useful to simplify circuit statements with less user intervention.
-/
import Clean.Circuit.Constant
variable {n : ℕ} {F : Type} [Field F] {α β : Type}

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

instance ConstantExplicitCircuit.toExplicitCircuit (circuit : Circuit F α) [constant: ConstantExplicitCircuit circuit] : ExplicitCircuit circuit where
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

-- `pure` is a (constant) explicit circuit
instance ConstantExplicitCircuit.from_pure {a : α} : ConstantExplicitCircuit (pure a : Circuit F α) where
  output _ := a
  local_length := 0
  operations _ := []

instance ConstantExplicitCircuits.from_pure {f : α → β} : ConstantExplicitCircuits (fun a => pure (f a) : α → Circuit F β) where
  output a _ := f a
  local_length := 0
  operations _ _ := []

-- `bind` of two explicit circuits yields a explicit circuit
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

-- basic operations are (constant) explicit circuits

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

-- lower `ConstantExplicitCircuits` to `ConstantExplicitCircuit`
instance ConstantExplicitCircuits.to_single (circuit : α → Circuit F β) (a : α) [explicit : ConstantExplicitCircuits circuit] : ConstantExplicitCircuit (circuit a) where
  output n := output circuit a n
  local_length := explicit.local_length
  operations n := operations circuit a n
  output_eq := output_eq a
  local_length_eq := (ConstantCircuits.to_single circuit a).local_length_eq
  operations_eq := operations_eq a

instance ExplicitCircuit.from_constants {circuit : α → Circuit F β} (explicit : ConstantExplicitCircuits circuit) (a : α) :
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

-- this tactic is pretty good at inferring explicit circuits!
section
example : ExplicitCircuit (witness (fun _ => (0 : F))) := by infer_explicit_circuit

example :
  let add := do
    let x : Expression F ← witness (fun _ => 0)
    let y ← witness (fun _ => 1)
    let z ← witness (fun eval => eval (x + y))
    assert_zero (x + y - z)
    pure z

  ExplicitCircuit add := by infer_explicit_circuit
end

-- `ConstantExplicitCircuit(s)` can be proved from `ExplicitCircuit` by adding the requirement that `final_offset` is `n` plus a constant.
-- the latter can usually be proved by rfl!
def ConstantExplicitCircuit.from_constant_length {circuit : Circuit F α} (explicit : ExplicitCircuit circuit)
  (h_length : ∀ n, circuit.local_length n = circuit.local_length 0) : ConstantExplicitCircuit circuit where
  output n := explicit.output n
  local_length := circuit.local_length 0
  operations n := explicit.operations n
  output_eq n := explicit.output_eq n
  local_length_eq := h_length
  operations_eq n := explicit.operations_eq n

def ConstantExplicitCircuits.from_constant_length {circuit : α → Circuit F β} [Inhabited α] (explicit : ∀ a, ExplicitCircuit (circuit a))
  (h_length : ∀ a n, (explicit a).local_length n = (explicit default).local_length 0) : ConstantExplicitCircuits circuit where
  output a n := ExplicitCircuit.output (circuit a) n
  local_length := ExplicitCircuit.local_length (circuit default) 0
  operations a n := ExplicitCircuit.operations (circuit a) n

  output_eq a n := ExplicitCircuit.output_eq n
  local_length_eq a n := by rw [ExplicitCircuit.local_length_eq, h_length]
  operations_eq a n := ExplicitCircuit.operations_eq n

syntax "infer_constant_explicit_circuits" : tactic

macro_rules
  | `(tactic|infer_constant_explicit_circuits) => `(tactic|(
    apply ConstantExplicitCircuits.from_constant_length (by infer_explicit_circuit)
    try intros
    try simp only [ExplicitCircuit.local_length]
    try ac_rfl))

section
example : ConstantExplicitCircuits (witness (F:=F)) := by infer_constant_explicit_circuits

example :
  let add (x : Expression F) := do
    let y ← witness (fun _ => (1 : F))
    let z ← witness (fun eval => eval (x + y))
    assert_zero (x + y - z)
    pure z

  ConstantExplicitCircuits add := by infer_constant_explicit_circuits
end

attribute [explicit_circuit_norm] ExplicitCircuit.local_length ExplicitCircuit.operations ExplicitCircuit.output
attribute [explicit_circuit_norm] ConstantCircuit.local_length ConstantExplicitCircuit.output ConstantExplicitCircuit.operations
attribute [explicit_circuit_norm] ConstantCircuits.local_length ConstantExplicitCircuits.output ConstantExplicitCircuits.operations
  ConstantExplicitCircuits.from_constant_length id_eq
attribute [explicit_circuit_norm] ElaboratedCircuit.local_length ElaboratedCircuit.output
