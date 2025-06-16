/-
This file introduces `ExplicitCircuit`, a variant of `ElaboratedCircuit` that can be auto-derived
using the `infer_explicit_circuit(s)` tactic.

This could be useful to simplify circuit statements with less user intervention.
-/

import Clean.Circuit.Constant
variable {n : ℕ} {F : Type} [Field F] {α β : Type}

class ExplicitCircuit (circuit : Circuit F α) where
  /-- an "explicit" circuit is encapsulated by three functions of the input offset -/
  output : ℕ → α
  local_length : ℕ → ℕ
  operations : ℕ → Operations F

  /-- the functions have to match the circuit -/
  output_eq : ∀ n : ℕ, circuit.output n = output n := by intro _; rfl
  local_length_eq : ∀ n : ℕ, circuit.local_length n = local_length n := by intro _; rfl
  operations_eq : ∀ n : ℕ, circuit.operations n = operations n := by intro _; rfl

  /-- same condition as in `ElaboratedCircuit`: subcircuits must be consistent with the current offset -/
  subcircuits_consistent : ∀ n : ℕ, (circuit.operations n).subcircuits_consistent n := by
    intro _; and_intros <;> try first | ac_rfl | trivial

/-- family of explicit circuits -/
class ExplicitCircuits (circuit : α → Circuit F β) where
  output : α → ℕ → β
  local_length : α → ℕ → ℕ
  operations : α → ℕ → Operations F
  output_eq : ∀ (a : α) (n: ℕ), (circuit a).output n = output a n := by intro _ _; rfl
  local_length_eq : ∀ (a : α) (n: ℕ), (circuit a).local_length n = local_length a n := by intro _ _; rfl
  operations_eq : ∀ (a : α) (n: ℕ), (circuit a).operations n = operations a n := by intro _ _; rfl
  subcircuits_consistent : ∀ (a : α) (n: ℕ), ((circuit a).operations n).subcircuits_consistent n := by
    intro _ _; and_intros <;> try first | ac_rfl | trivial

-- move between family and single explicit circuit

instance ExplicitCircuits.from_single {circuit : α → Circuit F β}
    (explicit : ∀ a, ExplicitCircuit (circuit a)) : ExplicitCircuits circuit where
  output a n := (explicit a).output n
  local_length a n := (explicit a).local_length n
  operations a n := (explicit a).operations n
  output_eq a n := (explicit a).output_eq n
  local_length_eq a n := (explicit a).local_length_eq n
  operations_eq a n := (explicit a).operations_eq n
  subcircuits_consistent a n := (explicit a).subcircuits_consistent n

instance ExplicitCircuits.to_single (circuit : α → Circuit F β) (a : α)
    [explicit : ExplicitCircuits circuit] : ExplicitCircuit (circuit a) where
  output n := output circuit a n
  local_length n := explicit.local_length a n
  operations n := operations circuit a n
  output_eq n := output_eq a n
  local_length_eq n := local_length_eq a n
  operations_eq n := operations_eq a n
  subcircuits_consistent n := subcircuits_consistent a n

-- `pure` is an explicit circuit
instance ExplicitCircuit.from_pure {a : α} : ExplicitCircuit (pure a : Circuit F α) where
  output _ := a
  local_length _ := 0
  operations _ := []

instance ExplicitCircuits.from_pure {f : α → β} : ExplicitCircuits (fun a => pure (f a) : α → Circuit F β) where
  output a _ := f a
  local_length _ _ := 0
  operations _ _ := []

-- `bind` of two explicit circuits yields an explicit circuit
instance ExplicitCircuit.from_bind {f: Circuit F α} {g : α → Circuit F β}
    (f_explicit : ExplicitCircuit f) (g_explicit : ∀ a : α, ExplicitCircuit (g a)) : ExplicitCircuit (f >>= g) where
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
  subcircuits_consistent n := by
    rw [Operations.subcircuits_consistent, Circuit.bind_forAll]
    exact ⟨ f_explicit.subcircuits_consistent .., (g_explicit _).subcircuits_consistent .. ⟩

-- `map` of an explicit circuit yields an explicit circuit
instance ExplicitCircuit.from_map {f : α → β} {g : Circuit F α}
    (g_explicit : ExplicitCircuit g) : ExplicitCircuit (f <$> g) where
  output n := output g n |> f
  local_length n := local_length g n
  operations n := operations g n

  output_eq n := by rw [Circuit.map_output_eq, output_eq]
  local_length_eq n := by rw [Circuit.map_local_length_eq, local_length_eq]
  operations_eq n := by rw [Circuit.map_operations_eq, operations_eq]
  subcircuits_consistent n := by
    rw [Circuit.map_operations_eq]
    exact g_explicit.subcircuits_consistent n

-- basic operations are explicit circuits

instance : ExplicitCircuits (F:=F) witness_var where
  output _ n := ⟨ n ⟩
  local_length _ _ := 1
  operations c n := [.witness 1 fun env => #v[c env]]

instance {k : ℕ} {c : Environment F → Vector F k} : ExplicitCircuit (witness_vars k c) where
  output n := .mapRange k fun i => ⟨n + i⟩
  local_length _ := k
  operations n := [.witness k c]

instance {α: TypeMap} [ProvableType α] : ExplicitCircuits (ProvableType.witness (α:=α) (F:=F)) where
  output _ n := var_from_offset α n
  local_length _ _ := size α
  operations c n := [.witness (size α) (to_elements ∘ c)]

instance : ExplicitCircuits (F:=F) assert_zero where
  output _ _ := ()
  local_length _ _ := 0
  operations e n := [.assert e]

instance : ExplicitCircuits (F:=F) lookup where
  output _ _ := ()
  local_length _ _ := 0
  operations l n := [.lookup l.toLookup]

instance {β α: TypeMap} [ProvableType α] [ProvableType β] {circuit : FormalCircuit F β α} {input} :
    ExplicitCircuit (subcircuit circuit input) where
  output n := circuit.output input n
  local_length _ := circuit.local_length input
  operations n := [.subcircuit (circuit.to_subcircuit n input)]

instance {β: TypeMap} [ProvableType β] {circuit : FormalAssertion F β} {input} :
    ExplicitCircuit (assertion circuit input) where
  output n := ()
  local_length _ := circuit.local_length input
  operations n := [.subcircuit (circuit.to_subcircuit n input)]

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

syntax "infer_explicit_circuits" : tactic

macro_rules
  | `(tactic|infer_explicit_circuits) => `(tactic|(
    apply ExplicitCircuits.from_single (by infer_explicit_circuit)))

-- this tactic is pretty good at inferring explicit circuits!
section

-- single
example : ExplicitCircuit (witness (fun _ => (0 : F))) := by infer_explicit_circuit

example :
  let add := do
    let x : Expression F ← witness (fun _ => 0)
    let y ← witness (fun _ => 1)
    let z ← witness (fun eval => eval (x + y))
    assert_zero (x + y - z)
    pure z

  ExplicitCircuit add := by infer_explicit_circuit

-- family
example : ExplicitCircuits (witness (F:=F)) := by infer_explicit_circuits

example :
  let add (x : Expression F) := do
    let y ← witness (fun _ => (1 : F))
    let z ← witness (fun eval => eval (x + y))
    assert_zero (x + y - z)
    pure z

  ExplicitCircuits add := by infer_explicit_circuits
end

attribute [explicit_circuit_norm] ExplicitCircuit.local_length ExplicitCircuit.operations ExplicitCircuit.output
attribute [explicit_circuit_norm] ExplicitCircuits.local_length ExplicitCircuits.operations ExplicitCircuits.output
attribute [explicit_circuit_norm] ExplicitCircuits.to_single ExplicitCircuits.from_single
attribute [explicit_circuit_norm] ElaboratedCircuit.local_length ElaboratedCircuit.output
